import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog, StringVar, IntVar, BooleanVar
import threading
import queue
import time
import os
import json
import sqlite3
import tempfile
from urllib.robotparser import RobotFileParser
from urllib.parse import urljoin, urlparse
import requests
from bs4 import BeautifulSoup
from collections import deque, defaultdict
import re
import html
from datetime import datetime

# Default user agent - can be customized through the UI
DEFAULT_USER_AGENT = "LocalSearchEngine/1.0"

# If a site's robots.txt Crawl-delay for our user agent (or *) exceeds this many
# seconds, we refuse to crawl it automatically and move it to the "Blocked Sites" tab.
MAX_ALLOWED_CRAWL_DELAY = 120


class WebPage:
    """Class to store page information"""
    def __init__(self, url, title="", description="", content="", links=None, timestamp=None):
        self.url = url
        self.title = title or url
        self.description = description or ""
        self.content = content or ""
        self.links = links or []
        self.timestamp = timestamp or datetime.now()

    def to_dict(self):
        return {
            'url': self.url,
            'title': self.title,
            'description': self.description,
            'content': self.content[:500],  # Store first 500 chars for search
            'timestamp': self.timestamp
        }

    def to_full_dict(self):
        """Full representation (used for export - no truncation)"""
        ts = self.timestamp
        if isinstance(ts, datetime):
            ts = ts.isoformat()
        return {
            'url': self.url,
            'title': self.title,
            'description': self.description,
            'content': self.content,
            'links': self.links,
            'timestamp': ts
        }


class PageStore:
    """
    SQLite-backed store for crawled/indexed pages.
    Keeps page data (title, description, content, links) out of process memory
    and persisted to a database file on disk instead of a big in-memory dict.
    """

    def __init__(self, db_path):
        self.db_path = db_path
        # allow use from the crawl worker thread as well as the main thread
        self.conn = sqlite3.connect(db_path, check_same_thread=False)
        self.lock = threading.Lock()
        self._create_table()

    def _create_table(self):
        with self.lock:
            self.conn.execute('''
                CREATE TABLE IF NOT EXISTS pages (
                    url TEXT PRIMARY KEY,
                    title TEXT,
                    description TEXT,
                    content TEXT,
                    links TEXT,
                    timestamp TEXT,
                    domain TEXT,
                    security_status INTEGER
                )
            ''')
            self.conn.commit()

    def insert_page(self, page, domain="", security_status=None):
        """security_status: True (https), False (http-only), or None (unknown)"""
        if security_status is True:
            sec_val = 1
        elif security_status is False:
            sec_val = 0
        else:
            sec_val = None

        ts = page.timestamp
        if isinstance(ts, datetime):
            ts = ts.isoformat()

        with self.lock:
            self.conn.execute('''
                INSERT OR REPLACE INTO pages
                    (url, title, description, content, links, timestamp, domain, security_status)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            ''', (
                page.url, page.title, page.description, page.content,
                json.dumps(page.links), ts, domain, sec_val
            ))
            self.conn.commit()

    def _row_to_page(self, row):
        url, title, description, content, links_json, timestamp = row
        try:
            links = json.loads(links_json) if links_json else []
        except (TypeError, ValueError):
            links = []
        try:
            ts = datetime.fromisoformat(timestamp) if timestamp else datetime.now()
        except (TypeError, ValueError):
            ts = datetime.now()
        return WebPage(url, title, description, content, links, ts)

    def get_page(self, url):
        with self.lock:
            cur = self.conn.execute(
                'SELECT url, title, description, content, links, timestamp FROM pages WHERE url = ?',
                (url,)
            )
            row = cur.fetchone()
        return self._row_to_page(row) if row else None

    def has_page(self, url):
        with self.lock:
            cur = self.conn.execute('SELECT 1 FROM pages WHERE url = ?', (url,))
            return cur.fetchone() is not None

    def count(self):
        with self.lock:
            cur = self.conn.execute('SELECT COUNT(*) FROM pages')
            return cur.fetchone()[0]

    def all_pages(self):
        with self.lock:
            cur = self.conn.execute(
                'SELECT url, title, description, content, links, timestamp FROM pages ORDER BY rowid'
            )
            rows = cur.fetchall()
        return [self._row_to_page(r) for r in rows]

    def get_security_status(self, domain):
        with self.lock:
            cur = self.conn.execute(
                'SELECT security_status FROM pages WHERE domain = ? AND security_status IS NOT NULL LIMIT 1',
                (domain,)
            )
            row = cur.fetchone()
        if row is None or row[0] is None:
            return None
        return bool(row[0])

    def search(self, query):
        """Simple relevance-scored search over title/description/content/url."""
        query = query.lower()
        with self.lock:
            cur = self.conn.execute(
                'SELECT url, title, description, content, links, timestamp FROM pages'
            )
            rows = cur.fetchall()

        results = []
        for row in rows:
            page = self._row_to_page(row)
            score = 0
            if query in page.title.lower():
                score += 3
            if query in page.description.lower():
                score += 2
            if query in page.content.lower():
                score += 1
            if query in page.url.lower():
                score += 1
            if score > 0:
                results.append((score, page))

        results.sort(key=lambda x: x[0], reverse=True)
        return [p for _, p in results]

    def clear(self):
        with self.lock:
            self.conn.execute('DELETE FROM pages')
            self.conn.commit()

    def close(self):
        try:
            self.conn.close()
        except Exception:
            pass

    # ---- Export / Import ----

    def export_to_sqlite(self, dest_path):
        """Copy the live database out to a standalone .db file the user keeps."""
        with self.lock:
            dest_conn = sqlite3.connect(dest_path)
            self.conn.backup(dest_conn)
            dest_conn.close()

    def export_to_json(self, dest_path):
        pages = self.all_pages()
        data = [p.to_full_dict() for p in pages]
        with open(dest_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

    def import_from_sqlite(self, src_path, merge=True):
        src_conn = sqlite3.connect(src_path)
        try:
            cur = src_conn.execute(
                'SELECT url, title, description, content, links, timestamp, domain, security_status FROM pages'
            )
            rows = cur.fetchall()
        finally:
            src_conn.close()

        with self.lock:
            if not merge:
                self.conn.execute('DELETE FROM pages')
            self.conn.executemany('''
                INSERT OR REPLACE INTO pages
                    (url, title, description, content, links, timestamp, domain, security_status)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            ''', rows)
            self.conn.commit()
        return len(rows)

    def import_from_json(self, src_path, merge=True):
        with open(src_path, 'r', encoding='utf-8') as f:
            data = json.load(f)

        if not merge:
            self.clear()

        count = 0
        for d in data:
            ts = None
            if d.get('timestamp'):
                try:
                    ts = datetime.fromisoformat(d['timestamp'])
                except (TypeError, ValueError):
                    ts = None
            page = WebPage(
                d.get('url', ''),
                d.get('title', ''),
                d.get('description', ''),
                d.get('content', ''),
                d.get('links', []),
                ts
            )
            self.insert_page(page, d.get('domain', ''), d.get('security_status'))
            count += 1
        return count


class WebCrawlerBrowser:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title("Crawler Browser")
        self.root.geometry("1400x900")

        # Queue for thread-safe communication
        self.crawl_queue = queue.Queue()

        # Crawling state
        self.is_crawling = False
        self.crawl_thread = None

        # Data storage (small, bounded bookkeeping stays in memory)
        self.visited_urls = set()
        self.urls_to_visit = deque()
        self.robot_parsers = {}
        self.crawl_delays = {}  # Store crawl delays per domain
        self.last_crawl_time = {}  # Track last crawl time per domain
        self.search_results = []

        # Domain security status tracking
        self.domain_security_status = {}  # domain -> bool (True if HTTPS-only, False if HTTP-only/unsecured)

        # Per-domain page counting
        self.pages_per_domain = defaultdict(int)  # Track pages crawled per domain
        self.domain_page_limits = {}  # Store per-domain limits (if using per-domain mode)

        # Store robots.txt files that match criteria
        self.interesting_robot_files = []  # List of dicts with url, content, matched_criteria

        # Domains blocked because their robots.txt Crawl-delay exceeds the configured maximum
        self.blocked_domains = {}  # domain -> dict with robots_url, crawl_delay, sample_url, timestamp

        # Current page data
        self.current_url = ""
        self.current_content = ""

        # User agent - will be set from UI or default
        self.user_agent = DEFAULT_USER_AGENT

        # Set up a temporary SQLite database to hold crawled/indexed page data.
        # This keeps large crawl results off the Python heap and on disk instead;
        # the file is deleted automatically when the app closes.
        fd, self.db_path = tempfile.mkstemp(prefix="crawler_index_", suffix=".db")
        os.close(fd)
        self.page_store = PageStore(self.db_path)

        self.setup_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

        # Start the persistent queue-polling loop (handles crawl updates, manual fetch
        # responses, etc.) - runs continuously regardless of crawl state
        self.root.after(100, self.update_gui)

    def setup_ui(self):
        # Create main frame
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Top toolbar
        toolbar = ttk.Frame(main_frame)
        toolbar.pack(fill=tk.X, pady=(0, 5))

        # Search section
        ttk.Label(toolbar, text="Search:").pack(side=tk.LEFT, padx=(0, 5))
        self.search_var = StringVar()
        self.search_entry = ttk.Entry(toolbar, textvariable=self.search_var, width=40)
        self.search_entry.pack(side=tk.LEFT, padx=(0, 5))

        self.search_button = ttk.Button(toolbar, text="Search", command=self.perform_search)
        self.search_button.pack(side=tk.LEFT, padx=(0, 20))

        # URL section
        ttk.Label(toolbar, text="URL:").pack(side=tk.LEFT, padx=(0, 5))
        self.url_entry = ttk.Entry(toolbar, width=50)
        self.url_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 5))

        self.crawl_button = ttk.Button(toolbar, text="Start Crawl", command=self.toggle_crawl)
        self.crawl_button.pack(side=tk.LEFT, padx=(0, 5))

        self.visit_button = ttk.Button(toolbar, text="Visit", command=self.visit_url)
        self.visit_button.pack(side=tk.LEFT, padx=(0, 20))

        # Import / Export
        self.export_button = ttk.Button(toolbar, text="Export Index", command=self.export_index)
        self.export_button.pack(side=tk.LEFT, padx=(0, 5))

        self.import_button = ttk.Button(toolbar, text="Import Index", command=self.import_index)
        self.import_button.pack(side=tk.LEFT)

        # Progress frame
        progress_frame = ttk.Frame(main_frame)
        progress_frame.pack(fill=tk.X, pady=(0, 5))

        self.progress_label = ttk.Label(progress_frame, text="Ready")
        self.progress_label.pack(side=tk.LEFT)

        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(progress_frame, variable=self.progress_var, maximum=100)
        self.progress_bar.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(10, 0))

        # Stats label
        self.stats_label = ttk.Label(progress_frame, text="Pages: 0")
        self.stats_label.pack(side=tk.RIGHT, padx=(10, 0))

        # Create notebook for tabs
        self.notebook = ttk.Notebook(main_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)

        # Create tabs
        self.browse_tab = ttk.Frame(self.notebook)
        self.search_tab = ttk.Frame(self.notebook)  # New search results tab
        self.crawl_tab = ttk.Frame(self.notebook)
        self.robots_tab = ttk.Frame(self.notebook)  # New robots.txt tab
        self.blocked_tab = ttk.Frame(self.notebook)  # Sites blocked for excessive crawl-delay

        self.notebook.add(self.browse_tab, text="Browser")
        self.notebook.add(self.search_tab, text="Search Results")
        self.notebook.add(self.crawl_tab, text="Crawling")
        self.notebook.add(self.robots_tab, text="Interesting robots.txt")
        self.notebook.add(self.blocked_tab, text="Blocked Sites")

        # Setup tabs
        self.setup_browse_tab()
        self.setup_search_tab()
        self.setup_crawl_tab()
        self.setup_robots_tab()
        self.setup_blocked_tab()

        # Status bar
        self.status_bar = ttk.Label(main_frame, text="Ready", relief=tk.SUNKEN)
        self.status_bar.pack(fill=tk.X, pady=(5, 0))

        # Bind enter key for URL and search
        self.url_entry.bind('<Return>', lambda e: self.visit_url())
        self.search_entry.bind('<Return>', lambda e: self.perform_search())

    def setup_browse_tab(self):
        # Text widget for displaying web content
        self.content_text = scrolledtext.ScrolledText(self.browse_tab, wrap=tk.WORD)
        self.content_text.pack(fill=tk.BOTH, expand=True)
        self.content_text.config(state=tk.DISABLED)

        # Configure tags for formatting
        self.content_text.tag_config("title", font=("Arial", 14, "bold"))
        self.content_text.tag_config("heading", font=("Arial", 12, "bold"))
        self.content_text.tag_config("link", foreground="blue", underline=True)
        self.content_text.tag_config("plain", font=("Arial", 10))
        self.content_text.tag_config("description", font=("Arial", 10, "italic"), foreground="gray")

    def setup_search_tab(self):
        # Search results frame
        search_frame = ttk.Frame(self.search_tab)
        search_frame.pack(fill=tk.BOTH, expand=True)

        # Left panel - search results list
        left_panel = ttk.Frame(search_frame)
        left_panel.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))

        # Search stats
        self.search_stats_label = ttk.Label(left_panel, text="No search performed")
        self.search_stats_label.pack(fill=tk.X, pady=(0, 5))

        # Treeview for search results
        columns = ('Title', 'URL', 'Description')
        self.search_tree = ttk.Treeview(left_panel, columns=columns, show='headings')

        # Define headings
        self.search_tree.heading('Title', text='Title')
        self.search_tree.heading('URL', text='URL')
        self.search_tree.heading('Description', text='Description')

        # Define columns
        self.search_tree.column('Title', width=200)
        self.search_tree.column('URL', width=300)
        self.search_tree.column('Description', width=400)

        # Add scrollbar
        tree_scroll = ttk.Scrollbar(left_panel, orient=tk.VERTICAL, command=self.search_tree.yview)
        self.search_tree.configure(yscrollcommand=tree_scroll.set)

        self.search_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        # Bind double-click to visit result
        self.search_tree.bind('<Double-Button-1>', self.on_search_result_double_click)

        # Right panel - result preview
        right_panel = ttk.Frame(search_frame)
        right_panel.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        ttk.Label(right_panel, text="Preview:", font=("Arial", 10, "bold")).pack(anchor=tk.W)
        self.search_preview = scrolledtext.ScrolledText(right_panel, wrap=tk.WORD, height=30)
        self.search_preview.pack(fill=tk.BOTH, expand=True)
        self.search_preview.config(state=tk.DISABLED)

    def setup_crawl_tab(self):
        # Frame for crawl controls
        crawl_controls = ttk.Frame(self.crawl_tab)
        crawl_controls.pack(fill=tk.X, pady=(0, 5))

        # Row 1: User Agent and Default Delay
        row1 = ttk.Frame(crawl_controls)
        row1.pack(fill=tk.X, pady=(0, 5))

        ttk.Label(row1, text="User Agent:").pack(side=tk.LEFT, padx=(0, 5))
        self.user_agent_var = tk.StringVar(value=DEFAULT_USER_AGENT)
        self.user_agent_entry = ttk.Entry(row1, textvariable=self.user_agent_var, width=30)
        self.user_agent_entry.pack(side=tk.LEFT, padx=(0, 20))

        ttk.Label(row1, text="Default Delay (s):").pack(side=tk.LEFT, padx=(0, 5))
        self.default_delay_var = tk.StringVar(value="1")
        self.default_delay_entry = ttk.Entry(row1, textvariable=self.default_delay_var, width=5)
        self.default_delay_entry.pack(side=tk.LEFT, padx=(0, 20))

        ttk.Label(row1, text="Max Crawl-Delay (s):").pack(side=tk.LEFT, padx=(0, 5))
        self.max_crawl_delay_var = tk.StringVar(value="120")
        self.max_crawl_delay_entry = ttk.Entry(row1, textvariable=self.max_crawl_delay_var, width=6)
        self.max_crawl_delay_entry.pack(side=tk.LEFT)
        # Small hint so it's clear what this does and how to disable it
        self._max_crawl_delay_hint = ttk.Label(row1, text="(0 = no limit)")
        self._max_crawl_delay_hint.pack(side=tk.LEFT, padx=(2, 20))

        ttk.Label(row1, text="Start URL:").pack(side=tk.LEFT, padx=(0, 5))
        self.start_url_var = tk.StringVar(value="https://example.com/")
        self.start_url_entry = ttk.Entry(row1, textvariable=self.start_url_var, width=60)
        self.start_url_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)

        # Combined Row: Page Limit Mode + Limit Values
        row_limit = ttk.Frame(crawl_controls)
        row_limit.pack(fill=tk.X, pady=(0, 5))

        # Radio buttons
        ttk.Label(row_limit, text="Page Limit Mode:").pack(side=tk.LEFT, padx=(0, 10))

        self.limit_mode_var = tk.StringVar(value="global")

        self.global_radio = ttk.Radiobutton(
            row_limit, text="Global Limit", variable=self.limit_mode_var,
            value="global", command=self.on_limit_mode_change
        )
        self.global_radio.pack(side=tk.LEFT, padx=(0, 10))

        self.per_domain_radio = ttk.Radiobutton(
            row_limit, text="Per-Domain Limit", variable=self.limit_mode_var,
            value="per_domain", command=self.on_limit_mode_change
        )
        self.per_domain_radio.pack(side=tk.LEFT, padx=(0, 10))

        self.unlimited_radio = ttk.Radiobutton(
            row_limit, text="Unlimited", variable=self.limit_mode_var,
            value="unlimited", command=self.on_limit_mode_change
        )
        self.unlimited_radio.pack(side=tk.LEFT, padx=(0, 20))

        # Limit value frames
        self.global_frame = ttk.Frame(row_limit)
        self.global_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Label(self.global_frame, text="Global Max Pages:").pack(side=tk.LEFT, padx=(0, 5))
        self.max_pages_var = tk.StringVar(value="100000")
        self.max_pages_entry = ttk.Entry(self.global_frame, textvariable=self.max_pages_var, width=10)
        self.max_pages_entry.pack(side=tk.LEFT)
        ttk.Label(self.global_frame, text="(Total pages to crawl)").pack(side=tk.LEFT, padx=(5, 0))

        self.per_domain_frame = ttk.Frame(row_limit)
        ttk.Label(self.per_domain_frame, text="Max Pages per Domain:").pack(side=tk.LEFT, padx=(0, 5))
        self.per_domain_limit_var = tk.StringVar(value="100")
        self.per_domain_limit_entry = ttk.Entry(self.per_domain_frame, textvariable=self.per_domain_limit_var, width=8)
        self.per_domain_limit_entry.pack(side=tk.LEFT)
        ttk.Label(self.per_domain_frame, text="(Pages per domain)").pack(side=tk.LEFT, padx=(5, 0))

        self.unlimited_frame = ttk.Frame(row_limit)
        ttk.Label(self.unlimited_frame, text="Unlimited crawling - will crawl all pages found").pack(side=tk.LEFT)

        # Show the correct frame for the selected mode
        self.update_limit_mode_ui()

        # Results display
        results_frame = ttk.Frame(self.crawl_tab)
        results_frame.pack(fill=tk.BOTH, expand=True)

        # Treeview for crawled URLs with more info
        columns = ('Title', 'URL', 'Security', 'Description', 'Crawl Delay')
        self.results_tree = ttk.Treeview(results_frame, columns=columns, show='headings')

        # Define headings
        self.results_tree.heading('Title', text='Title')
        self.results_tree.heading('URL', text='URL')
        self.results_tree.heading('Security', text='Security')
        self.results_tree.heading('Description', text='Description')
        self.results_tree.heading('Crawl Delay', text='Crawl Delay')

        # Define columns
        self.results_tree.column('Title', width=150)
        self.results_tree.column('URL', width=250)
        self.results_tree.column('Security', width=80)
        self.results_tree.column('Description', width=300)
        self.results_tree.column('Crawl Delay', width=80)

        # Add scrollbar
        tree_scroll = ttk.Scrollbar(results_frame, orient=tk.VERTICAL, command=self.results_tree.yview)
        self.results_tree.configure(yscrollcommand=tree_scroll.set)

        self.results_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        # Bind double-click to visit result
        self.results_tree.bind('<Double-Button-1>', self.on_crawl_result_double_click)

    def setup_robots_tab(self):
        """Setup the robots.txt documentation tab"""
        # Main frame for robots.txt tab
        robots_frame = ttk.Frame(self.robots_tab)
        robots_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Info label
        info_label = ttk.Label(robots_frame,
                               text="Robots.txt files found that contain long repeating strings or complete sentences:",
                               font=("Arial", 10, "bold"))
        info_label.pack(anchor=tk.W, pady=(0, 5))

        # Create PanedWindow for split view
        paned_window = ttk.PanedWindow(robots_frame, orient=tk.HORIZONTAL)
        paned_window.pack(fill=tk.BOTH, expand=True)

        # Left panel - Treeview for robots.txt list
        left_frame = ttk.Frame(paned_window)
        paned_window.add(left_frame, weight=1)

        # Treeview for robots.txt files
        columns = ('URL', 'Criteria', 'Length')
        self.robots_tree = ttk.Treeview(left_frame, columns=columns, show='headings', height=20)

        # Define headings
        self.robots_tree.heading('URL', text='Robots.txt URL')
        self.robots_tree.heading('Criteria', text='Matched Criteria')
        self.robots_tree.heading('Length', text='Length (chars)')

        # Define columns
        self.robots_tree.column('URL', width=300)
        self.robots_tree.column('Criteria', width=150)
        self.robots_tree.column('Length', width=80)

        # Add scrollbar for treeview
        tree_scroll = ttk.Scrollbar(left_frame, orient=tk.VERTICAL, command=self.robots_tree.yview)
        self.robots_tree.configure(yscrollcommand=tree_scroll.set)

        self.robots_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        # Bind selection event
        self.robots_tree.bind('<<TreeviewSelect>>', self.on_robots_select)

        # Right panel - Text widget for displaying content
        right_frame = ttk.Frame(paned_window)
        paned_window.add(right_frame, weight=2)

        ttk.Label(right_frame, text="Robots.txt Content:", font=("Arial", 10, "bold")).pack(anchor=tk.W)

        # Text widget with scrollbar
        text_frame = ttk.Frame(right_frame)
        text_frame.pack(fill=tk.BOTH, expand=True)

        self.robots_content = scrolledtext.ScrolledText(text_frame, wrap=tk.WORD, font=("Courier", 10))
        self.robots_content.pack(fill=tk.BOTH, expand=True)

        # Configure tags for highlighting
        self.robots_content.tag_config("long_string", background="yellow", foreground="red")
        self.robots_content.tag_config("sentence", background="lightgreen")

        # Stats label
        self.robots_stats_label = ttk.Label(robots_frame, text="No interesting robots.txt files found yet", relief=tk.SUNKEN)
        self.robots_stats_label.pack(fill=tk.X, pady=(5, 0))

    def setup_blocked_tab(self):
        """Setup the tab listing sites blocked for excessive Crawl-delay, plus a manual fetch tool"""
        frame = ttk.Frame(self.blocked_tab)
        frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.blocked_info_label = ttk.Label(
            frame,
            text=self._blocked_info_text(),
            font=("Arial", 10, "bold"), wraplength=1300, justify=tk.LEFT
        )
        self.blocked_info_label.pack(anchor=tk.W, pady=(0, 5))

        # Keep the label in sync whenever the user changes the threshold
        self.max_crawl_delay_var.trace_add("write", lambda *a: self.blocked_info_label.config(text=self._blocked_info_text()))

        # Treeview of blocked domains
        columns = ('Domain', 'Crawl Delay', 'Sample URL', 'Robots.txt')
        self.blocked_tree = ttk.Treeview(frame, columns=columns, show='headings', height=8)
        self.blocked_tree.heading('Domain', text='Domain')
        self.blocked_tree.heading('Crawl Delay', text='Crawl Delay')
        self.blocked_tree.heading('Sample URL', text='Sample URL')
        self.blocked_tree.heading('Robots.txt', text='Robots.txt URL')
        self.blocked_tree.column('Domain', width=180)
        self.blocked_tree.column('Crawl Delay', width=90)
        self.blocked_tree.column('Sample URL', width=350)
        self.blocked_tree.column('Robots.txt', width=350)

        tree_scroll = ttk.Scrollbar(frame, orient=tk.VERTICAL, command=self.blocked_tree.yview)
        self.blocked_tree.configure(yscrollcommand=tree_scroll.set)
        self.blocked_tree.pack(fill=tk.BOTH, expand=False, pady=(0, 10))

        self.blocked_tree.bind('<<TreeviewSelect>>', self.on_blocked_select)

        # Manual fetch panel
        manual_frame = ttk.LabelFrame(frame, text="Manual Fetch (custom headers)")
        manual_frame.pack(fill=tk.BOTH, expand=True)

        url_row = ttk.Frame(manual_frame)
        url_row.pack(fill=tk.X, padx=5, pady=5)
        ttk.Label(url_row, text="URL:").pack(side=tk.LEFT, padx=(0, 5))
        self.manual_url_var = tk.StringVar()
        self.manual_url_entry = ttk.Entry(url_row, textvariable=self.manual_url_var)
        self.manual_url_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)

        ttk.Label(manual_frame, text="Custom Headers (one per line, e.g. Header-Name: value):").pack(
            anchor=tk.W, padx=5)
        self.manual_headers_text = tk.Text(manual_frame, height=4)
        self.manual_headers_text.pack(fill=tk.X, padx=5, pady=(0, 5))
        self.manual_headers_text.insert(1.0, f"User-Agent: {self.user_agent}\nX-Comment: 'Your Crawl-delay is unacceptable!'")

        button_row = ttk.Frame(manual_frame)
        button_row.pack(fill=tk.X, padx=5, pady=(0, 5))
        self.send_manual_button = ttk.Button(button_row, text="Send Request", command=self.send_manual_request)
        self.send_manual_button.pack(side=tk.LEFT, padx=(0, 5))
        self.index_manual_button = ttk.Button(button_row, text="Index Result", command=self.index_manual_response)
        self.index_manual_button.pack(side=tk.LEFT)

        ttk.Label(manual_frame, text="Response:").pack(anchor=tk.W, padx=5)
        self.manual_response_text = scrolledtext.ScrolledText(manual_frame, wrap=tk.WORD, height=12)
        self.manual_response_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=(0, 5))
        self.manual_response_text.config(state=tk.DISABLED)

        # Holds the most recent manual response so "Index Result" can store it
        self._last_manual_response = None
        self._last_manual_url = None

    def on_blocked_select(self, event):
        """When a blocked domain is selected, pre-fill the manual fetch URL with its sample page"""
        selection = self.blocked_tree.selection()
        if selection:
            item = self.blocked_tree.item(selection[0])
            sample_url = item['values'][2]
            self.manual_url_var.set(sample_url)

    def send_manual_request(self):
        """Send a one-off GET request with user-supplied custom headers"""
        url = self.manual_url_var.get().strip()
        if not url:
            messagebox.showwarning("Warning", "Please enter a URL to fetch")
            return
        if not url.startswith(('http://', 'https://')):
            url = 'https://' + url
            self.manual_url_var.set(url)

        headers_text = self.manual_headers_text.get(1.0, tk.END).strip()
        headers = {}
        for line in headers_text.split('\n'):
            line = line.strip()
            if not line or ':' not in line:
                continue
            key, value = line.split(':', 1)
            key = key.strip()
            value = value.strip()
            if key:
                headers[key] = value
        if 'User-Agent' not in headers:
            headers['User-Agent'] = self.user_agent

        self.send_manual_button.config(state=tk.DISABLED)
        self.status_bar.config(text=f"Sending manual request to {url}...")

        thread = threading.Thread(target=self._do_manual_request, args=(url, headers))
        thread.daemon = True
        thread.start()

    def _do_manual_request(self, url, headers):
        """Runs in a background thread so the UI doesn't freeze"""
        try:
            response = requests.get(url, headers=headers, timeout=15)
            self.crawl_queue.put(("manual_response", (url, response)))
        except Exception as e:
            self.crawl_queue.put(("manual_response_error", (url, str(e))))

    def display_manual_response(self, url, response):
        """Show the result of a manual fetch in the response panel"""
        self._last_manual_response = response
        self._last_manual_url = url

        self.manual_response_text.config(state=tk.NORMAL)
        self.manual_response_text.delete(1.0, tk.END)
        self.manual_response_text.insert(tk.END, f"URL: {url}\nStatus: {response.status_code}\n\n")
        self.manual_response_text.insert(tk.END, "Response Headers:\n")
        for k, v in response.headers.items():
            self.manual_response_text.insert(tk.END, f"  {k}: {v}\n")
        self.manual_response_text.insert(tk.END, "\nBody Preview (first 3000 chars):\n")
        body_preview = response.text[:3000] if response.text else "(empty body)"
        self.manual_response_text.insert(tk.END, body_preview)
        self.manual_response_text.config(state=tk.DISABLED)

        self.send_manual_button.config(state=tk.NORMAL)
        self.status_bar.config(text=f"Received {response.status_code} from {url}")

    def index_manual_response(self):
        """Parse the last manual response as a page and add it to the search index"""
        if self._last_manual_response is None:
            messagebox.showinfo("Index Result", "No response to index yet. Send a request first.")
            return

        content_type = self._last_manual_response.headers.get('content-type', '')
        if 'text/html' not in content_type:
            messagebox.showwarning("Index Result", "The response doesn't look like HTML; nothing to index.")
            return

        url = self._last_manual_url
        page_info = self.parse_page(url, self._last_manual_response.text)
        domain = self.get_domain(url)
        self.page_store.insert_page(page_info, domain, self.domain_security_status.get(domain))
        self.refresh_results_tree()
        messagebox.showinfo("Index Result", f"Indexed:\n{url}")

    def _blocked_info_text(self):
        """Build the info label text for the Blocked Sites tab based on the current threshold"""
        max_delay = self.get_max_crawl_delay()
        if max_delay is None:
            return ("Crawl-delay blocking is disabled (max set to 0) - no sites will be auto-blocked. "
                    "You can still send a one-off manual request with custom headers below.")
        return (f"Sites whose robots.txt Crawl-delay exceeds {max_delay:g} seconds are "
                "blocked from automatic crawling and listed here. You can still send a one-off "
                "manual request with custom headers below.")

    def get_max_crawl_delay(self):
        """
        Read the user-customizable max crawl-delay threshold from the UI.
        Returns None if the limit is disabled (value <= 0 or blank/invalid),
        meaning no domain should ever be auto-blocked for a high Crawl-delay.
        """
        try:
            raw = self.max_crawl_delay_var.get().strip()
        except AttributeError:
            return MAX_ALLOWED_CRAWL_DELAY  # UI not built yet, fall back to default
        if not raw:
            return MAX_ALLOWED_CRAWL_DELAY
        try:
            value = float(raw)
        except ValueError:
            return MAX_ALLOWED_CRAWL_DELAY
        if value <= 0:
            return None  # 0 or negative disables the block entirely
        return value

    def block_domain(self, domain, robots_url, crawl_delay, sample_url):
        """Mark a domain as blocked for automatic crawling due to an excessive Crawl-delay"""
        if domain in self.blocked_domains:
            return
        max_delay = self.get_max_crawl_delay()
        entry = {
            'domain': domain,
            'robots_url': robots_url,
            'crawl_delay': crawl_delay,
            'sample_url': sample_url,
            'timestamp': datetime.now()
        }
        self.blocked_domains[domain] = entry
        self.crawl_queue.put(("blocked", entry))
        self.crawl_queue.put((
            "status",
            f"BLOCKED {domain}: Crawl-delay {crawl_delay}s exceeds {max_delay}s limit "
            "- see 'Blocked Sites' tab"
        ))

    def on_limit_mode_change(self):
        """Handle limit mode radio button changes"""
        self.update_limit_mode_ui()

    def update_limit_mode_ui(self):
        """Update UI based on selected limit mode"""
        mode = self.limit_mode_var.get()

        # Hide all frames
        self.global_frame.pack_forget()
        self.per_domain_frame.pack_forget()
        self.unlimited_frame.pack_forget()

        # Show the appropriate frame
        if mode == "global":
            self.global_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        elif mode == "per_domain":
            self.per_domain_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        else:  # unlimited
            self.unlimited_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)

    def check_domain_security(self, url):
        """Check if a domain supports HTTPS (returns True if secure, False if HTTP-only/unsecured)"""
        domain = self.get_domain(url)

        # If we've already checked this domain, return cached result
        if domain in self.domain_security_status:
            return self.domain_security_status[domain]

        # Check if the URL is already HTTPS
        parsed = urlparse(url)
        if parsed.scheme == 'https':
            # Domain uses HTTPS, consider it secure
            self.domain_security_status[domain] = True
            return True

        # For HTTP URLs, try to check if HTTPS is available
        # Try to connect to HTTPS version of the domain
        https_url = f"https://{domain}/"
        try:
            # Send a HEAD request to check if HTTPS is accessible
            headers = {'User-Agent': self.user_agent}
            response = requests.head(https_url, timeout=5, allow_redirects=True)

            # If we get a successful response, HTTPS is available
            if response.status_code < 400:
                self.domain_security_status[domain] = True
                self.crawl_queue.put(("status", f"Domain {domain} supports HTTPS"))
                return True
            else:
                # HTTPS returned an error, domain might be HTTP-only
                self.domain_security_status[domain] = False
                self.crawl_queue.put(("status", f"WARNING: Domain {domain} appears to be HTTP-only/unsecured"))
                return False

        except requests.exceptions.RequestException:
            # Connection failed, likely no HTTPS support
            self.domain_security_status[domain] = False
            self.crawl_queue.put(("status", f"WARNING: Domain {domain} appears to be HTTP-only/unsecured"))
            return False

    def check_domain_limit(self, domain):
        """Check if domain has reached its page limit"""
        mode = self.limit_mode_var.get()

        if mode == "global":
            # Global limit is handled separately in crawl_worker
            return True
        elif mode == "per_domain":
            try:
                per_domain_limit = int(self.per_domain_limit_var.get())
                if per_domain_limit <= 0:
                    return True  # Invalid limit, don't crawl
                return self.pages_per_domain[domain] < per_domain_limit
            except ValueError:
                return True
        else:  # unlimited
            return True

    def can_crawl_page(self, domain):
        """Determine if we can crawl another page from this domain"""
        mode = self.limit_mode_var.get()

        if mode == "global":
            return True  # Global limit is checked separately
        elif mode == "per_domain":
            try:
                per_domain_limit = int(self.per_domain_limit_var.get())
                if per_domain_limit <= 0:
                    return False
                return self.pages_per_domain[domain] < per_domain_limit
            except ValueError:
                return False
        else:  # unlimited
            return True

    def check_robots_for_criteria(self, content):
        """Check robots.txt content for long repeating strings or sentences"""
        matched_criteria = []

        # Check for long repeating strings (10+ characters repeated 3+ times)
        # Pattern for repeated characters
        repeating_pattern = r'((.)\2{9,})'  # At least 10 identical characters in a row
        if re.search(repeating_pattern, content):
            matched_criteria.append("Long repeating strings")

        # Check for sentences (multiple words with punctuation)
        # Look for patterns that resemble sentences: words separated by spaces, ending with .!?
        sentence_pattern = r'[A-Z][a-z]+(\s+[a-z]+)+[.!?]'
        if re.search(sentence_pattern, content):
            matched_criteria.append("Contains sentences")

        # Also check for long repeating patterns (like "ababababab")
        repeating_pattern2 = r'(.{2,})\1{4,}'  # Any 2+ char pattern repeated 5+ times
        if re.search(repeating_pattern2, content):
            matched_criteria.append("Long repeating patterns")

        return matched_criteria

    def highlight_interesting_content(self, text_widget, content, criteria):
        """Highlight interesting parts in the robots.txt content"""
        text_widget.delete(1.0, tk.END)
        text_widget.insert(1.0, content)

        # Highlight long repeating strings
        if "Long repeating strings" in criteria:
            # Find sequences of 10+ identical characters
            pattern = r'((.)\2{9,})'
            for match in re.finditer(pattern, content):
                start = match.start()
                end = match.end()
                # Convert to tkinter text indices
                start_line = content[:start].count('\n') + 1
                start_col = start - content[:start].rfind('\n') - 1 if '\n' in content[:start] else start
                end_line = content[:end].count('\n') + 1
                end_col = end - content[:end].rfind('\n') - 1 if '\n' in content[:end] else end

                start_idx = f"{start_line}.{start_col}"
                end_idx = f"{end_line}.{end_col}"
                text_widget.tag_add("long_string", start_idx, end_idx)

        # Highlight sentences
        if "Contains sentences" in criteria:
            pattern = r'[A-Z][a-z]+(\s+[a-z]+)+[.!?]'
            for match in re.finditer(pattern, content):
                start = match.start()
                end = match.end()
                start_line = content[:start].count('\n') + 1
                start_col = start - content[:start].rfind('\n') - 1 if '\n' in content[:start] else start
                end_line = content[:end].count('\n') + 1
                end_col = end - content[:end].rfind('\n') - 1 if '\n' in content[:end] else end

                start_idx = f"{start_line}.{start_col}"
                end_idx = f"{end_line}.{end_col}"
                text_widget.tag_add("sentence", start_idx, end_idx)

        # Highlight long repeating patterns
        if "Long repeating patterns" in criteria:
            pattern = r'(.{2,})\1{4,}'
            for match in re.finditer(pattern, content):
                start = match.start()
                end = match.end()
                start_line = content[:start].count('\n') + 1
                start_col = start - content[:start].rfind('\n') - 1 if '\n' in content[:start] else start
                end_line = content[:end].count('\n') + 1
                end_col = end - content[:end].rfind('\n') - 1 if '\n' in content[:end] else end

                start_idx = f"{start_line}.{start_col}"
                end_idx = f"{end_line}.{end_col}"
                text_widget.tag_add("long_string", start_idx, end_idx)

    def on_robots_select(self, event):
        """Handle selection of robots.txt in the treeview"""
        selection = self.robots_tree.selection()
        if selection:
            item = self.robots_tree.item(selection[0])
            url = item['values'][0]

            # Find the corresponding robots.txt data
            for robot_data in self.interesting_robot_files:
                if robot_data['url'] == url:
                    self.highlight_interesting_content(self.robots_content,
                                                       robot_data['content'],
                                                       robot_data['matched_criteria'])
                    break

    def add_interesting_robots_txt(self, robots_url, content, matched_criteria):
        """Add a robots.txt file to the interesting list if it matches criteria"""
        if matched_criteria:
            # Check if already added
            for existing in self.interesting_robot_files:
                if existing['url'] == robots_url:
                    return

            # Add to list
            robot_entry = {
                'url': robots_url,
                'content': content,
                'matched_criteria': matched_criteria,
                'timestamp': datetime.now()
            }
            self.interesting_robot_files.append(robot_entry)

            # Add to treeview
            criteria_str = ", ".join(matched_criteria)
            self.robots_tree.insert('', tk.END, values=(
                robots_url,
                criteria_str,
                len(content)
            ))

            # Update stats
            self.robots_stats_label.config(
                text=f"Found {len(self.interesting_robot_files)} interesting robots.txt files"
            )

    def toggle_crawl(self):
        if not self.is_crawling:
            self.start_crawling()
        else:
            self.stop_crawling()

    def start_crawling(self):
        start_url = self.start_url_var.get().strip()
        if not start_url:
            messagebox.showwarning("Warning", "Please enter a start URL")
            return

        # Get user agent from UI
        user_agent = self.user_agent_var.get().strip()
        if not user_agent:
            user_agent = DEFAULT_USER_AGENT
        self.user_agent = user_agent

        # Get default delay
        try:
            self.default_delay = float(self.default_delay_var.get())
            if self.default_delay < 0:
                raise ValueError("Delay cannot be negative")
        except ValueError:
            messagebox.showwarning("Warning", "Please enter a valid number for default delay")
            return

        # Validate limits based on mode
        mode = self.limit_mode_var.get()
        max_pages = None
        per_domain_limit = None

        if mode == "global":
            try:
                max_pages = int(self.max_pages_var.get())
                if max_pages <= 0:
                    raise ValueError("Max pages must be positive")
            except ValueError:
                messagebox.showwarning("Warning", "Please enter a valid number for max pages")
                return
        elif mode == "per_domain":
            try:
                per_domain_limit = int(self.per_domain_limit_var.get())
                if per_domain_limit <= 0:
                    raise ValueError("Per-domain limit must be positive")
            except ValueError:
                messagebox.showwarning("Warning", "Please enter a valid number for per-domain page limit")
                return
        # Unlimited mode doesn't need validation

        # Reset crawling state
        self.visited_urls.clear()
        self.urls_to_visit.clear()
        self.robot_parsers.clear()
        self.crawl_delays.clear()
        self.last_crawl_time.clear()
        self.domain_security_status.clear()  # Clear domain security cache
        self.pages_per_domain.clear()  # Clear per-domain page counts
        self.blocked_domains.clear()  # Clear domains blocked for excessive crawl-delay
        self.results_tree.delete(*self.results_tree.get_children())
        self.blocked_tree.delete(*self.blocked_tree.get_children())
        self.page_store.clear()  # Clear indexed pages (SQLite) for new crawl

        # Add start URL
        self.urls_to_visit.append(start_url)

        # Update UI
        self.is_crawling = True
        self.crawl_button.config(text="Stop Crawl")
        self.progress_label.config(text="Crawling...")
        self.progress_var.set(0)

        # Display appropriate limit info
        if mode == "global":
            self.status_bar.config(text=f"Crawling started with {max_pages} page global limit. User-Agent: {user_agent[:30]}...")
        elif mode == "per_domain":
            self.status_bar.config(text=f"Crawling started with {per_domain_limit} page per-domain limit. User-Agent: {user_agent[:30]}...")
        else:
            self.status_bar.config(text=f"Crawling started with unlimited pages. User-Agent: {user_agent[:30]}...")

        # Start crawl thread
        self.crawl_thread = threading.Thread(target=self.crawl_worker, args=(max_pages, per_domain_limit))
        self.crawl_thread.daemon = True
        self.crawl_thread.start()

    def crawl_worker(self, max_pages, per_domain_limit):
        crawled_count = 0
        mode = self.limit_mode_var.get()

        while self.is_crawling and self.urls_to_visit:
            # Check global limit if in global mode
            if mode == "global" and max_pages and crawled_count >= max_pages:
                break

            try:
                url = self.urls_to_visit.popleft()

                if url in self.visited_urls:
                    continue

                # Get domain and check per-domain limit
                domain = self.get_domain(url)

                # Skip domains that were blocked for having an excessive Crawl-delay
                if domain in self.blocked_domains:
                    blocked_delay = self.blocked_domains[domain]['crawl_delay']
                    max_delay = self.get_max_crawl_delay()
                    self.crawl_queue.put((
                        "status",
                        f"Skipped {url} - {domain} is blocked (Crawl-delay {blocked_delay}s > {max_delay}s)"
                    ))
                    continue

                # Check if we've reached per-domain limit
                if mode == "per_domain" and per_domain_limit:
                    if self.pages_per_domain[domain] >= per_domain_limit:
                        self.crawl_queue.put(("status", f"Skipped {url} - domain {domain} reached limit ({per_domain_limit} pages)"))
                        continue
                # Unlimited mode has no limit check

                # Check robots.txt
                if not self.can_fetch(url):
                    self.crawl_queue.put(("status", f"Skipped {url} (robots.txt)"))
                    continue

                # Respect crawl delay for this domain
                if domain in self.last_crawl_time:
                    delay = self.get_crawl_delay(domain)
                    if delay > 0:
                        elapsed = time.time() - self.last_crawl_time[domain]
                        if elapsed < delay:
                            wait_time = delay - elapsed
                            self.crawl_queue.put(("status", f"Respecting crawl delay for {domain}: waiting {wait_time:.1f}s"))
                            time.sleep(wait_time)

                # Fetch the page
                content = self.fetch_url(url)
                if content:
                    # Parse page and extract metadata
                    page_info = self.parse_page(url, content)

                    # Check security status for this domain (only once per domain)
                    security_status = self.check_domain_security(url)
                    security_marker = "🔒 HTTPS" if security_status else "⚠️ HTTP-Only"

                    # Store in the SQLite-backed index instead of an in-memory dict
                    self.page_store.insert_page(page_info, domain, security_status)

                    self.visited_urls.add(url)
                    crawled_count += 1
                    self.pages_per_domain[domain] += 1

                    # Update last crawl time for this domain
                    self.last_crawl_time[domain] = time.time()

                    # Extract links and add to queue (BFS)
                    for link in page_info.links:
                        if link not in self.visited_urls and link not in self.urls_to_visit:
                            link_domain = self.get_domain(link)

                            # Don't bother queuing pages from a domain we've already blocked
                            if link_domain in self.blocked_domains:
                                continue

                            # For per-domain mode, check if we can add more from this domain
                            if mode == "per_domain" and per_domain_limit:
                                if self.pages_per_domain[link_domain] < per_domain_limit:
                                    self.urls_to_visit.append(link)
                            else:
                                # Global and unlimited modes don't filter when adding to queue
                                self.urls_to_visit.append(link)

                    # Update GUI
                    self.crawl_queue.put(("page", (page_info, domain, security_marker)))

                    # Display first page
                    if crawled_count == 1:
                        self.crawl_queue.put(("display", (url, content)))

                # Update progress
                if mode == "global" and max_pages:
                    progress = (crawled_count / max_pages) * 100
                    self.crawl_queue.put(("progress", progress))
                elif mode == "per_domain" and per_domain_limit:
                    # For per-domain, we show number of pages crawled (no percentage)
                    self.crawl_queue.put(("progress", 0))  # Don't show progress bar
                else:
                    self.crawl_queue.put(("progress", 0))  # Unlimited mode no progress bar

                self.crawl_queue.put(("count", crawled_count))

            except Exception as e:
                self.crawl_queue.put(("error", f"Error crawling {url}: {str(e)}"))

        # Crawling finished
        finish_msg = f"Crawled {crawled_count} pages"
        if mode == "per_domain" and per_domain_limit:
            finish_msg += f" (limit: {per_domain_limit} per domain)"
        elif mode == "global" and max_pages:
            finish_msg += f" (global limit: {max_pages})"
        else:
            finish_msg += " (unlimited)"

        self.crawl_queue.put(("finished", finish_msg))
        self.is_crawling = False

    def get_domain(self, url):
        """Extract domain from URL"""
        parsed = urlparse(url)
        return parsed.netloc

    def get_crawl_delay(self, domain):
        """Get crawl delay for a domain"""
        if domain in self.crawl_delays:
            return self.crawl_delays[domain]
        return self.default_delay

    def parse_robots_txt_for_crawl_delay(self, content):
        """Parse robots.txt content for Crawl-delay directive specific to our user agent or wildcard"""
        lines = content.split('\n')

        # States for parsing
        in_user_agent_section = False
        in_our_agent_section = False
        in_wildcard_section = False

        our_agent_crawl_delay = None
        wildcard_crawl_delay = None

        # Process each line
        for line in lines:
            line = line.strip()

            # Skip empty lines and comments
            if not line or line.startswith('#'):
                continue

            # Convert to lowercase for case-insensitive matching
            line_lower = line.lower()

            # Check for User-agent directive
            if line_lower.startswith('user-agent:'):
                # Reset section flags
                in_user_agent_section = True
                in_our_agent_section = False
                in_wildcard_section = False

                # Get the user agent value
                agent_value = line.split(':', 1)[1].strip()

                # Check if this section is for our user agent
                if agent_value == self.user_agent:
                    in_our_agent_section = True
                # Check if this section is for wildcard
                elif agent_value == '*':
                    in_wildcard_section = True

            # Check for Crawl-delay directive
            elif line_lower.startswith('crawl-delay:') and in_user_agent_section:
                try:
                    # Extract the delay value
                    delay_str = line.split(':', 1)[1].strip()
                    delay_value = float(delay_str)

                    # Store based on which section we're in
                    if in_our_agent_section:
                        our_agent_crawl_delay = delay_value
                    elif in_wildcard_section:
                        wildcard_crawl_delay = delay_value
                except (ValueError, IndexError):
                    # Skip invalid crawl delay values
                    continue

        # Return the appropriate crawl delay
        # Priority: 1. Our specific user agent, 2. Wildcard (*), 3. None
        if our_agent_crawl_delay is not None:
            return our_agent_crawl_delay
        elif wildcard_crawl_delay is not None:
            return wildcard_crawl_delay
        else:
            return None

    def can_fetch(self, url):
        """Check robots.txt for given URL"""
        try:
            parsed = urlparse(url)
            base_url = f"{parsed.scheme}://{parsed.netloc}/"
            domain = parsed.netloc

            # Already blocked for excessive Crawl-delay - refuse immediately
            if domain in self.blocked_domains:
                return False

            if base_url not in self.robot_parsers:
                robots_url = urljoin(base_url, "/robots.txt")
                rp = RobotFileParser()
                try:
                    rp.set_url(robots_url)

                    # Fetch robots.txt manually to parse Crawl-delay
                    headers = {'User-Agent': self.user_agent}
                    response = requests.get(robots_url, headers=headers, timeout=10)

                    if response.status_code == 200:
                        # Parse the robots.txt content
                        content = response.text

                        # Check if this robots.txt is interesting
                        matched_criteria = self.check_robots_for_criteria(content)
                        if matched_criteria:
                            self.add_interesting_robots_txt(robots_url, content, matched_criteria)

                        # Check for Crawl-delay directive for our user agent or wildcard
                        crawl_delay = self.parse_robots_txt_for_crawl_delay(content)
                        if crawl_delay is not None:
                            self.crawl_delays[domain] = crawl_delay
                            self.crawl_queue.put(("status", f"Found Crawl-delay: {crawl_delay}s for {domain} (for {self.user_agent} or *)"))

                            # If the site demands an excessive delay, don't crawl it automatically -
                            # block it and surface it on the "Blocked Sites" tab instead.
                            max_delay = self.get_max_crawl_delay()
                            if max_delay is not None and crawl_delay > max_delay:
                                self.block_domain(domain, robots_url, crawl_delay, url)
                                self.robot_parsers[base_url] = rp
                                return False
                        else:
                            # Use default delay
                            self.crawl_delays[domain] = self.default_delay
                            self.crawl_queue.put(("status", f"No Crawl-delay found for {domain}, using default: {self.default_delay}s"))

                        # Parse robots.txt with RobotFileParser
                        rp.parse(content.split('\n'))
                    else:
                        # If robots.txt not found, assume all is allowed
                        rp.allow_all = True
                        self.crawl_delays[domain] = self.default_delay
                        self.crawl_queue.put(("status", f"No robots.txt found for {domain}, using default delay: {self.default_delay}s"))

                    self.robot_parsers[base_url] = rp

                except Exception as e:
                    # If robots.txt can't be read, assume all is allowed
                    self.crawl_queue.put(("status", f"Could not fetch robots.txt for {domain}: {str(e)}"))
                    rp = RobotFileParser()
                    rp.allow_all = True
                    self.robot_parsers[base_url] = rp
                    self.crawl_delays[domain] = self.default_delay

            return self.robot_parsers[base_url].can_fetch(self.user_agent, url)
        except Exception as e:
            self.crawl_queue.put(("error", f"Error checking robots.txt for {url}: {str(e)}"))
            return True  # Default to allowing if there's an error

    def parse_page(self, url, content):
        """Parse HTML content and extract metadata"""
        soup = BeautifulSoup(content, 'html.parser')

        # Extract title
        title = ""
        if soup.title and soup.title.string:
            title = soup.title.string.strip()

        # Extract description from meta tags
        description = ""
        meta_desc = soup.find('meta', attrs={'name': 'description'})
        if meta_desc and meta_desc.get('content'):
            description = meta_desc['content'].strip()
        else:
            # Try Open Graph description
            og_desc = soup.find('meta', attrs={'property': 'og:description'})
            if og_desc and og_desc.get('content'):
                description = og_desc['content'].strip()
            else:
                # Use first paragraph as fallback
                first_p = soup.find('p')
                if first_p and first_p.text:
                    description = first_p.text[:200].strip() + "..."

        # Extract main content (simplified)
        main_content = ""
        main_elem = soup.find('main') or soup.find('article') or soup.body
        if main_elem:
            # Get text content, limit to first 2000 chars for search indexing
            main_content = main_elem.get_text()[:2000]

        # Extract links
        links = []
        for link in soup.find_all('a', href=True):
            href = link['href']
            absolute_url = urljoin(url, href)
            parsed = urlparse(absolute_url)
            if parsed.scheme in ('http', 'https'):
                links.append(absolute_url)

        return WebPage(url, title, description, main_content, links)

    def fetch_url(self, url):
        """Fetch URL content with error handling"""
        try:
            headers = {'User-Agent': self.user_agent}
            response = requests.get(url, headers=headers, timeout=10)
            response.raise_for_status()
            # Check content type
            content_type = response.headers.get('content-type', '')
            if 'text/html' not in content_type:
                return None
            return response.text
        except Exception as e:
            self.crawl_queue.put(("error", f"Failed to fetch {url}: {str(e)}"))
            return None

    def perform_search(self):
        """Search through indexed pages (queries the SQLite index directly)"""
        query = self.search_var.get().strip().lower()
        if not query:
            messagebox.showinfo("Search", "Please enter a search query")
            return

        # Clear previous results
        self.search_results = []
        self.search_tree.delete(*self.search_tree.get_children())
        self.search_preview.config(state=tk.NORMAL)
        self.search_preview.delete(1.0, tk.END)
        self.search_preview.config(state=tk.DISABLED)

        # Switch to search tab
        self.notebook.select(1)

        # Perform search against the SQLite-backed store
        self.search_results = self.page_store.search(query)

        # Display results
        for page in self.search_results:
            self.search_tree.insert('', tk.END, values=(
                page.title[:50] + ("..." if len(page.title) > 50 else ""),
                page.url[:60] + ("..." if len(page.url) > 60 else ""),
                page.description[:80] + ("..." if len(page.description) > 80 else "")
            ))

        # Update stats
        self.search_stats_label.config(
            text=f"Found {len(self.search_results)} results for '{query}' in {self.page_store.count()} indexed pages"
        )

        if self.search_results:
            # Select first result
            self.search_tree.selection_set(self.search_tree.get_children()[0])
            self.show_search_preview(self.search_results[0])

    def show_search_preview(self, page):
        """Show preview of selected search result"""
        self.search_preview.config(state=tk.NORMAL)
        self.search_preview.delete(1.0, tk.END)

        # Insert page information
        self.search_preview.insert(tk.END, f"Title: {page.title}\n", "title")
        self.search_preview.insert(tk.END, f"URL: {page.url}\n", "plain")
        self.search_preview.insert(tk.END, f"Crawled: {page.timestamp.strftime('%Y-%m-%d %H:%M:%S')}\n\n", "plain")

        self.search_preview.insert(tk.END, "Description:\n", "heading")
        self.search_preview.insert(tk.END, f"{page.description}\n\n", "description")

        self.search_preview.insert(tk.END, "Preview:\n", "heading")
        preview_text = page.content[:500] + ("..." if len(page.content) > 500 else "")
        self.search_preview.insert(tk.END, preview_text, "plain")

        self.search_preview.config(state=tk.DISABLED)

    def update_gui(self):
        """Process messages from crawl thread"""
        try:
            while True:
                msg_type, data = self.crawl_queue.get_nowait()

                if msg_type == "page":
                    page, domain, security_marker = data
                    delay = self.get_crawl_delay(domain)

                    # Add to treeview with security marker
                    self.results_tree.insert('', tk.END, values=(
                        page.title[:40] + ("..." if len(page.title) > 40 else ""),
                        page.url[:50] + ("..." if len(page.url) > 50 else ""),
                        security_marker,
                        page.description[:70] + ("..." if len(page.description) > 70 else ""),
                        f"{delay}s"
                    ))

                elif msg_type == "display":
                    url, content = data
                    self.display_content(url, content)

                elif msg_type == "progress":
                    if data > 0:  # Only show progress bar for global mode
                        self.progress_var.set(data)
                    else:
                        self.progress_var.set(0)  # Hide progress for other modes

                elif msg_type == "count":
                    self.progress_label.config(text=f"Crawled: {data}")
                    self.stats_label.config(text=f"Pages: {self.page_store.count()}")

                    # Show per-domain stats if in per-domain mode
                    mode = self.limit_mode_var.get()
                    if mode == "per_domain" and self.pages_per_domain:
                        domain_stats = ", ".join([f"{d}: {c}" for d, c in list(self.pages_per_domain.items())[:3]])
                        if len(self.pages_per_domain) > 3:
                            domain_stats += f" (+{len(self.pages_per_domain)-3} more)"
                        self.status_bar.config(text=f"Pages per domain: {domain_stats}")

                elif msg_type == "blocked":
                    info = data
                    self.blocked_tree.insert('', tk.END, values=(
                        info['domain'],
                        f"{info['crawl_delay']}s",
                        info['sample_url'],
                        info['robots_url']
                    ))

                elif msg_type == "manual_response":
                    url, response = data
                    self.display_manual_response(url, response)

                elif msg_type == "manual_response_error":
                    url, err = data
                    self.manual_response_text.config(state=tk.NORMAL)
                    self.manual_response_text.delete(1.0, tk.END)
                    self.manual_response_text.insert(tk.END, f"Request to {url} failed:\n\n{err}")
                    self.manual_response_text.config(state=tk.DISABLED)
                    self.send_manual_button.config(state=tk.NORMAL)
                    self.status_bar.config(text=f"Manual request to {url} failed: {err}")

                elif msg_type == "status":
                    self.status_bar.config(text=data)

                elif msg_type == "error":
                    self.status_bar.config(text=f"Error: {data}")

                elif msg_type == "finished":
                    self.crawl_button.config(text="Start Crawl")
                    self.progress_label.config(text="Finished")
                    self.status_bar.config(text=data)
                    messagebox.showinfo("Crawling Complete", data)

                self.crawl_queue.task_done()
        except queue.Empty:
            pass

        # Keep polling regardless of crawl state - manual fetch responses and other
        # background messages can arrive even when no crawl is running
        self.root.after(100, self.update_gui)

    def stop_crawling(self):
        self.is_crawling = False
        self.crawl_button.config(text="Start Crawl")
        self.status_bar.config(text="Crawling stopped")

    def visit_url(self):
        url = self.url_entry.get().strip()
        if not url:
            return

        if not url.startswith(('http://', 'https://')):
            url = 'https://' + url

        self.current_url = url
        self.status_bar.config(text=f"Fetching {url}...")

        # Check if already indexed (SQLite lookup)
        if self.page_store.has_page(url):
            page = self.page_store.get_page(url)
            self.display_content_from_page(page)
        else:
            # Fetch in separate thread
            thread = threading.Thread(target=self.fetch_and_display, args=(url,))
            thread.daemon = True
            thread.start()

    def fetch_and_display(self, url):
        # Get current user agent
        user_agent = self.user_agent_var.get().strip()
        if not user_agent:
            user_agent = DEFAULT_USER_AGENT
        self.user_agent = user_agent

        content = self.fetch_url(url)
        if content:
            self.crawl_queue.put(("display", (url, content)))
            self.status_bar.config(text=f"Loaded {url}")

    def display_content(self, url, html_content):
        """Display HTML content in simplified text format"""
        # Parse page
        page_info = self.parse_page(url, html_content)

        # Store in the SQLite-backed index
        domain = self.get_domain(url)
        security_status = self.domain_security_status.get(domain)
        self.page_store.insert_page(page_info, domain, security_status)

        # Display content
        self.display_content_from_page(page_info)

        # Update URL entry
        self.url_entry.delete(0, tk.END)
        self.url_entry.insert(0, url)

    def display_content_from_page(self, page):
        """Display page content from WebPage object (no security warnings in browser tab)"""
        self.current_url = page.url
        self.current_content = page.content

        # Switch to browser tab
        self.notebook.select(0)

        # Clear current content
        self.content_text.config(state=tk.NORMAL)
        self.content_text.delete(1.0, tk.END)

        # Display title
        self.content_text.insert(tk.END, page.title + "\n\n", "title")

        # Display URL and timestamp
        self.content_text.insert(tk.END, f"URL: {page.url}\n", "plain")
        self.content_text.insert(tk.END, f"Crawled: {page.timestamp.strftime('%Y-%m-%d %H:%M:%S')}\n\n", "plain")

        # Display description if available
        if page.description:
            self.content_text.insert(tk.END, "Description:\n", "heading")
            self.content_text.insert(tk.END, page.description + "\n\n", "description")

        # Display content preview
        self.content_text.insert(tk.END, "Content:\n", "heading")
        content_preview = page.content[:2000]
        if len(page.content) > 2000:
            content_preview += "...\n\n[Content truncated for display]"
        self.content_text.insert(tk.END, content_preview + "\n\n", "plain")

        # Display links section
        if page.links:
            self.content_text.insert(tk.END, "\n" + "="*50 + "\n", "plain")
            self.content_text.insert(tk.END, f"Links found ({len(page.links)}):\n", "heading")

            for link in page.links[:20]:  # Show first 20 links
                self.content_text.insert(tk.END, f"• {link}\n", "link")

            if len(page.links) > 20:
                self.content_text.insert(tk.END, f"... and {len(page.links) - 20} more\n", "plain")

        self.content_text.config(state=tk.DISABLED)

    def on_search_result_double_click(self, event):
        """Handle double-click on search result"""
        selection = self.search_tree.selection()
        if selection:
            item = self.search_tree.item(selection[0])
            url = item['values'][1]

            # Find the page object
            for page in self.search_results:
                if page.url == url:
                    self.url_entry.delete(0, tk.END)
                    self.url_entry.insert(0, url)
                    self.display_content_from_page(page)
                    self.notebook.select(0)  # Switch to browser tab
                    break

    def on_crawl_result_double_click(self, event):
        """Handle double-click on crawl result"""
        selection = self.results_tree.selection()
        if selection:
            item = self.results_tree.item(selection[0])
            url = item['values'][1]

            page = self.page_store.get_page(url)
            if page:
                self.url_entry.delete(0, tk.END)
                self.url_entry.insert(0, url)
                self.display_content_from_page(page)
                self.notebook.select(0)  # Switch to browser tab

    def refresh_results_tree(self):
        """Rebuild the crawling results table from the current SQLite index (used after import)"""
        self.results_tree.delete(*self.results_tree.get_children())
        for page in self.page_store.all_pages():
            domain = self.get_domain(page.url)
            security_status = self.domain_security_status.get(domain)
            if security_status is None:
                security_status = self.page_store.get_security_status(domain)
            if security_status is True:
                security_marker = "🔒 HTTPS"
            elif security_status is False:
                security_marker = "⚠️ HTTP-Only"
            else:
                security_marker = "—"
            delay = self.get_crawl_delay(domain)

            self.results_tree.insert('', tk.END, values=(
                page.title[:40] + ("..." if len(page.title) > 40 else ""),
                page.url[:50] + ("..." if len(page.url) > 50 else ""),
                security_marker,
                page.description[:70] + ("..." if len(page.description) > 70 else ""),
                f"{delay}s"
            ))

        self.stats_label.config(text=f"Pages: {self.page_store.count()}")

    def export_index(self):
        """Export the indexed pages to a standalone SQLite (.db) or JSON file the user chooses"""
        if self.page_store.count() == 0:
            messagebox.showinfo("Export", "No indexed pages to export yet.")
            return

        dest_path = filedialog.asksaveasfilename(
            title="Export indexed pages",
            defaultextension=".db",
            filetypes=[("SQLite database", "*.db"), ("JSON file", "*.json"), ("All files", "*.*")]
        )
        if not dest_path:
            return

        try:
            if dest_path.lower().endswith('.json'):
                self.page_store.export_to_json(dest_path)
            else:
                self.page_store.export_to_sqlite(dest_path)

            count = self.page_store.count()
            self.status_bar.config(text=f"Exported {count} pages to {dest_path}")
            messagebox.showinfo("Export Complete", f"Exported {count} pages to:\n{dest_path}")
        except Exception as e:
            messagebox.showerror("Export Failed", f"Could not export index:\n{str(e)}")

    def import_index(self):
        """Import previously exported pages from a SQLite (.db) or JSON file"""
        src_path = filedialog.askopenfilename(
            title="Import indexed pages",
            filetypes=[("SQLite database", "*.db"), ("JSON file", "*.json"), ("All files", "*.*")]
        )
        if not src_path:
            return

        merge = messagebox.askyesno(
            "Import Mode",
            "Merge with the current index?\n\n"
            "Yes = add imported pages to the current index\n"
            "No = replace the current index entirely"
        )

        try:
            if src_path.lower().endswith('.json'):
                count = self.page_store.import_from_json(src_path, merge=merge)
            else:
                count = self.page_store.import_from_sqlite(src_path, merge=merge)

            self.refresh_results_tree()
            self.status_bar.config(text=f"Imported {count} pages from {src_path}")
            messagebox.showinfo("Import Complete", f"Imported {count} pages.")
        except Exception as e:
            messagebox.showerror("Import Failed", f"Could not import index:\n{str(e)}")

    def on_closing(self):
        """Handle window closing"""
        self.is_crawling = False
        if self.crawl_thread and self.crawl_thread.is_alive():
            self.crawl_thread.join(timeout=2)

        # Close and remove the temporary SQLite index file
        try:
            self.page_store.close()
        except Exception:
            pass
        try:
            if os.path.exists(self.db_path):
                os.remove(self.db_path)
        except Exception:
            pass

        self.root.destroy()

    def run(self):
        self.root.mainloop()


def main():
    app = WebCrawlerBrowser()
    app.run()


if __name__ == "__main__":
    main()
