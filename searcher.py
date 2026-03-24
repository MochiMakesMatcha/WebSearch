import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, StringVar, IntVar, BooleanVar
import threading
import queue
import time
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

        # Data storage
        self.visited_urls = set()
        self.urls_to_visit = deque()
        self.robot_parsers = {}
        self.crawl_delays = {}  # Store crawl delays per domain
        self.last_crawl_time = {}  # Track last crawl time per domain
        self.indexed_pages = {}  # Store page objects for search
        self.search_results = []

        # Domain security status tracking
        self.domain_security_status = {}  # domain -> bool (True if HTTPS-only, False if HTTP-only/unsecured)

        # Per-domain page counting
        self.pages_per_domain = defaultdict(int)  # Track pages crawled per domain
        self.domain_page_limits = {}  # Store per-domain limits (if using per-domain mode)

        # Store robots.txt files that match criteria
        self.interesting_robot_files = []  # List of dicts with url, content, matched_criteria

        # Current page data
        self.current_url = ""
        self.current_content = ""

        # User agent - will be set from UI or default
        self.user_agent = DEFAULT_USER_AGENT

        self.setup_ui()
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)

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
        self.visit_button.pack(side=tk.LEFT)

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

        self.notebook.add(self.browse_tab, text="Browser")
        self.notebook.add(self.search_tab, text="Search Results")
        self.notebook.add(self.crawl_tab, text="Crawling")
        self.notebook.add(self.robots_tab, text="Interesting robots.txt")

        # Setup tabs
        self.setup_browse_tab()
        self.setup_search_tab()
        self.setup_crawl_tab()
        self.setup_robots_tab()

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
        self.default_delay_entry.pack(side=tk.LEFT)

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
        self.results_tree.delete(*self.results_tree.get_children())
        self.indexed_pages.clear()  # Clear indexed pages for new crawl

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

        # Start GUI update thread
        self.root.after(100, self.update_gui)

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

                    # Store in index
                    self.indexed_pages[url] = page_info

                    self.visited_urls.add(url)
                    crawled_count += 1
                    self.pages_per_domain[domain] += 1

                    # Update last crawl time for this domain
                    self.last_crawl_time[domain] = time.time()

                    # Extract links and add to queue (BFS)
                    for link in page_info.links:
                        if link not in self.visited_urls and link not in self.urls_to_visit:
                            # For per-domain mode, check if we can add more from this domain
                            if mode == "per_domain" and per_domain_limit:
                                link_domain = self.get_domain(link)
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
        """Search through indexed pages"""
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

        # Perform search
        results = []
        for url, page in self.indexed_pages.items():
            # Calculate relevance score
            score = 0

            # Check title
            if query in page.title.lower():
                score += 3

            # Check description
            if query in page.description.lower():
                score += 2

            # Check content
            if query in page.content.lower():
                score += 1

            # Check URL
            if query in url.lower():
                score += 1

            if score > 0:
                results.append((score, page))

        # Sort by relevance
        results.sort(key=lambda x: x[0], reverse=True)
        self.search_results = [page for _, page in results]

        # Display results
        for page in self.search_results:
            self.search_tree.insert('', tk.END, values=(
                page.title[:50] + ("..." if len(page.title) > 50 else ""),
                page.url[:60] + ("..." if len(page.url) > 60 else ""),
                page.description[:80] + ("..." if len(page.description) > 80 else "")
            ))

        # Update stats
        self.search_stats_label.config(
            text=f"Found {len(results)} results for '{query}' in {len(self.indexed_pages)} indexed pages"
        )

        if results:
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
                    self.stats_label.config(text=f"Pages: {len(self.indexed_pages)}")

                    # Show per-domain stats if in per-domain mode
                    mode = self.limit_mode_var.get()
                    if mode == "per_domain" and self.pages_per_domain:
                        domain_stats = ", ".join([f"{d}: {c}" for d, c in list(self.pages_per_domain.items())[:3]])
                        if len(self.pages_per_domain) > 3:
                            domain_stats += f" (+{len(self.pages_per_domain)-3} more)"
                        self.status_bar.config(text=f"Pages per domain: {domain_stats}")

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

        # Continue updating if still crawling
        if self.is_crawling:
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

        # Check if already indexed
        if url in self.indexed_pages:
            page = self.indexed_pages[url]
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

        # Store in index
        self.indexed_pages[url] = page_info

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

            if url in self.indexed_pages:
                page = self.indexed_pages[url]
                self.url_entry.delete(0, tk.END)
                self.url_entry.insert(0, url)
                self.display_content_from_page(page)
                self.notebook.select(0)  # Switch to browser tab

    def on_closing(self):
        """Handle window closing"""
        self.is_crawling = False
        if self.crawl_thread and self.crawl_thread.is_alive():
            self.crawl_thread.join(timeout=2)
        self.root.destroy()

    def run(self):
        self.root.mainloop()

def main():
    app = WebCrawlerBrowser()
    app.run()

if __name__ == "__main__":
    main()
