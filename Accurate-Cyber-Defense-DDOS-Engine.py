#!/usr/bin/env python3
"""
Enhanced Cyber Security Network Diagnostic Tool with GUI
A comprehensive network security tool with advanced diagnostics capabilities
"""

import argparse
import asyncio
import ipaddress
import json
import os
import random
import re
import socket
import subprocess
import sys
import threading
import time
import dns.resolver
import netifaces
import psutil
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from typing import Dict, List, Set, Tuple, Optional, Any, Callable

try:
    import scapy.all as scapy
    from scapy.layers.inet import IP, ICMP, TCP, UDP
    from scapy.layers.inet6 import IPv6, ICMPv6EchoRequest
    from scapy.sendrecv import send, sr, sr1, srp
    from scapy.volatile import RandShort
except ImportError:
    print("Scapy not installed. Some features may not work properly.")
    
try:
    import requests
    from requests.exceptions import RequestException
except ImportError:
    print("Requests library not installed. Web features may not work properly.")

try:
    import matplotlib.pyplot as plt
    import numpy as np
    from matplotlib.ticker import MaxNLocator
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    from matplotlib.figure import Figure
    MATPLOTLIB_AVAILABLE = True
except ImportError:
    print("Matplotlib not installed. Graphing features disabled.")
    MATPLOTLIB_AVAILABLE = False

try:
    import tkinter as tk
    from tkinter import ttk, messagebox, scrolledtext, filedialog
    from tkinter import Menu
    GUI_AVAILABLE = True
except ImportError:
    print("Tkinter not available. GUI features disabled.")
    GUI_AVAILABLE = False

# Color codes for green theme
class Colors:
    GREEN = '\033[92m'
    DARK_GREEN = '\033[32m'
    LIGHT_GREEN = '\033[1;92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    PURPLE = '\033[95m'
    END = '\033[0m'
    BOLD = '\033[1m'

# Banner for the tool
BANNER = f"""
{Colors.GREEN}{Colors.BOLD}
  ██████ ▓█████  ██▀███   ██▓ ██▓███  ▄▄▄█████▓▓█████  ██▀███  
▒██    ▒ ▓█   ▀ ▓██ ▒ ██▒▓██▒▓██░  ██▒▓  ██▒ ▓▒▓█   ▀ ▓██ ▒ ██▒
░ ▓██▄   ▒███   ▓██ ░▄█ ▒▒██▒▓██░ ██▓▒▒ ▓██░ ▒░▒███   ▓██ ░▄█ ▒
  ▒   ██▒▒▓█  ▄ ▒██▀▀█▄  ░██░▒██▄█▓▒ ▒░ ▓██▓ ░ ▒▓█  ▄ ▒██▀▀█▄  
▒██████▒▒░▒████▒░██▓ ▒██▒░██░▒██▒ ░  ░  ▒██▒ ░ ░▒████▒░██▓ ▒██▒
▒ ▒▓▒ ▒ ░░░ ▒░ ░░ ▒▓ ░▒▓░░▓  ▒▓▒░ ░  ░  ▒ ░░   ░░ ▒░ ░░ ▒▓ ░▒▓░
░ ░▒  ░ ░ ░ ░  ░  ░▒ ░ ▒░ ▒ ░░▒ ░         ░     ░ ░  ░  ░▒ ░ ▒░
░  ░  ░     ░     ░░   ░  ▒ ░░░         ░         ░     ░░   ░ 
      ░     ░  ░   ░      ░                       ░  ░   ░     
                                                                
{Colors.END}
{Colors.LIGHT_GREEN}Accurate Cyber Defense DDOS Engine{Colors.END}
{Colors.DARK_GREEN}Version 3.0 | Advanced Network Operations Suite{Colors.END}
"""

class CyberSecurityTool:
    def __init__(self, use_gui=False):
        self.monitoring = False
        self.monitored_ips = set()
        self.traffic_generation = False
        self.traffic_threads = []
        self.config = {
            'telegram_token': None,
            'telegram_chat_id': None,
            'max_threads': 100,
            'ping_timeout': 2,
            'scan_timeout': 1,
            'traffic_intensity': 'medium',
            'dns_servers': ['8.8.8.8', '1.1.1.1', '9.9.9.9'],
            'network_interface': self.get_default_interface(),
            'packet_count_history': [],
            'response_time_history': [],
            'http_user_agents': [
                'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36',
                'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/14.1.1 Safari/605.1.15',
                'Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:89.0) Gecko/20100101 Firefox/89.0',
                'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/92.0.4515.107 Safari/537.36'
            ],
            'http_targets': [
                '/', '/index.html', '/about', '/contact', '/products',
                '/services', '/blog', '/news', '/api/v1/users', '/login'
            ]
        }
        self.ip_list = set()
        self.log_file = "cyber_tool.log"
        self.operation_log = []
        self.executor = ThreadPoolExecutor(max_workers=self.config['max_threads'])
        self.lock = threading.Lock()
        self.hostname_cache = {}
        self.use_gui = use_gui and GUI_AVAILABLE
        
        if self.use_gui:
            self.setup_gui()
        
    def setup_gui(self):
        """Setup the graphical user interface"""
        self.root = tk.Tk()
        self.root.title("Accurate Cyber Defense DDOS Engine")
        self.root.geometry("1200x800")
        self.root.configure(bg='#003300')  # Dark green background
        
        # Set green theme
        self.style = ttk.Style()
        self.style.theme_use('clam')
        
        # Configure colors
        self.style.configure('TFrame', background='#003300')
        self.style.configure('TLabel', background='#003300', foreground='#00FF00')
        self.style.configure('TButton', background='#006600', foreground='white')
        self.style.configure('TEntry', fieldbackground='#002200', foreground='#00FF00')
        self.style.configure('TNotebook', background='#003300')
        self.style.configure('TNotebook.Tab', background='#006600', foreground='white')
        
        # Create menu bar
        self.create_menu()
        
        # Create main frame
        self.main_frame = ttk.Frame(self.root)
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Create notebook (tabs)
        self.notebook = ttk.Notebook(self.main_frame)
        self.notebook.pack(fill=tk.BOTH, expand=True)
        
        # Create tabs
        self.dashboard_tab = ttk.Frame(self.notebook)
        self.monitoring_tab = ttk.Frame(self.notebook)
        self.scanning_tab = ttk.Frame(self.notebook)
        self.traffic_tab = ttk.Frame(self.notebook)
        self.diagnostics_tab = ttk.Frame(self.notebook)
        self.visualization_tab = ttk.Frame(self.notebook)
        self.log_tab = ttk.Frame(self.notebook)
        
        self.notebook.add(self.dashboard_tab, text='Dashboard')
        self.notebook.add(self.monitoring_tab, text='Monitoring')
        self.notebook.add(self.scanning_tab, text='Scanning')
        self.notebook.add(self.traffic_tab, text='Traffic')
        self.notebook.add(self.diagnostics_tab, text='Diagnostics')
        self.notebook.add(self.visualization_tab, text='Visualization')
        self.notebook.add(self.log_tab, text='Log')
        
        # Setup each tab
        self.setup_dashboard_tab()
        self.setup_monitoring_tab()
        self.setup_scanning_tab()
        self.setup_traffic_tab()
        self.setup_diagnostics_tab()
        self.setup_visualization_tab()
        self.setup_log_tab()
        
        # Status bar
        self.status_var = tk.StringVar()
        self.status_var.set("Ready")
        self.status_bar = ttk.Label(self.root, textvariable=self.status_var, relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
    def create_menu(self):
        """Create the menu bar"""
        menubar = Menu(self.root)
        self.root.config(menu=menubar)
        
        # File menu
        file_menu = Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Export Data", command=self.export_data)
        file_menu.add_command(label="Save Log", command=self.save_log)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.root.quit)
        
        # Tools menu
        tools_menu = Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Tools", menu=tools_menu)
        tools_menu.add_command(label="Network Info", command=self.show_network_info)
        tools_menu.add_command(label="Test Connection", command=self.test_connection)
        tools_menu.add_command(label="Bandwidth Monitor", command=lambda: self.monitor_bandwidth(10))
        
        # View menu
        view_menu = Menu(menubar, tearoff=0)
        menubar.add_cascade(label="View", menu=view_menu)
        view_menu.add_command(label="Refresh", command=self.refresh_dashboard)
        view_menu.add_command(label="Clear Log", command=self.clear_log)
        
        # Settings menu
        settings_menu = Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Settings", menu=settings_menu)
        settings_menu.add_command(label="Telegram Config", command=self.show_telegram_config)
        settings_menu.add_command(label="Interface Settings", command=self.show_interface_settings)
        
    def setup_dashboard_tab(self):
        """Setup the dashboard tab"""
        # Header
        header = ttk.Label(self.dashboard_tab, text="Network Security Dashboard", 
                          font=("Arial", 16, "bold"))
        header.pack(pady=10)
        
        # Stats frame
        stats_frame = ttk.Frame(self.dashboard_tab)
        stats_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # Stats labels
        stats_data = [
            ("Monitored IPs", "0"),
            ("Traffic Active", "No"),
            ("Open Ports", "0"),
            ("Log Entries", "0")
        ]
        
        self.stats_vars = {}
        for i, (label, value) in enumerate(stats_data):
            frame = ttk.Frame(stats_frame)
            frame.grid(row=0, column=i, padx=10, pady=5, sticky="ew")
            
            ttk.Label(frame, text=label, font=("Arial", 10)).pack()
            var = tk.StringVar(value=value)
            self.stats_vars[label.lower().replace(" ", "_")] = var
            ttk.Label(frame, textvariable=var, font=("Arial", 12, "bold")).pack()
        
        # Quick actions frame
        actions_frame = ttk.LabelFrame(self.dashboard_tab, text="Quick Actions")
        actions_frame.pack(fill=tk.X, padx=10, pady=10)
        
        action_buttons = [
            ("Start Monitoring", self.start_monitoring_gui),
            ("Stop All", self.stop_monitoring),
            ("Test Connection", self.test_connection),
            ("Bandwidth Monitor", lambda: self.monitor_bandwidth(10))
        ]
        
        for i, (text, command) in enumerate(action_buttons):
            btn = ttk.Button(actions_frame, text=text, command=command)
            btn.grid(row=0, column=i, padx=5, pady=5)
        
        # Recent activity frame
        activity_frame = ttk.LabelFrame(self.dashboard_tab, text="Recent Activity")
        activity_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        self.activity_text = scrolledtext.ScrolledText(activity_frame, height=10, 
                                                     bg='#002200', fg='#00FF00',
                                                     insertbackground='#00FF00')
        self.activity_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.activity_text.config(state=tk.DISABLED)
    
    def setup_monitoring_tab(self):
        """Setup the monitoring tab"""
        # IP management frame
        ip_frame = ttk.LabelFrame(self.monitoring_tab, text="IP Management")
        ip_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Label(ip_frame, text="IP Address:").grid(row=0, column=0, padx=5, pady=5)
        self.ip_entry = ttk.Entry(ip_frame, width=20)
        self.ip_entry.grid(row=0, column=1, padx=5, pady=5)
        
        ttk.Button(ip_frame, text="Add IP", command=self.add_ip_gui).grid(row=0, column=2, padx=5, pady=5)
        ttk.Button(ip_frame, text="Remove IP", command=self.remove_ip_gui).grid(row=0, column=3, padx=5, pady=5)
        ttk.Button(ip_frame, text="Ping IP", command=self.ping_ip_gui).grid(row=0, column=4, padx=5, pady=5)
        
        # Monitored IPs list
        list_frame = ttk.LabelFrame(self.monitoring_tab, text="Monitored IPs")
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        self.monitored_listbox = tk.Listbox(list_frame, bg='#002200', fg='#00FF00',
                                          selectbackground='#006600')
        self.monitored_listbox.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Control buttons
        control_frame = ttk.Frame(self.monitoring_tab)
        control_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Button(control_frame, text="Start Monitoring Selected", 
                  command=self.start_monitoring_selected).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Stop Monitoring", 
                  command=self.stop_monitoring).pack(side=tk.LEFT, padx=5)
    
    def setup_scanning_tab(self):
        """Setup the scanning tab"""
        # Scan target frame
        target_frame = ttk.LabelFrame(self.scanning_tab, text="Scan Target")
        target_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Label(target_frame, text="Target IP/Hostname:").grid(row=0, column=0, padx=5, pady=5)
        self.scan_target_entry = ttk.Entry(target_frame, width=20)
        self.scan_target_entry.grid(row=0, column=1, padx=5, pady=5)
        
        # Scan type frame
        type_frame = ttk.Frame(self.scanning_tab)
        type_frame.pack(fill=tk.X, padx=10, pady=5)
        
        self.scan_type = tk.StringVar(value="quick")
        ttk.Radiobutton(type_frame, text="Quick Scan (1-1000)", 
                       variable=self.scan_type, value="quick").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(type_frame, text="Deep Scan (1-65535)", 
                       variable=self.scan_type, value="deep").pack(side=tk.LEFT, padx=5)
        
        # Scan buttons
        button_frame = ttk.Frame(self.scanning_tab)
        button_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Button(button_frame, text="Port Scan", 
                  command=self.start_port_scan).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="DNS Lookup", 
                  command=self.dns_lookup_gui).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="WHOIS Lookup", 
                  command=self.whois_lookup_gui).pack(side=tk.LEFT, padx=5)
        
        # Results frame
        results_frame = ttk.LabelFrame(self.scanning_tab, text="Scan Results")
        results_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        self.scan_results_text = scrolledtext.ScrolledText(results_frame, 
                                                         bg='#002200', fg='#00FF00',
                                                         insertbackground='#00FF00')
        self.scan_results_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.scan_results_text.config(state=tk.DISABLED)
    
    def setup_traffic_tab(self):
        """Setup the traffic generation tab"""
        # Target selection frame
        target_frame = ttk.LabelFrame(self.traffic_tab, text="Traffic Target")
        target_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Label(target_frame, text="Target IP:").grid(row=0, column=0, padx=5, pady=5)
        self.traffic_ip_entry = ttk.Entry(target_frame, width=20)
        self.traffic_ip_entry.grid(row=0, column=1, padx=5, pady=5)
        
        ttk.Label(target_frame, text="or use monitored IPs").grid(row=0, column=2, padx=5, pady=5)
        self.use_monitored_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(target_frame, variable=self.use_monitored_var, 
                       command=self.toggle_traffic_target).pack(side=tk.LEFT, padx=5)
        
        # Traffic type frame
        type_frame = ttk.LabelFrame(self.traffic_tab, text="Traffic Type")
        type_frame.pack(fill=tk.X, padx=10, pady=5)
        
        self.traffic_type = tk.StringVar(value="tcp")
        traffic_types = [("TCP", "tcp"), ("UDP", "udp"), ("HTTP", "http"), ("HTTPS", "https")]
        
        for i, (text, value) in enumerate(traffic_types):
            ttk.Radiobutton(type_frame, text=text, variable=self.traffic_type, 
                           value=value).grid(row=0, column=i, padx=5, pady=5)
        
        # Duration frame
        duration_frame = ttk.Frame(self.traffic_tab)
        duration_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Label(duration_frame, text="Duration (seconds):").pack(side=tk.LEFT, padx=5)
        self.duration_entry = ttk.Entry(duration_frame, width=10)
        self.duration_entry.insert(0, "30")
        self.duration_entry.pack(side=tk.LEFT, padx=5)
        
        # Control buttons
        control_frame = ttk.Frame(self.traffic_tab)
        control_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Button(control_frame, text="Start Traffic Generation", 
                  command=self.start_traffic_gui).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Stop Traffic", 
                  command=self.stop_traffic).pack(side=tk.LEFT, padx=5)
        
        # Status frame
        status_frame = ttk.LabelFrame(self.traffic_tab, text="Traffic Status")
        status_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        self.traffic_status_text = scrolledtext.ScrolledText(status_frame, 
                                                           bg='#002200', fg='#00FF00',
                                                           insertbackground='#00FF00')
        self.traffic_status_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.traffic_status_text.config(state=tk.DISABLED)
    
    def setup_diagnostics_tab(self):
        """Setup the diagnostics tab"""
        # Diagnostic tools frame
        tools_frame = ttk.LabelFrame(self.diagnostics_tab, text="Diagnostic Tools")
        tools_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Label(tools_frame, text="Target:").grid(row=0, column=0, padx=5, pady=5)
        self.diagnostic_target_entry = ttk.Entry(tools_frame, width=20)
        self.diagnostic_target_entry.grid(row=0, column=1, padx=5, pady=5)
        
        # Buttons for various diagnostics
        buttons_frame = ttk.Frame(tools_frame)
        buttons_frame.grid(row=1, column=0, columnspan=2, pady=5)
        
        diagnostic_buttons = [
            ("Traceroute", self.traceroute_gui),
            ("TCP Traceroute", lambda: self.traceroute_gui("tcp")),
            ("UDP Traceroute", lambda: self.traceroute_gui("udp")),
            ("Reverse DNS", self.reverse_dns_gui)
        ]
        
        for i, (text, command) in enumerate(diagnostic_buttons):
            ttk.Button(buttons_frame, text=text, command=command).grid(row=0, column=i, padx=2)
        
        # Results frame
        results_frame = ttk.LabelFrame(self.diagnostics_tab, text="Diagnostic Results")
        results_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        self.diagnostic_results_text = scrolledtext.ScrolledText(results_frame, 
                                                               bg='#002200', fg='#00FF00',
                                                               insertbackground='#00FF00')
        self.diagnostic_results_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.diagnostic_results_text.config(state=tk.DISABLED)
    
    def setup_visualization_tab(self):
        """Setup the visualization tab"""
        if not MATPLOTLIB_AVAILABLE:
            label = ttk.Label(self.visualization_tab, 
                             text="Matplotlib not available. Visualization features disabled.")
            label.pack(pady=20)
            return
            
        # Control frame
        control_frame = ttk.Frame(self.visualization_tab)
        control_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Button(control_frame, text="Traffic Graph", 
                  command=self.show_traffic_graph).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Response Time Graph", 
                  command=self.show_response_time_graph).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Port Scan Results", 
                  command=self.show_port_scan_graph).pack(side=tk.LEFT, padx=5)
        
        # Canvas for matplotlib figures
        self.viz_frame = ttk.Frame(self.visualization_tab)
        self.viz_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Placeholder for graphs
        self.viz_label = ttk.Label(self.viz_frame, text="Select a visualization option above")
        self.viz_label.pack(expand=True)
    
    def setup_log_tab(self):
        """Setup the log tab"""
        # Log display
        log_frame = ttk.Frame(self.log_tab)
        log_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        self.log_text = scrolledtext.ScrolledText(log_frame, 
                                                bg='#002200', fg='#00FF00',
                                                insertbackground='#00FF00')
        self.log_text.pack(fill=tk.BOTH, expand=True)
        self.log_text.config(state=tk.DISABLED)
        
        # Control buttons
        button_frame = ttk.Frame(self.log_tab)
        button_frame.pack(fill=tk.X, padx=10, pady=5)
        
        ttk.Button(button_frame, text="Refresh Log", 
                  command=self.refresh_log).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Clear Log", 
                  command=self.clear_log).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Export Log", 
                  command=self.export_log).pack(side=tk.LEFT, padx=5)
    
    def toggle_traffic_target(self):
        """Toggle between specific IP and monitored IPs for traffic generation"""
        if self.use_monitored_var.get():
            self.traffic_ip_entry.config(state=tk.DISABLED)
        else:
            self.traffic_ip_entry.config(state=tk.NORMAL)
    
    def add_ip_gui(self):
        """Add IP from GUI"""
        ip = self.ip_entry.get().strip()
        if not ip:
            messagebox.showerror("Error", "Please enter an IP address")
            return
            
        if self.validate_ip(ip) or self.validate_ipv6(ip):
            self.ip_list.add(ip)
            self.monitored_listbox.insert(tk.END, ip)
            self.ip_entry.delete(0, tk.END)
            self.update_status(f"Added IP: {ip}")
            self.log_operation("ADD_IP", f"IP: {ip}")
        else:
            messagebox.showerror("Error", "Invalid IP address format")
    
    def remove_ip_gui(self):
        """Remove IP from GUI"""
        selection = self.monitored_listbox.curselection()
        if not selection:
            messagebox.showerror("Error", "Please select an IP to remove")
            return
            
        ip = self.monitored_listbox.get(selection[0])
        if ip in self.ip_list:
            self.ip_list.remove(ip)
            self.monitored_listbox.delete(selection[0])
            self.update_status(f"Removed IP: {ip}")
            self.log_operation("REMOVE_IP", f"IP: {ip}")
    
    def ping_ip_gui(self):
        """Ping IP from GUI"""
        ip = self.ip_entry.get().strip()
        if not ip:
            messagebox.showerror("Error", "Please enter an IP address")
            return
            
        if not (self.validate_ip(ip) or self.validate_ipv6(ip)):
            messagebox.showerror("Error", "Invalid IP address format")
            return
            
        # Run ping in background thread to avoid GUI freeze
        threading.Thread(target=self._ping_ip_gui_thread, args=(ip,), daemon=True).start()
    
    def _ping_ip_gui_thread(self, ip):
        """Thread for GUI ping operation"""
        if self.validate_ipv6(ip):
            success, response_time = self.ping_ip6(ip)
        else:
            success, response_time = self.ping_ip(ip)
            
        status = "Reachable" if success else "Unreachable"
        message = f"Ping {ip}: {status} ({response_time}ms)"
        
        self.update_status(message)
        self.log_operation("PING", f"IP: {ip}, Status: {status}, Time: {response_time}ms")
        
        # Show result in messagebox
        self.root.after(0, lambda: messagebox.showinfo("Ping Result", message))
    
    def start_monitoring_gui(self):
        """Start monitoring from GUI"""
        selection = self.monitored_listbox.curselection()
        if not selection:
            messagebox.showerror("Error", "Please select an IP to monitor")
            return
            
        ip = self.monitored_listbox.get(selection[0])
        self.start_monitoring_ip(ip)
    
    def start_monitoring_selected(self):
        """Start monitoring selected IPs"""
        selection = self.monitored_listbox.curselection()
        if not selection:
            messagebox.showerror("Error", "Please select IPs to monitor")
            return
            
        for index in selection:
            ip = self.monitored_listbox.get(index)
            self.start_monitoring_ip(ip)
    
    def start_port_scan(self):
        """Start port scan from GUI"""
        target = self.scan_target_entry.get().strip()
        if not target:
            messagebox.showerror("Error", "Please enter a target IP or hostname")
            return
            
        # Resolve hostname if needed
        if not self.validate_ip(target) and not self.validate_ipv6(target):
            ip = self.resolve_hostname(target)
            if not ip:
                messagebox.showerror("Error", f"Could not resolve hostname: {target}")
                return
            target = ip
            
        deep = self.scan_type.get() == "deep"
        
        # Run scan in background thread
        threading.Thread(target=self._port_scan_thread, args=(target, deep), daemon=True).start()
    
    def _port_scan_thread(self, target, deep):
        """Thread for port scan operation"""
        self.update_scan_results(f"Starting {'deep ' if deep else ''}port scan on {target}\n")
        
        port_range = range(1, 65536) if deep else range(1, 1001)
        open_ports = []
        start_time = time.time()
        
        # Use thread pool for faster scanning
        with ThreadPoolExecutor(max_workers=100) as executor:
            futures = {executor.submit(self._check_port, target, port): port for port in port_range}
            
            for i, future in enumerate(futures):
                try:
                    port, is_open = future.result(timeout=self.config['scan_timeout'])
                    if is_open:
                        open_ports.append(port)
                        self.update_scan_results(f"Port {port} is open\n")
                        
                    # Update progress every 100 ports
                    if (i + 1) % 100 == 0:
                        elapsed = time.time() - start_time
                        self.update_scan_results(f"Scanned {i+1} ports | Elapsed: {elapsed:.1f}s | Open ports: {len(open_ports)}\n")
                        
                except Exception as e:
                    pass
                    
        elapsed = time.time() - start_time
        self.update_scan_results(f"Scan completed in {elapsed:.1f} seconds\n")
        self.update_scan_results(f"Open ports: {sorted(open_ports)}\n")
        
        self.log_operation("PORT_SCAN_COMPLETE", 
                          f"Target: {target}, Open ports: {len(open_ports)}, Time: {elapsed:.1f}s")
    
    def dns_lookup_gui(self):
        """DNS lookup from GUI"""
        domain = self.scan_target_entry.get().strip()
        if not domain:
            messagebox.showerror("Error", "Please enter a domain name")
            return
            
        # Run DNS lookup in background thread
        threading.Thread(target=self._dns_lookup_thread, args=(domain,), daemon=True).start()
    
    def _dns_lookup_thread(self, domain):
        """Thread for DNS lookup operation"""
        self.update_scan_results(f"Performing DNS lookup for {domain}\n")
        self.dns_lookup(domain)
    
    def whois_lookup_gui(self):
        """WHOIS lookup from GUI"""
        query = self.scan_target_entry.get().strip()
        if not query:
            messagebox.showerror("Error", "Please enter a domain or IP address")
            return
            
        # Run WHOIS lookup in background thread
        threading.Thread(target=self._whois_lookup_thread, args=(query,), daemon=True).start()
    
    def _whois_lookup_thread(self, query):
        """Thread for WHOIS lookup operation"""
        self.update_scan_results(f"Performing WHOIS lookup for {query}\n")
        self.whois_lookup(query)
    
    def start_traffic_gui(self):
        """Start traffic generation from GUI"""
        if self.use_monitored_var.get():
            # Use monitored IPs
            if not self.monitored_ips:
                messagebox.showerror("Error", "No IPs being monitored")
                return
                
            traffic_type = self.traffic_type.get()
            try:
                duration = int(self.duration_entry.get())
                if duration <= 0:
                    raise ValueError
            except ValueError:
                messagebox.showerror("Error", "Duration must be a positive integer")
                return
                
            self.generate_traffic_to_monitored(traffic_type, duration)
        else:
            # Use specific IP
            ip = self.traffic_ip_entry.get().strip()
            if not ip:
                messagebox.showerror("Error", "Please enter a target IP")
                return
                
            if not (self.validate_ip(ip) or self.validate_ipv6(ip)):
                messagebox.showerror("Error", "Invalid IP address format")
                return
                
            traffic_type = self.traffic_type.get()
            try:
                duration = int(self.duration_entry.get())
                if duration <= 0:
                    raise ValueError
            except ValueError:
                messagebox.showerror("Error", "Duration must be a positive integer")
                return
                
            self.generate_traffic(ip, traffic_type, duration)
    
    def stop_traffic(self):
        """Stop traffic generation from GUI"""
        self.stop_monitoring()
        self.update_traffic_status("Traffic generation stopped\n")
    
    def traceroute_gui(self, protocol="icmp"):
        """Traceroute from GUI"""
        target = self.diagnostic_target_entry.get().strip()
        if not target:
            messagebox.showerror("Error", "Please enter a target IP or hostname")
            return
            
        # Resolve hostname if needed
        if not self.validate_ip(target) and not self.validate_ipv6(target):
            ip = self.resolve_hostname(target)
            if not ip:
                messagebox.showerror("Error", f"Could not resolve hostname: {target}")
                return
            target = ip
            
        # Run traceroute in background thread
        threading.Thread(target=self._traceroute_thread, args=(target, protocol), daemon=True).start()
    
    def _traceroute_thread(self, target, protocol):
        """Thread for traceroute operation"""
        self.update_diagnostic_results(f"Starting {protocol.upper()} traceroute to {target}\n")
        self.traceroute(target, protocol)
    
    def reverse_dns_gui(self):
        """Reverse DNS from GUI"""
        ip = self.diagnostic_target_entry.get().strip()
        if not ip:
            messagebox.showerror("Error", "Please enter an IP address")
            return
            
        if not self.validate_ip(ip):
            messagebox.showerror("Error", "Invalid IP address format")
            return
            
        # Run reverse DNS in background thread
        threading.Thread(target=self._reverse_dns_thread, args=(ip,), daemon=True).start()
    
    def _reverse_dns_thread(self, ip):
        """Thread for reverse DNS operation"""
        self.update_diagnostic_results(f"Performing reverse DNS lookup for {ip}\n")
        self.reverse_dns(ip)
    
    def show_traffic_graph(self):
        """Show traffic generation graph"""
        if not MATPLOTLIB_AVAILABLE:
            messagebox.showerror("Error", "Matplotlib not available")
            return
            
        if not self.packet_count_history:
            messagebox.showinfo("Info", "No traffic data available")
            return
            
        # Clear previous visualization
        for widget in self.viz_frame.winfo_children():
            widget.destroy()
            
        # Create figure
        fig = Figure(figsize=(8, 6), dpi=100)
        ax = fig.add_subplot(111)
        
        # Prepare data
        timestamps = [t for t, _ in self.packet_count_history]
        packets = [p for _, p in self.packet_count_history]
        
        # Convert timestamps to relative time
        start_time = timestamps[0]
        relative_times = [t - start_time for t in timestamps]
        
        # Plot data
        ax.plot(relative_times, packets, 'g-', linewidth=2)
        ax.set_xlabel('Time (seconds)')
        ax.set_ylabel('Packets Sent')
        ax.set_title('Traffic Generation Over Time')
        ax.grid(True, alpha=0.3)
        
        # Embed in tkinter
        canvas = FigureCanvasTkAgg(fig, self.viz_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
    
    def show_response_time_graph(self):
        """Show response time graph"""
        if not MATPLOTLIB_AVAILABLE:
            messagebox.showerror("Error", "Matplotlib not available")
            return
            
        if not self.response_time_history:
            messagebox.showinfo("Info", "No response time data available")
            return
            
        # Clear previous visualization
        for widget in self.viz_frame.winfo_children():
            widget.destroy()
            
        # Create figure
        fig = Figure(figsize=(8, 6), dpi=100)
        ax = fig.add_subplot(111)
        
        # Prepare data
        timestamps = [t for t, _ in self.response_time_history]
        response_times = [r for _, r in self.response_time_history]
        
        # Convert timestamps to relative time
        start_time = timestamps[0]
        relative_times = [t - start_time for t in timestamps]
        
        # Plot data
        ax.plot(relative_times, response_times, 'b-', linewidth=2)
        ax.set_xlabel('Time (seconds)')
        ax.set_ylabel('Response Time (ms)')
        ax.set_title('Network Response Time Over Time')
        ax.grid(True, alpha=0.3)
        
        # Embed in tkinter
        canvas = FigureCanvasTkAgg(fig, self.viz_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
    
    def show_port_scan_graph(self):
        """Show port scan results as bar chart"""
        if not MATPLOTLIB_AVAILABLE:
            messagebox.showerror("Error", "Matplotlib not available")
            return
            
        # This is a placeholder - in a real implementation, you would use actual scan results
        messagebox.showinfo("Info", "Port scan visualization would show here with actual scan data")
    
    def refresh_dashboard(self):
        """Refresh dashboard data"""
        self.stats_vars['monitored_ips'].set(str(len(self.monitored_ips)))
        self.stats_vars['traffic_active'].set("Yes" if self.traffic_generation else "No")
        self.stats_vars['log_entries'].set(str(len(self.operation_log)))
        
        # Update activity log
        self.activity_text.config(state=tk.NORMAL)
        self.activity_text.delete(1.0, tk.END)
        for entry in self.operation_log[-10:]:
            self.activity_text.insert(tk.END, entry + "\n")
        self.activity_text.config(state=tk.DISABLED)
        
        self.update_status("Dashboard refreshed")
    
    def refresh_log(self):
        """Refresh log display"""
        self.log_text.config(state=tk.NORMAL)
        self.log_text.delete(1.0, tk.END)
        for entry in self.operation_log:
            self.log_text.insert(tk.END, entry + "\n")
        self.log_text.config(state=tk.DISABLED)
        self.log_text.see(tk.END)
        
        self.update_status("Log refreshed")
    
    def clear_log(self):
        """Clear the log"""
        self.operation_log.clear()
        self.refresh_log()
        self.update_status("Log cleared")
    
    def export_log(self):
        """Export log to file"""
        filename = filedialog.asksaveasfilename(
            defaultextension=".log",
            filetypes=[("Log files", "*.log"), ("Text files", "*.txt"), ("All files", "*.*")]
        )
        if filename:
            try:
                with open(filename, 'w') as f:
                    for entry in self.operation_log:
                        f.write(entry + "\n")
                self.update_status(f"Log exported to {filename}")
            except Exception as e:
                messagebox.showerror("Error", f"Failed to export log: {e}")
    
    def save_log(self):
        """Save log to file (menu command)"""
        self.export_log()
    
    def show_network_info(self):
        """Show network information dialog"""
        network_info = self.get_network_info()
        if not network_info:
            messagebox.showinfo("Network Info", "Could not retrieve network information")
            return
            
        info_text = "Network Interface Information:\n\n"
        for interface, info in network_info.items():
            info_text += f"Interface: {interface}\n"
            for key, value in info.items():
                info_text += f"  {key}: {value}\n"
            info_text += "\n"
            
        # Show in a dialog
        dialog = tk.Toplevel(self.root)
        dialog.title("Network Information")
        dialog.geometry("500x400")
        dialog.configure(bg='#003300')
        
        text = scrolledtext.ScrolledText(dialog, bg='#002200', fg='#00FF00')
        text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        text.insert(tk.END, info_text)
        text.config(state=tk.DISABLED)
        
        ttk.Button(dialog, text="Close", command=dialog.destroy).pack(pady=10)
    
    def show_telegram_config(self):
        """Show Telegram configuration dialog"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Telegram Configuration")
        dialog.geometry("400x200")
        dialog.configure(bg='#003300')
        
        ttk.Label(dialog, text="Telegram Bot Token:").pack(pady=(20, 5))
        token_entry = ttk.Entry(dialog, width=40)
        token_entry.insert(0, self.config['telegram_token'] or "")
        token_entry.pack(pady=5)
        
        ttk.Label(dialog, text="Chat ID:").pack(pady=(10, 5))
        chat_id_entry = ttk.Entry(dialog, width=40)
        chat_id_entry.insert(0, self.config['telegram_chat_id'] or "")
        chat_id_entry.pack(pady=5)
        
        def save_config():
            self.config['telegram_token'] = token_entry.get().strip() or None
            self.config['telegram_chat_id'] = chat_id_entry.get().strip() or None
            self.update_status("Telegram configuration saved")
            dialog.destroy()
        
        ttk.Button(dialog, text="Save", command=save_config).pack(pady=20)
    
    def show_interface_settings(self):
        """Show interface settings dialog"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Interface Settings")
        dialog.geometry("400x300")
        dialog.configure(bg='#003300')
        
        ttk.Label(dialog, text="Network Interface:").pack(pady=(20, 5))
        interface_var = tk.StringVar(value=self.config['network_interface'])
        interface_combo = ttk.Combobox(dialog, textvariable=interface_var, width=30)
        
        # Get available interfaces
        try:
            interfaces = netifaces.interfaces()
            interface_combo['values'] = interfaces
        except:
            interface_combo['values'] = [self.config['network_interface']]
            
        interface_combo.pack(pady=5)
        
        ttk.Label(dialog, text="Ping Timeout (seconds):").pack(pady=(10, 5))
        timeout_var = tk.StringVar(value=str(self.config['ping_timeout']))
        timeout_entry = ttk.Entry(dialog, textvariable=timeout_var, width=10)
        timeout_entry.pack(pady=5)
        
        ttk.Label(dialog, text="Scan Timeout (seconds):").pack(pady=(10, 5))
        scan_timeout_var = tk.StringVar(value=str(self.config['scan_timeout']))
        scan_timeout_entry = ttk.Entry(dialog, textvariable=scan_timeout_var, width=10)
        scan_timeout_entry.pack(pady=5)
        
        def save_settings():
            try:
                self.config['network_interface'] = interface_var.get()
                self.config['ping_timeout'] = float(timeout_var.get())
                self.config['scan_timeout'] = float(scan_timeout_var.get())
                self.update_status("Interface settings saved")
                dialog.destroy()
            except ValueError:
                messagebox.showerror("Error", "Please enter valid numeric values for timeouts")
        
        ttk.Button(dialog, text="Save", command=save_settings).pack(pady=20)
    
    def update_status(self, message):
        """Update status bar"""
        self.status_var.set(message)
        self.log_operation("STATUS", message)
    
    def update_scan_results(self, message):
        """Update scan results text area"""
        self.scan_results_text.config(state=tk.NORMAL)
        self.scan_results_text.insert(tk.END, message)
        self.scan_results_text.see(tk.END)
        self.scan_results_text.config(state=tk.DISABLED)
    
    def update_traffic_status(self, message):
        """Update traffic status text area"""
        self.traffic_status_text.config(state=tk.NORMAL)
        self.traffic_status_text.insert(tk.END, message)
        self.traffic_status_text.see(tk.END)
        self.traffic_status_text.config(state=tk.DISABLED)
    
    def update_diagnostic_results(self, message):
        """Update diagnostic results text area"""
        self.diagnostic_results_text.config(state=tk.NORMAL)
        self.diagnostic_results_text.insert(tk.END, message)
        self.diagnostic_results_text.see(tk.END)
        self.diagnostic_results_text.config(state=tk.DISABLED)
    
    def get_default_interface(self):
        """Get the default network interface"""
        try:
            gateways = netifaces.gateways()
            default_interface = gateways['default'][netifaces.AF_INET][1]
            return default_interface
        except:
            return "eth0"  # Fallback default
            
    def get_network_info(self):
        """Get detailed network information"""
        try:
            interfaces = netifaces.interfaces()
            network_info = {}
            
            for interface in interfaces:
                addrs = netifaces.ifaddresses(interface)
                if netifaces.AF_INET in addrs:
                    network_info[interface] = {
                        'ipv4': addrs[netifaces.AF_INET][0]['addr'],
                        'netmask': addrs[netifaces.AF_INET][0]['netmask'],
                        'broadcast': addrs[netifaces.AF_INET][0].get('broadcast', 'N/A')
                    }
                if netifaces.AF_INET6 in addrs:
                    if interface not in network_info:
                        network_info[interface] = {}
                    network_info[interface]['ipv6'] = addrs[netifaces.AF_INET6][0]['addr']
                    
            return network_info
        except Exception as e:
            print(f"{Colors.RED}Error getting network info: {e}{Colors.END}")
            return {}
            
    def log_operation(self, operation: str, details: str = ""):
        """Log operations with timestamp"""
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        log_entry = f"[{timestamp}] {operation} {details}"
        self.operation_log.append(log_entry)
        
        # Also write to log file
        with open(self.log_file, "a") as f:
            f.write(log_entry + "\n")
            
        # Update GUI if needed
        if self.use_gui and hasattr(self, 'log_text'):
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, log_entry + "\n")
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
            
        return log_entry

    def print_banner(self):
        """Display the tool banner"""
        print(BANNER)
        print(f"{Colors.GREEN}Type 'help' for available commands{Colors.END}\n")

    def print_help(self):
        """Display help information"""
        help_text = f"""
{Colors.BOLD}{Colors.LIGHT_GREEN}Available Commands:{Colors.END}

{Colors.GREEN}General Commands:{Colors.END}
  {Colors.CYAN}help{Colors.END} - Show this help message
  {Colors.CYAN}exit{Colors.END} - Exit the program
  {Colors.CYAN}clear{Colors.END} - Clear the screen
  {Colors.CYAN}view{Colors.END} - View operation log
  {Colors.CYAN}status{Colors.END} - Show current tool status
  {Colors.CYAN}network info{Colors.END} - Show network interface information

{Colors.GREEN}IP Management:{Colors.END}
  {Colors.CYAN}add ip <IP>{Colors.END} - Add IP to monitoring list
  {Colors.CYAN}remove ip <IP>{Colors.END} - Remove IP from monitoring list
  {Colors.CYAN}ping ip <IP>{Colors.END} - Ping an IP address
  {Colors.CYAN}ping ip6 <IPv6>{Colors.END} - Ping an IPv6 address
  {Colors.CYAN}ping hostname <HOSTNAME>{Colors.END} - Ping a hostname

{Colors.GREEN}Monitoring:{Colors.END}
  {Colors.CYAN}start monitoring ip <IP>{Colors.END} - Start monitoring an IP
  {Colors.CYAN}stop{Colors.END} - Stop all monitoring and traffic generation
  {Colors.CYAN}bandwidth{Colors.END} - Monitor bandwidth usage

{Colors.GREEN}Network Diagnostics:{Colors.END}
  {Colors.CYAN}traceroute ip <IP>{Colors.END} - Perform traceroute to IP
  {Colors.CYAN}tcptraceroute ip <IP>{Colors.END} - Perform TCP traceroute
  {Colors.CYAN}udptraceroute ip <IP>{Colors.END} - Perform UDP traceroute
  {Colors.CYAN}test connection{Colors.END} - Test network connectivity
  {Colors.CYAN}scan ip <IP>{Colors.END} - Basic port scan
  {Colors.CYAN}deep scan ip <IP>{Colors.END} - Deep port scan (1-65535)
  {Colors.CYAN}dns lookup <DOMAIN>{Colors.END} - DNS lookup for a domain
  {Colors.CYAN}reverse dns <IP>{Colors.END} - Reverse DNS lookup
  {Colors.CYAN}whois <IP/DOMAIN>{Colors.END} - WHOIS lookup

{Colors.GREEN}Traffic Generation:{Colors.END}
  {Colors.CYAN}generate traffic <IP> <TYPE> <DURATION>{Colors.END} - Generate network traffic to specific IP
  {Colors.CYAN}generate traffic tcp <DURATION>{Colors.END} - Generate TCP traffic to monitored IPs
  {Colors.CYAN}generate traffic udp <DURATION>{Colors.END} - Generate UDP traffic to monitored IPs
  {Colors.CYAN}generate traffic http <DURATION>{Colors.END} - Generate HTTP traffic to monitored IPs
  {Colors.CYAN}generate traffic https <DURATION>{Colors.END} - Generate HTTPS traffic to monitored IPs

{Colors.GREEN}Telegram Integration:{Colors.END}
  {Colors.CYAN}config telegram token <TOKEN>{Colors.END} - Set Telegram bot token
  {Colors.CYAN}config telegram chat_id <ID>{Colors.END} - Set Telegram chat ID
  {Colors.CYAN}test message{Colors.END} - Send test message to Telegram
  {Colors.CYAN}export data{Colors.END} - Export data to Telegram

{Colors.YELLOW}Examples:{Colors.END}
  ping ip 192.168.1.1
  add ip 10.0.0.5
  generate traffic 192.168.1.1 tcp 60
  generate traffic 8.8.8.8 https 30
  deep scan ip 192.168.1.100
  dns lookup example.com
  bandwidth
        """
        print(help_text)

    def validate_ip(self, ip: str) -> bool:
        """Validate IP address format"""
        try:
            ipaddress.ip_address(ip)
            return True
        except ValueError:
            return False

    def validate_ipv6(self, ip: str) -> bool:
        """Validate IPv6 address format"""
        try:
            ipaddress.IPv6Address(ip)
            return True
        except ValueError:
            return False

    def resolve_hostname(self, hostname: str) -> Optional[str]:
        """Resolve a hostname to an IP address"""
        try:
            # Check cache first
            if hostname in self.hostname_cache:
                if time.time() - self.hostname_cache[hostname]['timestamp'] < 300:  # 5 minute cache
                    return self.hostname_cache[hostname]['ip']
            
            # Resolve using DNS
            result = socket.getaddrinfo(hostname, None)
            ip = result[0][4][0]
            
            # Update cache
            self.hostname_cache[hostname] = {
                'ip': ip,
                'timestamp': time.time()
            }
            
            return ip
        except socket.gaierror:
            return None

    def ping_ip(self, ip: str) -> Tuple[bool, float]:
        """Ping an IP address and return success status and response time"""
        try:
            # Use system ping command for cross-platform compatibility
            param = "-n" if os.name == "nt" else "-c"
            command = ["ping", param, "1", ip]
            result = subprocess.run(
                command, 
                capture_output=True, 
                text=True, 
                timeout=self.config['ping_timeout']
            )
            
            if result.returncode == 0:
                # Extract time from ping output
                time_match = re.search(r"time=([\d.]+) ms", result.stdout)
                response_time = float(time_match.group(1)) if time_match else 0
                return True, response_time
            else:
                return False, 0
        except (subprocess.TimeoutExpired, Exception):
            return False, 0

    def ping_ip6(self, ip: str) -> Tuple[bool, float]:
        """Ping an IPv6 address"""
        try:
            param = "-n" if os.name == "nt" else "-c"
            command = ["ping6", param, "1", ip]
            result = subprocess.run(
                command, 
                capture_output=True, 
                text=True, 
                timeout=self.config['ping_timeout']
            )
            
            if result.returncode == 0:
                time_match = re.search(r"time=([\d.]+) ms", result.stdout)
                response_time = float(time_match.group(1)) if time_match else 0
                return True, response_time
            else:
                return False, 0
        except (subprocess.TimeoutExpired, Exception):
            return False, 0

    def start_monitoring_ip(self, ip: str):
        """Start monitoring an IP address"""
        if not self.validate_ip(ip) and not self.validate_ipv6(ip):
            if self.use_gui:
                messagebox.showerror("Error", "Invalid IP address format")
            else:
                print(f"{Colors.RED}Invalid IP address format{Colors.END}")
            return
            
        with self.lock:
            self.monitored_ips.add(ip)
            
        if self.use_gui:
            self.update_status(f"Started monitoring IP: {ip}")
            self.update_traffic_status(f"Started monitoring IP: {ip}\n")
        else:
            print(f"{Colors.GREEN}Started monitoring IP: {ip}{Colors.END}")
            
        self.log_operation("START_MONITORING", f"IP: {ip}")
        
        # Start monitoring in background thread
        monitor_thread = threading.Thread(
            target=self._monitor_ip, 
            args=(ip,),
            daemon=True
        )
        monitor_thread.start()

    def _monitor_ip(self, ip: str):
        """Background IP monitoring function"""
        while ip in self.monitored_ips:
            if self.validate_ipv6(ip):
                success, response_time = self.ping_ip6(ip)
            else:
                success, response_time = self.ping_ip(ip)
                
            status = f"{Colors.GREEN}UP{Colors.END}" if success else f"{Colors.RED}DOWN{Colors.END}"
            timestamp = datetime.now().strftime("%H:%M:%S")
            
            if success:
                message = f"[{timestamp}] {ip} is {status} - Response time: {response_time}ms"
                # Store for graphing
                self.response_time_history.append((time.time(), response_time))
            else:
                message = f"[{timestamp}] {ip} is {status}"
                
            if self.use_gui:
                self.update_traffic_status(message + "\n")
            else:
                if success:
                    print(f"{Colors.DARK_GREEN}{message}{Colors.END}")
                else:
                    print(f"{Colors.RED}{message}{Colors.END}")
                    
            self.log_operation("MONITORING", message)
            time.sleep(5)  # Check every 5 seconds

    def stop_monitoring(self):
        """Stop all monitoring activities"""
        with self.lock:
            self.monitored_ips.clear()
            
        self.traffic_generation = False
        for thread in self.traffic_threads:
            if thread.is_alive():
                thread.join(timeout=1)
                
        self.traffic_threads.clear()
        
        if self.use_gui:
            self.update_status("All monitoring and traffic generation stopped")
            self.update_traffic_status("All monitoring and traffic generation stopped\n")
        else:
            print(f"{Colors.GREEN}All monitoring and traffic generation stopped{Colors.END}")
            
        self.log_operation("STOP_ALL", "Monitoring and traffic generation stopped")

    def generate_traffic(self, target_ip: str, traffic_type: str, duration: int):
        """Generate network traffic to specific IP of specified type and duration"""
        if not self.validate_ip(target_ip) and not self.validate_ipv6(target_ip):
            if self.use_gui:
                messagebox.showerror("Error", "Invalid target IP address format")
            else:
                print(f"{Colors.RED}Invalid target IP address format{Colors.END}")
            return
            
        if traffic_type.lower() not in ["tcp", "udp", "http", "https"]:
            if self.use_gui:
                messagebox.showerror("Error", "Traffic type must be 'tcp', 'udp', 'http', or 'https'")
            else:
                print(f"{Colors.RED}Traffic type must be 'tcp', 'udp', 'http', or 'https'{Colors.END}")
            return
            
        try:
            duration = int(duration)
            if duration <= 0:
                if self.use_gui:
                    messagebox.showerror("Error", "Duration must be a positive integer")
                else:
                    print(f"{Colors.RED}Duration must be a positive integer{Colors.END}")
                return
        except ValueError:
            if self.use_gui:
                messagebox.showerror("Error", "Duration must be a valid integer")
            else:
                print(f"{Colors.RED}Duration must be a valid integer{Colors.END}")
            return
            
        if self.use_gui:
            self.update_status(f"Starting {traffic_type.upper()} traffic generation to {target_ip} for {duration} seconds")
            self.update_traffic_status(f"Starting {traffic_type.upper()} traffic generation to {target_ip} for {duration} seconds\n")
        else:
            print(f"{Colors.GREEN}Starting {traffic_type.upper()} traffic generation to {target_ip} for {duration} seconds{Colors.END}")
            
        self.log_operation("GENERATE_TRAFFIC", f"Target: {target_ip}, Type: {traffic_type}, Duration: {duration}s")
        
        self.traffic_generation = True
        traffic_thread = threading.Thread(
            target=self._generate_traffic,
            args=(target_ip, traffic_type, duration),
            daemon=True
        )
        traffic_thread.start()
        self.traffic_threads.append(traffic_thread)

    def generate_traffic_to_monitored(self, traffic_type: str, duration: int):
        """Generate network traffic to all monitored IPs"""
        if not self.monitored_ips:
            if self.use_gui:
                messagebox.showerror("Error", "No IPs being monitored. Add IPs first.")
            else:
                print(f"{Colors.RED}No IPs being monitored. Add IPs first.{Colors.END}")
            return
            
        if self.use_gui:
            self.update_status(f"Starting {traffic_type.upper()} traffic generation to {len(self.monitored_ips)} monitored IPs for {duration} seconds")
            self.update_traffic_status(f"Starting {traffic_type.upper()} traffic generation to {len(self.monitored_ips)} monitored IPs for {duration} seconds\n")
        else:
            print(f"{Colors.GREEN}Starting {traffic_type.upper()} traffic generation to {len(self.monitored_ips)} monitored IPs for {duration} seconds{Colors.END}")
            
        self.log_operation("GENERATE_TRAFFIC_MONITORED", f"Type: {traffic_type}, Duration: {duration}s")
        
        self.traffic_generation = True
        for target_ip in self.monitored_ips:
            traffic_thread = threading.Thread(
                target=self._generate_traffic,
                args=(target_ip, traffic_type, duration),
                daemon=True
            )
            traffic_thread.start()
            self.traffic_threads.append(traffic_thread)

    def _generate_traffic(self, target_ip: str, traffic_type: str, duration: int):
        """Background traffic generation function"""
        end_time = time.time() + duration
        packet_count = 0
        
        if self.use_gui:
            self.update_traffic_status(f"Generating {traffic_type.upper()} traffic to {target_ip}\n")
        else:
            print(f"{Colors.GREEN}Generating {traffic_type.upper()} traffic to {target_ip}{Colors.END}")
        
        while time.time() < end_time and self.traffic_generation:
            try:
                if traffic_type.lower() == "tcp":
                    self._generate_tcp_traffic(target_ip)
                elif traffic_type.lower() == "udp":
                    self._generate_udp_traffic(target_ip)
                elif traffic_type.lower() == "http":
                    self._generate_http_traffic(target_ip)
                elif traffic_type.lower() == "https":
                    self._generate_https_traffic(target_ip)
                    
                packet_count += 1
                
                # Store for graphing
                self.packet_count_history.append((time.time(), packet_count))
                
                # Display progress every 100 packets
                if packet_count % 100 == 0:
                    elapsed = int(time.time() - (end_time - duration))
                    remaining = max(0, int(end_time - time.time()))
                    message = f"Generated {packet_count} packets to {target_ip} | Elapsed: {elapsed}s | Remaining: {remaining}s"
                    
                    if self.use_gui:
                        self.update_traffic_status(message + "\n")
                    else:
                        print(f"{Colors.DARK_GREEN}{message}{Colors.END}")
                    
            except Exception as e:
                error_msg = f"Error generating traffic to {target_ip}: {e}"
                if self.use_gui:
                    self.update_traffic_status(error_msg + "\n")
                else:
                    print(f"{Colors.RED}{error_msg}{Colors.END}")
                
            # Small delay to prevent complete system overload
            time.sleep(0.01)
            
        message = f"Traffic generation to {target_ip} completed. Total packets sent: {packet_count}"
        if self.use_gui:
            self.update_traffic_status(message + "\n")
        else:
            print(f"{Colors.GREEN}{message}{Colors.END}")
            
        self.log_operation("TRAFFIC_COMPLETED", f"Target: {target_ip}, Packets: {packet_count}, Type: {traffic_type}")

    def _generate_tcp_traffic(self, target_ip: str):
        """Generate TCP traffic to target IP"""
        try:
            # Create a TCP socket
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(0.5)
            
            # Try to connect to a random port
            port = random.randint(1024, 65535)
            sock.connect((target_ip, port))
            
            # Send some data
            sock.send(b"GET / HTTP/1.1\r\nHost: example.com\r\n\r\n")
            
            # Close the socket
            sock.close()
        except:
            # Most connections will fail, which is expected
            pass

    def _generate_udp_traffic(self, target_ip: str):
        """Generate UDP traffic to target IP"""
        try:
            # Create a UDP socket
            sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            
            # Send data to a random port
            port = random.randint(1024, 65535)
            sock.sendto(b"UDP Traffic Generation", (target_ip, port))
            
            # Close the socket
            sock.close()
        except:
            pass

    def _generate_http_traffic(self, target_ip: str):
        """Generate HTTP traffic to target IP"""
        try:
            # Create a TCP socket
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(0.5)
            
            # Connect to port 80
            sock.connect((target_ip, 80))
            
            # Generate realistic HTTP request
            user_agent = random.choice(self.config['http_user_agents'])
            target_path = random.choice(self.config['http_targets'])
            
            http_request = (
                f"GET {target_path} HTTP/1.1\r\n"
                f"Host: {target_ip}\r\n"
                f"User-Agent: {user_agent}\r\n"
                f"Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n"
                f"Accept-Language: en-US,en;q=0.5\r\n"
                f"Connection: keep-alive\r\n"
                f"Upgrade-Insecure-Requests: 1\r\n\r\n"
            )
            
            # Send HTTP request
            sock.send(http_request.encode())
            
            # Try to receive response (but don't wait too long)
            try:
                sock.recv(1024)
            except:
                pass
                
            # Close the socket
            sock.close()
        except:
            # Most connections will fail, which is expected
            pass

    def _generate_https_traffic(self, target_ip: str):
        """Generate HTTPS traffic to target IP"""
        try:
            # Create a TCP socket
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(0.5)
            
            # Connect to port 443
            sock.connect((target_ip, 443))
            
            # Send TLS Client Hello (simplified)
            # This is a basic representation - real TLS is more complex
            tls_header = bytes([
                0x16,  # Content Type: Handshake
                0x03, 0x01,  # Version: TLS 1.0
                0x00, 0x2f,  # Length: 47 bytes
            ])
            
            # Send the header
            sock.send(tls_header)
            
            # Close the socket
            sock.close()
        except:
            # Most connections will fail, which is expected
            pass

    def traceroute(self, ip: str, protocol: str = "icmp"):
        """Perform traceroute to an IP address"""
        if not self.validate_ip(ip) and not self.validate_ipv6(ip):
            if self.use_gui:
                messagebox.showerror("Error", "Invalid IP address format")
            else:
                print(f"{Colors.RED}Invalid IP address format{Colors.END}")
            return
            
        if self.use_gui:
            self.update_diagnostic_results(f"Starting {protocol.upper()} traceroute to {ip}\n")
        else:
            print(f"{Colors.GREEN}Starting {protocol.upper()} traceroute to {ip}{Colors.END}")
            
        self.log_operation("TRACEROUTE", f"IP: {ip}, Protocol: {protocol}")
        
        try:
            if protocol.lower() == "tcp":
                result = subprocess.run(
                    ["traceroute", "-T", "-w", "1", "-q", "1", ip],
                    capture_output=True,
                    text=True,
                    timeout=30
                )
            elif protocol.lower() == "udp":
                result = subprocess.run(
                    ["traceroute", "-U", "-w", "1", "-q", "1", ip],
                    capture_output=True,
                    text=True,
                    timeout=30
                )
            else:  # ICMP
                result = subprocess.run(
                    ["traceroute", "-w", "1", "-q", "1", ip],
                    capture_output=True,
                    text=True,
                    timeout=30
                )
                
            if self.use_gui:
                self.update_diagnostic_results(result.stdout)
                if result.stderr:
                    self.update_diagnostic_results(result.stderr)
            else:
                print(f"{Colors.CYAN}{result.stdout}{Colors.END}")
                if result.stderr:
                    print(f"{Colors.RED}{result.stderr}{Colors.END}")
                    
        except subprocess.TimeoutExpired:
            error_msg = "Traceroute timed out"
            if self.use_gui:
                self.update_diagnostic_results(error_msg + "\n")
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")
        except Exception as e:
            error_msg = f"Error performing traceroute: {e}"
            if self.use_gui:
                self.update_diagnostic_results(error_msg + "\n")
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")

    def scan_ports(self, ip: str, deep: bool = False):
        """Scan ports on a target IP"""
        if not self.validate_ip(ip) and not self.validate_ipv6(ip):
            if self.use_gui:
                messagebox.showerror("Error", "Invalid IP address format")
            else:
                print(f"{Colors.RED}Invalid IP address format{Colors.END}")
            return
            
        port_range = range(1, 65536) if deep else range(1, 1001)
        
        if self.use_gui:
            self.update_scan_results(f"Starting {'deep ' if deep else ''}port scan on {ip}\n")
            self.update_scan_results(f"Scanning {len(port_range)} ports...\n")
        else:
            print(f"{Colors.GREEN}Starting {'deep ' if deep else ''}port scan on {ip}{Colors.END}")
            print(f"{Colors.GREEN}Scanning {len(port_range)} ports...{Colors.END}")
        
        self.log_operation("PORT_SCAN", f"IP: {ip}, Deep: {deep}, Ports: {len(port_range)}")
        
        open_ports = []
        start_time = time.time()
        
        # Use thread pool for faster scanning
        with ThreadPoolExecutor(max_workers=100) as executor:
            futures = {executor.submit(self._check_port, ip, port): port for port in port_range}
            
            for i, future in enumerate(futures):
                try:
                    port, is_open = future.result(timeout=self.config['scan_timeout'])
                    if is_open:
                        open_ports.append(port)
                        if self.use_gui:
                            self.update_scan_results(f"Port {port} is open\n")
                        else:
                            print(f"{Colors.GREEN}Port {port} is open{Colors.END}")
                        
                    # Display progress every 100 ports
                    if (i + 1) % 100 == 0:
                        elapsed = time.time() - start_time
                        message = f"Scanned {i+1} ports | Elapsed: {elapsed:.1f}s | Open ports: {len(open_ports)}"
                        
                        if self.use_gui:
                            self.update_scan_results(message + "\n")
                        else:
                            print(f"{Colors.DARK_GREEN}{message}{Colors.END}")
                            
                except Exception as e:
                    pass
                    
        elapsed = time.time() - start_time
        if self.use_gui:
            self.update_scan_results(f"Scan completed in {elapsed:.1f} seconds\n")
            self.update_scan_results(f"Open ports: {sorted(open_ports)}\n")
        else:
            print(f"{Colors.GREEN}Scan completed in {elapsed:.1f} seconds{Colors.END}")
            print(f"{Colors.GREEN}Open ports: {sorted(open_ports)}{Colors.END}")
        
        self.log_operation("PORT_SCAN_COMPLETE", 
                          f"IP: {ip}, Open ports: {len(open_ports)}, Time: {elapsed:.1f}s")

    def _check_port(self, ip: str, port: int) -> Tuple[int, bool]:
        """Check if a port is open on the target IP"""
        try:
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(self.config['scan_timeout'])
            result = sock.connect_ex((ip, port))
            sock.close()
            return port, result == 0
        except:
            return port, False

    def test_connection(self):
        """Test network connectivity"""
        if self.use_gui:
            self.update_status("Testing network connectivity...")
        else:
            print(f"{Colors.GREEN}Testing network connectivity...{Colors.END}")
        
        test_ips = ["8.8.8.8", "1.1.1.1", "google.com"]
        all_successful = True
        
        for test_ip in test_ips:
            success, response_time = self.ping_ip(test_ip)
            status = "SUCCESS" if success else "FAILED"
            message = f"Ping {test_ip}: {status} ({response_time}ms)"
            
            if self.use_gui:
                self.update_diagnostic_results(message + "\n")
            else:
                print(message)
                
            if not success:
                all_successful = False
                
        if all_successful:
            message = "All connectivity tests passed"
            if self.use_gui:
                self.update_diagnostic_results(message + "\n")
                self.update_status(message)
            else:
                print(f"{Colors.GREEN}{message}{Colors.END}")
        else:
            message = "Some connectivity tests failed"
            if self.use_gui:
                self.update_diagnostic_results(message + "\n")
                self.update_status(message)
            else:
                print(f"{Colors.RED}{message}{Colors.END}")

    def dns_lookup(self, domain: str):
        """Perform DNS lookup for a domain"""
        if self.use_gui:
            self.update_scan_results(f"Performing DNS lookup for {domain}\n")
        else:
            print(f"{Colors.GREEN}Performing DNS lookup for {domain}{Colors.END}")
            
        self.log_operation("DNS_LOOKUP", f"Domain: {domain}")
        
        try:
            # A record
            try:
                a_records = dns.resolver.resolve(domain, 'A')
                if self.use_gui:
                    self.update_scan_results("A Records:\n")
                else:
                    print(f"{Colors.CYAN}A Records:{Colors.END}")
                for record in a_records:
                    if self.use_gui:
                        self.update_scan_results(f"  {record.address}\n")
                    else:
                        print(f"  {record.address}")
            except:
                if self.use_gui:
                    self.update_scan_results("No A records found\n")
                else:
                    print(f"{Colors.RED}No A records found{Colors.END}")
                
            # AAAA record (IPv6)
            try:
                aaaa_records = dns.resolver.resolve(domain, 'AAAA')
                if self.use_gui:
                    self.update_scan_results("AAAA Records:\n")
                else:
                    print(f"{Colors.CYAN}AAAA Records:{Colors.END}")
                for record in aaaa_records:
                    if self.use_gui:
                        self.update_scan_results(f"  {record.address}\n")
                    else:
                        print(f"  {record.address}")
            except:
                if self.use_gui:
                    self.update_scan_results("No AAAA records found\n")
                else:
                    print(f"{Colors.RED}No AAAA records found{Colors.END}")
                
            # MX records
            try:
                mx_records = dns.resolver.resolve(domain, 'MX')
                if self.use_gui:
                    self.update_scan_results("MX Records:\n")
                else:
                    print(f"{Colors.CYAN}MX Records:{Colors.END}")
                for record in mx_records:
                    if self.use_gui:
                        self.update_scan_results(f"  {record.preference} {record.exchange}\n")
                    else:
                        print(f"  {record.preference} {record.exchange}")
            except:
                if self.use_gui:
                    self.update_scan_results("No MX records found\n")
                else:
                    print(f"{Colors.RED}No MX records found{Colors.END}")
                
            # NS records
            try:
                ns_records = dns.resolver.resolve(domain, 'NS')
                if self.use_gui:
                    self.update_scan_results("NS Records:\n")
                else:
                    print(f"{Colors.CYAN}NS Records:{Colors.END}")
                for record in ns_records:
                    if self.use_gui:
                        self.update_scan_results(f"  {record.target}\n")
                    else:
                        print(f"  {record.target}")
            except:
                if self.use_gui:
                    self.update_scan_results("No NS records found\n")
                else:
                    print(f"{Colors.RED}No NS records found{Colors.END}")
                
        except dns.resolver.NXDOMAIN:
            error_msg = "Domain does not exist"
            if self.use_gui:
                self.update_scan_results(error_msg + "\n")
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")
        except dns.resolver.NoAnswer:
            error_msg = "No DNS records found"
            if self.use_gui:
                self.update_scan_results(error_msg + "\n")
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")
        except Exception as e:
            error_msg = f"DNS lookup error: {e}"
            if self.use_gui:
                self.update_scan_results(error_msg + "\n")
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")

    def reverse_dns(self, ip: str):
        """Perform reverse DNS lookup"""
        if not self.validate_ip(ip):
            if self.use_gui:
                messagebox.showerror("Error", "Invalid IP address format")
            else:
                print(f"{Colors.RED}Invalid IP address format{Colors.END}")
            return
            
        if self.use_gui:
            self.update_diagnostic_results(f"Performing reverse DNS lookup for {ip}\n")
        else:
            print(f"{Colors.GREEN}Performing reverse DNS lookup for {ip}{Colors.END}")
            
        self.log_operation("REVERSE_DNS", f"IP: {ip}")
        
        try:
            hostname, aliases, addresses = socket.gethostbyaddr(ip)
            if self.use_gui:
                self.update_diagnostic_results(f"Hostname: {hostname}\n")
                if aliases:
                    self.update_diagnostic_results(f"Aliases: {aliases}\n")
                if addresses:
                    self.update_diagnostic_results(f"Addresses: {addresses}\n")
            else:
                print(f"{Colors.CYAN}Hostname: {hostname}{Colors.END}")
                if aliases:
                    print(f"{Colors.CYAN}Aliases: {aliases}{Colors.END}")
                if addresses:
                    print(f"{Colors.CYAN}Addresses: {addresses}{Colors.END}")
        except socket.herror:
            error_msg = "No reverse DNS record found"
            if self.use_gui:
                self.update_diagnostic_results(error_msg + "\n")
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")
        except Exception as e:
            error_msg = f"Reverse DNS lookup error: {e}"
            if self.use_gui:
                self.update_diagnostic_results(error_msg + "\n")
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")

    def whois_lookup(self, query: str):
        """Perform WHOIS lookup"""
        if self.use_gui:
            self.update_scan_results(f"Performing WHOIS lookup for {query}\n")
        else:
            print(f"{Colors.GREEN}Performing WHOIS lookup for {query}{Colors.END}")
            
        self.log_operation("WHOIS_LOOKUP", f"Query: {query}")
        
        try:
            # Try to use system whois command
            result = subprocess.run(
                ["whois", query],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode == 0:
                # Extract relevant information
                lines = result.stdout.split('\n')
                relevant_info = []
                
                # Look for key fields
                key_fields = ['Registrar', 'Creation Date', 'Updated Date', 
                             'Expiration Date', 'Name Server', 'Status']
                
                for line in lines:
                    for field in key_fields:
                        if field.lower() in line.lower() and ':' in line:
                            relevant_info.append(line.strip())
                            break
                
                if relevant_info:
                    if self.use_gui:
                        self.update_scan_results("Relevant WHOIS information:\n")
                    else:
                        print(f"{Colors.CYAN}Relevant WHOIS information:{Colors.END}")
                    for info in relevant_info:
                        if self.use_gui:
                            self.update_scan_results(f"  {info}\n")
                        else:
                            print(f"  {info}")
                else:
                    if self.use_gui:
                        self.update_scan_results(result.stdout)
                    else:
                        print(f"{Colors.CYAN}{result.stdout}{Colors.END}")
            else:
                error_msg = "WHOIS lookup failed"
                if self.use_gui:
                    self.update_scan_results(error_msg + "\n")
                else:
                    print(f"{Colors.RED}{error_msg}{Colors.END}")
                    
        except subprocess.TimeoutExpired:
            error_msg = "WHOIS lookup timed out"
            if self.use_gui:
                self.update_scan_results(error_msg + "\n")
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")
        except FileNotFoundError:
            error_msg = "WHOIS command not available"
            if self.use_gui:
                self.update_scan_results(error_msg + "\n")
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")
        except Exception as e:
            error_msg = f"WHOIS lookup error: {e}"
            if self.use_gui:
                self.update_scan_results(error_msg + "\n")
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")

    def monitor_bandwidth(self, duration: int = 10):
        """Monitor bandwidth usage"""
        if self.use_gui:
            self.update_status(f"Monitoring bandwidth for {duration} seconds...")
            self.update_diagnostic_results(f"Monitoring bandwidth for {duration} seconds...\n")
        else:
            print(f"{Colors.GREEN}Monitoring bandwidth for {duration} seconds...{Colors.END}")
            print(f"{Colors.GREEN}Press Ctrl+C to stop early{Colors.END}")
        
        try:
            # Get initial network stats
            net_io_start = psutil.net_io_counters()
            start_time = time.time()
            
            while time.time() - start_time < duration:
                time.sleep(1)
                net_io_current = psutil.net_io_counters()
                
                # Calculate rates
                elapsed = time.time() - start_time
                bytes_sent = net_io_current.bytes_sent - net_io_start.bytes_sent
                bytes_recv = net_io_current.bytes_recv - net_io_start.bytes_recv
                
                # Convert to bits per second
                bps_sent = (bytes_sent * 8) / elapsed
                bps_recv = (bytes_recv * 8) / elapsed
                
                # Convert to appropriate units
                if bps_sent > 1000000:
                    sent_str = f"{bps_sent / 1000000:.2f} Mbps"
                else:
                    sent_str = f"{bps_sent / 1000:.2f} Kbps"
                    
                if bps_recv > 1000000:
                    recv_str = f"{bps_recv / 1000000:.2f} Mbps"
                else:
                    recv_str = f"{bps_recv / 1000:.2f} Kbps"
                
                # Display stats
                message = f"Upload: {sent_str} | Download: {recv_str}"
                
                if self.use_gui:
                    self.update_diagnostic_results(message + "\n")
                    self.status_var.set(message)
                else:
                    sys.stdout.write('\r\033[K')
                    sys.stdout.write(f"{Colors.CYAN}{message}{Colors.END}")
                    sys.stdout.flush()
                
            message = "Bandwidth monitoring completed"
            if self.use_gui:
                self.update_diagnostic_results(message + "\n")
                self.update_status(message)
            else:
                print(f"\n{Colors.GREEN}{message}{Colors.END}")
            
        except KeyboardInterrupt:
            message = "Bandwidth monitoring stopped"
            if self.use_gui:
                self.update_diagnostic_results(message + "\n")
                self.update_status(message)
            else:
                print(f"\n{Colors.YELLOW}{message}{Colors.END}")
        except Exception as e:
            error_msg = f"Bandwidth monitoring error: {e}"
            if self.use_gui:
                self.update_diagnostic_results(error_msg + "\n")
                self.update_status(error_msg)
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")

    def config_telegram(self, key: str, value: str):
        """Configure Telegram settings"""
        if key == "token":
            self.config['telegram_token'] = value
            if self.use_gui:
                self.update_status("Telegram token configured")
            else:
                print(f"{Colors.GREEN}Telegram token configured{Colors.END}")
        elif key == "chat_id":
            self.config['telegram_chat_id'] = value
            if self.use_gui:
                self.update_status("Telegram chat ID configured")
            else:
                print(f"{Colors.GREEN}Telegram chat ID configured{Colors.END}")
        else:
            error_msg = "Invalid configuration key"
            if self.use_gui:
                messagebox.showerror("Error", error_msg)
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")
            
        self.log_operation("CONFIG_TELEGRAM", f"{key}: {value}")

    def send_telegram_message(self, message: str):
        """Send a message via Telegram"""
        if not self.config['telegram_token'] or not self.config['telegram_chat_id']:
            error_msg = "Telegram not configured. Set token and chat ID first."
            if self.use_gui:
                messagebox.showerror("Error", error_msg)
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")
            return False
            
        try:
            url = f"https://api.telegram.org/bot{self.config['telegram_token']}/sendMessage"
            data = {
                "chat_id": self.config['telegram_chat_id'],
                "text": message
            }
            
            response = requests.post(url, data=data, timeout=10)
            if response.status_code == 200:
                if self.use_gui:
                    self.update_status("Message sent to Telegram")
                else:
                    print(f"{Colors.GREEN}Message sent to Telegram{Colors.END}")
                return True
            else:
                error_msg = f"Failed to send message: {response.text}"
                if self.use_gui:
                    messagebox.showerror("Error", error_msg)
                else:
                    print(f"{Colors.RED}{error_msg}{Colors.END}")
                return False
                
        except Exception as e:
            error_msg = f"Error sending Telegram message: {e}"
            if self.use_gui:
                messagebox.showerror("Error", error_msg)
            else:
                print(f"{Colors.RED}{error_msg}{Colors.END}")
            return False

    def export_data(self):
        """Export data to Telegram"""
        if not self.operation_log:
            if self.use_gui:
                messagebox.showinfo("Info", "No data to export")
            else:
                print(f"{Colors.YELLOW}No data to export{Colors.END}")
            return
            
        # Prepare the message (Telegram has a 4096 character limit)
        message = "Cyber Security Tool Export\n\n"
        message += "\n".join(self.operation_log[-20:])  # Last 20 entries
        
        if len(message) > 4000:
            message = message[:4000] + "\n... (truncated)"
            
        if self.send_telegram_message(message):
            if self.use_gui:
                self.update_status("Data exported to Telegram")
            else:
                print(f"{Colors.GREEN}Data exported to Telegram{Colors.END}")
            self.log_operation("EXPORT_DATA", "To Telegram")

    def show_status(self):
        """Show current tool status"""
        if self.use_gui:
            self.refresh_dashboard()
        else:
            print(f"{Colors.BOLD}{Colors.LIGHT_GREEN}Cyber Security Tool Status{Colors.END}")
            print(f"{Colors.GREEN}Monitoring: {len(self.monitored_ips)} IPs{Colors.END}")
            print(f"{Colors.GREEN}Traffic Generation: {'Active' if self.traffic_generation else 'Inactive'}{Colors.END}")
            print(f"{Colors.GREEN}Telegram: {'Configured' if self.config['telegram_token'] and self.config['telegram_chat_id'] else 'Not Configured'}{Colors.END}")
            print(f"{Colors.GREEN}Log Entries: {len(self.operation_log)}{Colors.END}")

    def view_log(self):
        """View operation log"""
        if not self.operation_log:
            if self.use_gui:
                messagebox.showinfo("Info", "No log entries")
            else:
                print(f"{Colors.YELLOW}No log entries{Colors.END}")
            return
            
        if self.use_gui:
            self.notebook.select(self.log_tab)
            self.refresh_log()
        else:
            print(f"{Colors.BOLD}{Colors.LIGHT_GREEN}Operation Log{Colors.END}")
            for entry in self.operation_log[-20:]:  # Show last 20 entries
                print(f"{Colors.DARK_GREEN}{entry}{Colors.END}")

    def clear_screen(self):
        """Clear the terminal screen"""
        if not self.use_gui:
            os.system('cls' if os.name == 'nt' else 'clear')
            self.print_banner()

    def run_command(self, command: str):
        """Parse and execute a command"""
        parts = command.strip().split()
        if not parts:
            return
            
        cmd = parts[0].lower()
        
        try:
            if cmd == "help":
                self.print_help()
                
            elif cmd == "exit":
                self.stop_monitoring()
                if self.use_gui:
                    self.root.quit()
                else:
                    print(f"{Colors.GREEN}Exiting Cyber Security Tool{Colors.END}")
                    exit(0)
                
            elif cmd == "clear":
                self.clear_screen()
                
            elif cmd == "view":
                self.view_log()
                
            elif cmd == "status":
                self.show_status()
                
            elif cmd == "ping" and len(parts) >= 3:
                if parts[1].lower() == "ip":
                    ip = parts[2]
                    success, response_time = self.ping_ip(ip)
                    status = f"{Colors.GREEN}Reachable{Colors.END}" if success else f"{Colors.RED}Unreachable{Colors.END}"
                    print(f"Ping {ip}: {status} ({response_time}ms)")
                    
                elif parts[1].lower() == "ip6" and len(parts) >= 3:
                    ip = parts[2]
                    success, response_time = self.ping_ip6(ip)
                    status = f"{Colors.GREEN}Reachable{Colors.END}" if success else f"{Colors.RED}Unreachable{Colors.END}"
                    print(f"Ping {ip}: {status} ({response_time}ms)")
                    
                elif parts[1].lower() == "hostname" and len(parts) >= 3:
                    hostname = parts[2]
                    ip = self.resolve_hostname(hostname)
                    if ip:
                        success, response_time = self.ping_ip(ip)
                        status = f"{Colors.GREEN}Reachable{Colors.END}" if success else f"{Colors.RED}Unreachable{Colors.END}"
                        print(f"Ping {hostname} ({ip}): {status} ({response_time}ms)")
                    else:
                        print(f"{Colors.RED}Could not resolve hostname: {hostname}{Colors.END}")
                    
            elif cmd == "start" and len(parts) >= 4 and parts[1].lower() == "monitoring":
                if parts[2].lower() == "ip":
                    ip = parts[3]
                    self.start_monitoring_ip(ip)
                    
            elif cmd == "stop":
                self.stop_monitoring()
                
            elif cmd == "config" and len(parts) >= 4:
                if parts[1].lower() == "telegram":
                    if parts[2].lower() == "token":
                        self.config_telegram("token", parts[3])
                    elif parts[2].lower() == "chat_id":
                        self.config_telegram("chat_id", parts[3])
                        
            elif cmd == "test" and len(parts) >= 2:
                if parts[1].lower() == "message":
                    self.send_telegram_message("Test message from Cyber Security Tool")
                elif parts[1].lower() == "connection":
                    self.test_connection()
                    
            elif cmd == "add" and len(parts) >= 3:
                if parts[1].lower() == "ip":
                    ip = parts[2]
                    if self.validate_ip(ip) or self.validate_ipv6(ip):
                        self.ip_list.add(ip)
                        print(f"{Colors.GREEN}Added IP: {ip}{Colors.END}")
                    else:
                        print(f"{Colors.RED}Invalid IP address{Colors.END}")
                        
            elif cmd == "remove" and len(parts) >= 3:
                if parts[1].lower() == "ip":
                    ip = parts[2]
                    if ip in self.ip_list:
                        self.ip_list.remove(ip)
                        print(f"{Colors.GREEN}Removed IP: {ip}{Colors.END}")
                    else:
                        print(f"{Colors.YELLOW}IP not in list{Colors.END}")
                        
            elif cmd == "generate" and len(parts) >= 4:
                if parts[1].lower() == "traffic":
                    if len(parts) >= 5:
                        # Format: generate traffic <IP> <TYPE> <DURATION>
                        target_ip = parts[2]
                        traffic_type = parts[3]
                        duration = parts[4]
                        self.generate_traffic(target_ip, traffic_type, duration)
                    else:
                        # Format: generate traffic <TYPE> <DURATION> (to monitored IPs)
                        traffic_type = parts[2]
                        duration = parts[3]
                        self.generate_traffic_to_monitored(traffic_type, duration)
                    
            elif cmd == "traceroute" and len(parts) >= 3:
                if parts[1].lower() == "ip":
                    ip = parts[2]
                    self.traceroute(ip)
                    
            elif cmd == "tcptraceroute" and len(parts) >= 3:
                if parts[1].lower() == "ip":
                    ip = parts[2]
                    self.traceroute(ip, "tcp")
                    
            elif cmd == "udptraceroute" and len(parts) >= 3:
                if parts[1].lower() == "ip":
                    ip = parts[2]
                    self.traceroute(ip, "udp")
                    
            elif cmd == "scan" and len(parts) >= 3:
                if parts[1].lower() == "ip":
                    ip = parts[2]
                    self.scan_ports(ip)
                    
            elif cmd == "deep" and len(parts) >= 4:
                if parts[1].lower() == "scan" and parts[2].lower() == "ip":
                    ip = parts[3]
                    self.scan_ports(ip, deep=True)
                    
            elif cmd == "dns" and len(parts) >= 3:
                if parts[1].lower() == "lookup":
                    domain = parts[2]
                    self.dns_lookup(domain)
                    
            elif cmd == "reverse" and len(parts) >= 3:
                if parts[1].lower() == "dns":
                    ip = parts[2]
                    self.reverse_dns(ip)
                    
            elif cmd == "whois" and len(parts) >= 2:
                query = parts[1]
                self.whois_lookup(query)
                
            elif cmd == "bandwidth":
                duration = 10
                if len(parts) >= 2:
                    try:
                        duration = int(parts[1])
                    except ValueError:
                        pass
                self.monitor_bandwidth(duration)
                
            elif cmd == "network" and len(parts) >= 2:
                if parts[1].lower() == "info":
                    network_info = self.get_network_info()
                    if network_info:
                        print(f"{Colors.CYAN}Network Information:{Colors.END}")
                        for interface, info in network_info.items():
                            print(f"{Colors.GREEN}Interface: {interface}{Colors.END}")
                            for key, value in info.items():
                                print(f"  {key}: {value}")
                    else:
                        print(f"{Colors.RED}Could not retrieve network information{Colors.END}")
                    
            elif cmd == "export" and len(parts) >= 2:
                if parts[1].lower() == "data":
                    self.export_data()
                    
            else:
                print(f"{Colors.RED}Unknown command: {command}{Colors.END}")
                print(f"{Colors.YELLOW}Type 'help' for available commands{Colors.END}")
                
        except Exception as e:
            print(f"{Colors.RED}Error executing command: {e}{Colors.END}")

    def run(self):
        """Main run loop"""
        if self.use_gui:
            # Start GUI
            self.refresh_dashboard()
            self.refresh_log()
            self.root.mainloop()
        else:
            # Start CLI
            self.clear_screen()
            
            while True:
                try:
                    command = input(f"{Colors.GREEN}cyber-tool>{Colors.END} ")
                    self.run_command(command)
                except KeyboardInterrupt:
                    print("\nUse 'exit' to quit the tool")
                except Exception as e:
                    print(f"{Colors.RED}Unexpected error: {e}{Colors.END}")

def main():
    """Main function"""
    parser = argparse.ArgumentParser(description="Accurate Cyber Defense")
    parser.add_argument("--gui", action="store_true", help="Launch with graphical interface")
    args = parser.parse_args()
    
    tool = CyberSecurityTool(use_gui=args.gui)
    tool.run()

if __name__ == "__main__":
    main()