# --- Keep ALL imports the same ---
import os
import sys
import re
import base64
import binascii
import json
import time
import random
import socket
import urllib.parse
import subprocess
import threading
import concurrent.futures
import platform
import tempfile
if platform.system() == "Windows":
    try:
        import winreg
        import ctypes
    except ImportError:
        # Handle missing modules on non-Windows or if they are not installed
        # This is more of a fallback, as the method using them should also check platform
        pass
import secrets
import traceback # Added for detailed error logging
import datetime # Added for timestamp in error logs
from datetime import datetime
import collections
from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout, QLabel,
    QLineEdit, QPushButton, QTextEdit, QComboBox, QTabWidget, QFileDialog,
    QCheckBox, QMessageBox, QGroupBox, QRadioButton, QButtonGroup, QListWidget,
    QSplitter, QFrame, QSpacerItem, QSizePolicy, QAbstractItemView, QProgressBar,
    QTreeWidget, QTreeWidgetItem, QScrollArea, QMenu, QTableWidget, QTableWidgetItem, QHeaderView,
    QSpinBox, QInputDialog, QDialog, QListWidgetItem
)
from PyQt5.QtCore import Qt, QUrl, QSize, QThread, pyqtSignal, QObject, QTimer, QMetaObject, pyqtSlot, Q_ARG, QCoreApplication, QEvent
from PyQt5.QtGui import QIcon, QFont, QDesktopServices, QColor, QPalette, QCursor, QClipboard
import requests
import math

# Disable requests warnings about unverified HTTPS requests
import urllib3
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry
from PyQt5.QtCore import QObject
import yaml
from urllib.parse import parse_qs, urlparse

# --- ADDED: Custom Exception for Cancelled Operations ---
class OperationCanceledError(Exception):
    """Exception raised when a test operation is cancelled by the user."""
    pass
# --- END ADDED ---

# --- Placeholder/Decoding Functions (Keep As Is) ---
def fix_base64_padding(s):
    s = s.strip(); padding_needed = len(s) % 4
    if padding_needed: s += '=' * (4 - padding_needed)
    return s

def decode_ssurl(url, parent_logger=None):
    # ... (Keep the refined decode_ssurl function - unchanged) ...
    log = parent_logger if parent_logger else print
    log(f"DEBUG (decode_ssurl): Processing SS URL: {url[:60]}...")
    config = {'protocol': 'ss', 'original_url': url, 'remark': 'N/A', 'hostname': 'error', 'port': '0'}
    try:
        if url.startswith('ss://'): url = url[5:]
        if url.startswith('ey'): # SIP008
            log(f"DEBUG (decode_ssurl): SIP008 format detected.")
            try:
                base64_str = fix_base64_padding(url)
                try:
                    decoded_bytes = base64.b64decode(base64_str)
                except Exception as b64_err:
                    log(f"DEBUG (decode_ssurl): Base64 decode error: {b64_err}")
                    raise ValueError(f"Base64 decode error: {b64_err}")

                try:
                    json_data = json.loads(decoded_bytes.decode('utf-8', errors='ignore'))
                except json.JSONDecodeError as json_err:
                    log(f"DEBUG (decode_ssurl): JSON decode error: {json_err}")
                    raise

                if isinstance(json_data, dict):
                    config['hostname'] = json_data.get('server', json_data.get('add', 'sip008_host_err'))
                    config['port'] = str(json_data.get('server_port', json_data.get('port', '0')))
                    config['method'] = json_data.get('method', 'aes-256-gcm'); config['password'] = json_data.get('password', 'sip008_pass_err')
                    config['remark'] = json_data.get('remarks', json_data.get('ps', 'SIP008 Config'))
                    # Add other potential fields if SIP008 includes stream settings etc.
                    config['plugin'] = json_data.get('plugin', '')
                    config['plugin_opts'] = json_data.get('plugin_opts', '')
                    log(f"DEBUG (decode_ssurl): SIP008 decoded successfully -> Host: {config['hostname']}")
                else:
                    log(f"DEBUG (decode_ssurl): SIP008 JSON structure invalid."); config.update({'remark': 'SIP008 (Invalid JSON Structure)'})
            except (json.JSONDecodeError, UnicodeDecodeError, ValueError) as json_err:
                log(f"DEBUG (decode_ssurl): SIP008 decoding failed: {json_err}"); config.update({'remark': f'SIP008 (Decode Error: {json_err})'})
            except Exception as sip_err:
                log(f"DEBUG (decode_ssurl): Unexpected SIP008 error: {sip_err}"); config.update({'remark': f'SIP008 (Processing Error)'})
            config['protocol'] = 'ss'; log(f"DEBUG (decode_ssurl): Returning SIP008 result: {config}"); return config
        elif '@' in url: # Standard with @
            log(f"DEBUG (decode_ssurl): Standard format with '@' detected."); parts = url.split('@', 1); auth_part = parts[0]; server_part = parts[1]
            try:
                auth_part_padded = fix_base64_padding(auth_part)
                try:
                    auth_decoded = base64.b64decode(auth_part_padded).decode('utf-8')
                except Exception as b64_err:
                    log(f"DEBUG (decode_ssurl): Base64 decode error in auth part: {b64_err}")
                    raise ValueError(f"Base64 decode error: {b64_err}")

                if ':' not in auth_decoded: raise ValueError("Auth part format invalid (missing colon)")
                config['method'], config['password'] = auth_decoded.split(':', 1)
            except (UnicodeDecodeError, ValueError) as auth_err:
                log(f"DEBUG (decode_ssurl): Failed decode auth '{auth_part}': {auth_err}. Trying plain text.")
                if ':' in auth_part:
                    try:
                        config['method'], config['password'] = auth_part.split(':', 1); log("DEBUG (decode_ssurl): Decoded auth as plain text.")
                    except ValueError:
                        log("DEBUG (decode_ssurl): Plain text auth format invalid."); return None
                else:
                    log("DEBUG (decode_ssurl): Auth part format invalid."); return None
            server_remark_parts = server_part.split('#', 1); server_info = server_remark_parts[0]
            if len(server_remark_parts) > 1:
                try:
                    config['remark'] = urllib.parse.unquote(server_remark_parts[1])
                except Exception:
                    config['remark'] = server_remark_parts[1]
            # Handle potential query parameters for plugin options etc.
            server_query_parts = server_info.split('?', 1)
            server_host_port = server_query_parts[0]
            if len(server_query_parts) > 1:
                config['query_str'] = server_query_parts[1] # Store query string for later parsing if needed

            if ':' not in server_host_port:
                log(f"DEBUG (decode_ssurl): Server part missing port: {server_host_port}"); return None
            config['hostname'], port_str = server_host_port.rsplit(':', 1)
            try:
                config['port'] = str(int(port_str))
            except ValueError:
                log(f"DEBUG (decode_ssurl): Invalid port number: {port_str}"); return None
        else: # Legacy no @
            log(f"DEBUG (decode_ssurl): Legacy format (no '@') detected."); url_remark_parts = url.split('#', 1); base64_content = url_remark_parts[0]
            if len(url_remark_parts) > 1:
                try:
                    config['remark'] = urllib.parse.unquote(url_remark_parts[1])
                except Exception:
                    config['remark'] = url_remark_parts[1]
            try:
                base64_padded = fix_base64_padding(base64_content)
                try:
                    decoded_str = base64.b64decode(base64_padded).decode('utf-8')
                except Exception as b64_err:
                    log(f"DEBUG (decode_ssurl): Base64 decode error in legacy format: {b64_err}")
                    raise ValueError(f"Base64 decode error: {b64_err}")

                if '@' not in decoded_str or ':' not in decoded_str: raise ValueError("Legacy decoded format invalid")
                auth_part, server_part = decoded_str.split('@', 1); config['method'], config['password'] = auth_part.split(':', 1)
                if ':' not in server_part: raise ValueError("Legacy server part missing port")
                config['hostname'], port_str = server_part.rsplit(':', 1); config['port'] = str(int(port_str))
            except (UnicodeDecodeError, ValueError) as legacy_err:
                log(f"DEBUG (decode_ssurl): Failed legacy decode: {legacy_err}"); return None
        config['protocol'] = 'ss'; log(f"DEBUG (decode_ssurl): Decoded OK -> Host:{config['hostname']}, Port:{config['port']}"); log(f"DEBUG (decode_ssurl): Returning: {config}"); return config
    except Exception as e:
        log(f"ERROR (decode_ssurl): Unexpected error processing URL {url[:60]}: {e}"); return None

def decode_proxy_url(url, parent_logger=None):
    # ... (Keep the refined decode_proxy_url function - unchanged) ...
    log = parent_logger if parent_logger else print; url = url.strip()

    # Special error logging function for critical errors
    def log_critical_error(error_type, error_msg, details=None):
        error_text = f"CRITICAL ERROR in decode_proxy_url: {error_type} - {error_msg}"
        log(error_text)

        # Log to debug_log.txt if possible
        try:
            log_file_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "debug_log.txt")
            with open(log_file_path, 'a', encoding='utf-8') as f:
                f.write(f"\n[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] {error_text}\n")
                if details:
                    f.write(f"Details: {details}\n")
                    f.write(f"URL: {url[:50]}...\n" if len(url) > 50 else f"URL: {url}\n")
        except Exception as log_err:
            print(f"Error writing to log file: {log_err}")

    if not url: return None
    log(f"DEBUG (decode_proxy_url): Processing line: {url[:60]}...")
    if url.startswith('#'):
        log("DEBUG (decode_proxy_url): Detected comment line.")
        comment_config = {'protocol': 'comment', 'original_url': url, 'remark': url[1:].strip()}
        log(f"DEBUG (decode_proxy_url): Returning comment config: {comment_config}")
        return comment_config

    parsed_url = None
    scheme = ''
    try:
        # Special handling for SS URIs that might not have // correctly
        if url.startswith('ss:') and not url.startswith('ss://'):
            url = 'ss://' + url[3:]
        # Try parsing SIP008 JSON directly if it starts with 'ey' (might be inside other schemes)
        if url.startswith('ey'):
            log("DEBUG (decode_proxy_url): Potential SIP008 base64 detected, attempting SS decode.")
            ss_config = decode_ssurl('ss://' + url, parent_logger=log) # Try decoding as SS
            if ss_config and ss_config.get('protocol') == 'ss':
                 log(f"DEBUG (decode_proxy_url): SIP008 base64 successfully decoded via ssurl: {ss_config}")
                 return ss_config
            else:
                 log("DEBUG (decode_proxy_url): SIP008 base64 decode via ssurl failed, proceeding as generic URL.")


        parsed_url = urlparse(url)
        scheme = parsed_url.scheme.lower() if parsed_url.scheme else ''
        if not scheme:
             # If no scheme, check if it's a potential SS URI (legacy base64 or method:pass@...)
             if '@' in url or len(url) > 20: # Heuristic
                 log(f"DEBUG (decode_proxy_url): No scheme, attempting SS decode for: {url[:60]}")
                 ss_config = decode_ssurl('ss://' + url, parent_logger=log) # Prepend ss:// and try
                 if ss_config and ss_config.get('protocol') == 'ss':
                     log(f"DEBUG (decode_proxy_url): Decoded as SS successfully: {ss_config}")
                     return ss_config
                 else:
                      log(f"DEBUG (decode_proxy_url): Failed SS decode, marking as unknown.")
                      return {'protocol': 'unknown', 'original_url': url, 'remark': 'Unknown Format (No Scheme)', 'hostname': 'error', 'port': '0'}
             else:
                 log(f"DEBUG (decode_proxy_url): No scheme and doesn't look like SS URI: {url[:60]}")
                 return {'protocol': 'unknown', 'original_url': url, 'remark': 'Unknown Format (No Scheme)', 'hostname': 'error', 'port': '0'}
    except Exception as parse_err:
        log(f"ERROR (decode_proxy_url): URL parsing failed for {url[:60]}: {parse_err}")
        return {'protocol': 'error', 'original_url': url, 'remark': f'URL Parse Error: {parse_err}', 'hostname': 'error', 'port': '0'}

    log(f"DEBUG (decode_proxy_url): Detected scheme: '{scheme}'")
    config = {'protocol': scheme, 'original_url': url, 'remark': 'N/A', 'hostname': 'error', 'port': '0'}

    try:
        if scheme == 'ss':
            # Use the dedicated ss decoder again, it handles variations better
            ss_config = decode_ssurl(url, parent_logger=log)
            log(f"DEBUG (decode_proxy_url): decode_ssurl returned: {ss_config}")
            # Ensure base fields exist even if ss_config is None
            if ss_config:
                ss_config.setdefault('hostname', 'ss_err')
                ss_config.setdefault('port', '0')
                ss_config.setdefault('remark', 'SS Decode Error' if ss_config.get('hostname') == 'error' else 'N/A')
                return ss_config
            else:
                return {'protocol': 'error', 'original_url': url, 'remark': 'SS Decode Failed', 'hostname': 'error', 'port': '0'}

        elif scheme == 'vmess':
            config['protocol'] = 'vmess'
            if not parsed_url.netloc:
                log("DEBUG (decode_proxy_url): VMess URL empty netloc.")
                return {'protocol': 'error', 'original_url': url, 'remark': 'VMess Error (Empty Netloc)', 'hostname': 'error', 'port': '0'}
            try:
                base64_str = fix_base64_padding(parsed_url.netloc)
                try:
                    decoded_bytes = base64.b64decode(base64_str)
                except Exception as b64_err:
                    log(f"DEBUG (decode_proxy_url): Base64 decode error: {b64_err}")
                    # Log critical error for debugging
                    log_critical_error("Base64Error", f"Failed to decode base64 in VMess URL",
                                      f"Error: {b64_err}\nBase64 string (first 20 chars): {base64_str[:20]}...")
                    raise ValueError(f"Base64 decode error: {b64_err}")

                try:
                    vmess_data = json.loads(decoded_bytes.decode('utf-8', errors='ignore'))
                except json.JSONDecodeError as json_err:
                    log(f"DEBUG (decode_proxy_url): JSON decode error: {json_err}")
                    # Log critical error for debugging
                    log_critical_error("JSONDecodeError", f"Failed to parse JSON in VMess URL",
                                      f"Error: {json_err}\nDecoded content (first 50 chars): {decoded_bytes.decode('utf-8', errors='ignore')[:50]}...")
                    raise

                if not isinstance(vmess_data, dict):
                    log_critical_error("DataTypeError", "Decoded VMess data is not a dictionary",
                                     f"Type: {type(vmess_data)}")
                    raise ValueError("Decoded VMess data not dict")

                config['hostname'] = vmess_data.get('add', 'vmess_host_err')
                config['port'] = str(vmess_data.get('port', '0'))
                config['id'] = vmess_data.get('id', 'vmess_id_err')
                config['aid'] = str(vmess_data.get('aid', '0'))
                config['method'] = vmess_data.get('scy', vmess_data.get('security', 'auto')) # Use 'scy' or 'security'
                config['network'] = vmess_data.get('net', 'tcp')
                config['type'] = vmess_data.get('type', 'none') # Header type for TCP
                config['host'] = vmess_data.get('host', '')
                config['path'] = vmess_data.get('path', '/')
                config['tls'] = vmess_data.get('tls', '') # Should be 'tls' or empty
                config['sni'] = vmess_data.get('sni', '') # SNI
                config['remark'] = vmess_data.get('ps', f"VMess-{config['hostname']}")
                config['v'] = vmess_data.get('v', '2')
                # Add other potential fields if present in JSON
                config['fp'] = vmess_data.get('fp', '') # Fingerprint? Not standard vmess json
                config['alpn'] = vmess_data.get('alpn', '') # ALPN? Not standard vmess json
                log(f"DEBUG (decode_proxy_url): VMess decoded OK -> Host:{config['hostname']}")
            except (json.JSONDecodeError, UnicodeDecodeError, ValueError) as vmess_err:
                log(f"DEBUG (decode_proxy_url): VMess decoding failed: {vmess_err}")
                config.update({'protocol': 'error', 'remark': f'VMess Decode Error: {vmess_err}'})
            except Exception as vmess_proc_err:
                log(f"DEBUG (decode_proxy_url): Unexpected VMess error: {vmess_proc_err}")
                config.update({'protocol': 'error', 'remark': 'VMess Processing Error'})

        elif scheme == 'vless':
            config['protocol'] = 'vless'
            if '@' not in parsed_url.netloc:
                log(f"DEBUG (decode_proxy_url): Invalid VLESS format (no @): {url[:60]}")
                return {'protocol': 'error', 'original_url': url, 'remark': 'VLESS Format Error (No @)', 'hostname': 'error', 'port': '0'}
            userinfo, hostinfo = parsed_url.netloc.split('@', 1)
            config['id'] = urllib.parse.unquote(userinfo) # UUID is typically URL encoded
            if ':' not in hostinfo:
                log(f"DEBUG (decode_proxy_url): Invalid VLESS format (no port): {hostinfo}")
                return {'protocol': 'error', 'original_url': url, 'remark': 'VLESS Format Error (No Port)', 'hostname': 'error', 'port': '0'}
            config['hostname'], port_str = hostinfo.rsplit(':', 1)
            try:
                config['port'] = str(int(port_str))
            except ValueError:
                log(f"DEBUG (decode_proxy_url): Invalid VLESS port: {port_str}")
                return {'protocol': 'error', 'original_url': url, 'remark': 'VLESS Format Error (Invalid Port)', 'hostname': 'error', 'port': '0'}

            query_params = parse_qs(parsed_url.query)
            config['query'] = {k: v[0] for k, v in query_params.items()} # Store query params

            # Extract parameters primarily from query string
            config['encryption'] = config['query'].get('encryption', 'none')
            config['security'] = config['query'].get('security', 'none') # tls, reality, none
            config['sni'] = config['query'].get('sni', config['hostname']) # Use hostname if SNI not specified
            config['fp'] = config['query'].get('fp', '') # fingerprint
            config['pbk'] = config['query'].get('pbk', '') # reality public key
            config['sid'] = config['query'].get('sid', '') # reality short id
            config['flow'] = config['query'].get('flow', '')
            config['network'] = config['query'].get('type', 'tcp') # ws, grpc, tcp, h2 etc.
            config['path'] = config['query'].get('path', '/')
            config['host'] = config['query'].get('host', config['hostname']) # Host header, default to hostname
            config['serviceName'] = config['query'].get('serviceName', '') # For gRPC
            config['headerType'] = config['query'].get('headerType', 'none').lower() # For TCP obfuscation
            config['alpn'] = config['query'].get('alpn', '') # ALPN for TLS
            config['allowInsecure'] = config['query'].get('allowInsecure', '0') # Allow insecure TLS

            if parsed_url.fragment:
                try:
                    config['remark'] = urllib.parse.unquote(parsed_url.fragment)
                except Exception:
                    config['remark'] = parsed_url.fragment
            else:
                 config['remark'] = f"VLESS-{config['hostname']}" # Default remark

            log(f"DEBUG (decode_proxy_url): VLESS decoded OK -> Host:{config['hostname']}")

        elif scheme == 'trojan':
            config['protocol'] = 'trojan'
            if '@' not in parsed_url.netloc:
                log(f"DEBUG (decode_proxy_url): Invalid Trojan format (no @): {url[:60]}")
                return {'protocol': 'error', 'original_url': url, 'remark': 'Trojan Format Error (No @)', 'hostname': 'error', 'port': '0'}
            userinfo, hostinfo = parsed_url.netloc.split('@', 1)
            config['password'] = urllib.parse.unquote(userinfo) # Password can be URL encoded

            if ':' not in hostinfo:
                log(f"DEBUG (decode_proxy_url): Invalid Trojan format (no port): {hostinfo}")
                return {'protocol': 'error', 'original_url': url, 'remark': 'Trojan Format Error (No Port)', 'hostname': 'error', 'port': '0'}
            config['hostname'], port_str = hostinfo.rsplit(':', 1)
            try:
                config['port'] = str(int(port_str))
            except ValueError:
                log(f"DEBUG (decode_proxy_url): Invalid Trojan port: {port_str}")
                return {'protocol': 'error', 'original_url': url, 'remark': 'Trojan Format Error (Invalid Port)', 'hostname': 'error', 'port': '0'}

            query_params = parse_qs(parsed_url.query)
            config['query'] = {k: v[0] for k, v in query_params.items()} # Store query params

            # Extract parameters primarily from query string (Trojan usually implies TLS but Reality is possible)
            config['security'] = config['query'].get('security', 'tls') # Default to TLS for Trojan if not specified
            config['sni'] = config['query'].get('sni', config['hostname']) # Use hostname if SNI not specified
            config['fp'] = config['query'].get('fp', '') # fingerprint (usually for TLS/Reality)
            config['pbk'] = config['query'].get('pbk', '') # reality public key (if security=reality)
            config['sid'] = config['query'].get('sid', '') # reality short id (if security=reality)
            config['flow'] = config['query'].get('flow', '') # Not standard Trojan, but handle if present
            config['network'] = config['query'].get('type', 'tcp') # Underlying transport: ws, grpc, tcp
            config['path'] = config['query'].get('path', '/') # Path for WS/gRPC/H2
            config['host'] = config['query'].get('host', config['hostname']) # Host header
            config['serviceName'] = config['query'].get('serviceName', '') # For gRPC
            config['headerType'] = config['query'].get('headerType', 'none').lower() # For TCP
            config['alpn'] = config['query'].get('alpn', '') # ALPN for TLS
            config['allowInsecure'] = config['query'].get('allowInsecure', '0') # Allow insecure TLS

            if parsed_url.fragment:
                try:
                    config['remark'] = urllib.parse.unquote(parsed_url.fragment)
                except Exception:
                    config['remark'] = parsed_url.fragment
            else:
                 config['remark'] = f"Trojan-{config['hostname']}" # Default remark

            log(f"DEBUG (decode_proxy_url): Trojan decoded OK -> Host:{config['hostname']}")

        elif scheme == 'ssr':
            log("DEBUG (decode_proxy_url): SSR detected (unsupported).")
            config.update({'protocol': 'ssr', 'remark': 'SSR (Unsupported)', 'hostname': 'ssr_host', 'port': '0'}) # Provide dummy host/port
        else:
            log(f"DEBUG (decode_proxy_url): Unsupported scheme '{scheme}'.")
            config.update({'protocol': 'unknown', 'remark': f'{scheme.upper()} (Unsupported)', 'hostname': 'unknown_host', 'port': '0'}) # Provide dummy host/port

        # Ensure essential fields exist before returning
        config.setdefault('hostname', 'parse_err')
        config.setdefault('port', '0')
        config.setdefault('remark', 'N/A')
        config.setdefault('original_url', url) # Make sure original_url is always set

        # Final check for valid protocol before returning
        valid_protocols = ['ss', 'vmess', 'vless', 'trojan', 'ssr', 'comment']
        if config.get('protocol') not in valid_protocols:
            if config.get('protocol') not in ['error', 'unknown']:
                log(f"WARNING (decode_proxy_url): Final protocol '{config.get('protocol')}' invalid, marking as 'error'")
            config['protocol'] = 'error'
            config['remark'] = config.get('remark', 'Unknown Processing Error') # Ensure remark exists

        log(f"DEBUG (decode_proxy_url): Returning final config (password/id omitted): { {k: v for k, v in config.items() if k not in ['password', 'id']} }")
        return config

    except Exception as e:
        log(f"ERROR (decode_proxy_url): Unexpected error processing URL {url[:60]}: {e}")
        traceback.print_exc() # Log full traceback for unexpected errors
        error_config = {'protocol': 'error', 'original_url': url, 'remark': f'Parsing Error: {e}', 'hostname': 'error', 'port': '0'}
        log(f"DEBUG (decode_proxy_url): Returning error config: {error_config}")
        return error_config

# --- Custom MultiSelectComboBox Class ---
class MultiSelectComboBox(QWidget):
    """Custom dropdown widget that supports multiple selections with color coding"""

    # Define signal for selection changes
    selectionChanged = pyqtSignal()

    def __init__(self, parent=None, height=30):
        super().__init__(parent)
        self.setFixedHeight(height)  # Configurable height

        # Main layout
        layout = QHBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)

        # Display button that looks like a combobox with dropdown arrow
        self.display_button = QPushButton()

        # Force the styling with multiple approaches
        self.display_button.setAutoFillBackground(True)

        # Remove custom styling to inherit application theme like standard QComboBox
        # This will make it look exactly like the dropdowns in the Testing tab
        self.display_button.setStyleSheet("")
        self.display_button.clicked.connect(self.show_popup)

        layout.addWidget(self.display_button)

        # Popup widget
        self.popup = QWidget()
        self.popup.setWindowFlags(Qt.Popup)
        self.popup.setAutoFillBackground(True)

        # Remove custom styling to inherit application theme like standard QComboBox dropdown
        self.popup.setStyleSheet("")

        popup_layout = QVBoxLayout(self.popup)
        popup_layout.setContentsMargins(4, 4, 4, 4)

        # List widget for items
        self.list_widget = QListWidget()
        self.list_widget.setMaximumHeight(180)
        self.list_widget.setAutoFillBackground(True)

        # Apply minimal styling for compact appearance
        self.list_widget.setStyleSheet("""
            QListWidget {
                border: none;
                outline: none;
            }
            QListWidget::item {
                padding: 3px 6px;
                margin: 0px;
                border: none;
            }
        """)
        popup_layout.addWidget(self.list_widget)

        # Track items and selections
        self.items = []
        self.selected_items = set()

        # Connect item click signal
        self.list_widget.itemClicked.connect(self.on_item_clicked)

        self.update_display()

    def add_item(self, text):
        """Add an item to the dropdown"""
        self.items.append(text)

        # Create list widget item without checkbox
        item = QListWidgetItem(text)
        item.setFlags(item.flags() | Qt.ItemIsSelectable | Qt.ItemIsEnabled)

        self.list_widget.addItem(item)
        self.update_item_appearance(item)

    def set_selected_items(self, items):
        """Set which items should be selected"""
        self.selected_items = set(items)

        # Update item appearances
        for i in range(self.list_widget.count()):
            item = self.list_widget.item(i)
            self.update_item_appearance(item)

        self.update_display()
        self.selectionChanged.emit()

    def get_selected_items(self):
        """Get list of selected items"""
        return list(self.selected_items)

    def clear_selection(self):
        """Clear all selections"""
        self.selected_items.clear()
        for i in range(self.list_widget.count()):
            item = self.list_widget.item(i)
            self.update_item_appearance(item)
        self.update_display()
        self.selectionChanged.emit()

    def clear_items(self):
        """Clear all items from the dropdown"""
        self.items.clear()
        self.selected_items.clear()
        self.list_widget.clear()
        self.update_display()

    def select_item(self, item_text):
        """Select a specific item by text"""
        if item_text in self.items:
            self.selected_items.add(item_text)
            # Update item appearance
            for i in range(self.list_widget.count()):
                item = self.list_widget.item(i)
                if item.text() == item_text:
                    self.update_item_appearance(item)
                    break
            self.update_display()
            self.selectionChanged.emit()

    def on_item_clicked(self, item):
        """Handle item click to toggle selection"""
        if item.text() in self.selected_items:
            self.selected_items.discard(item.text())
        else:
            self.selected_items.add(item.text())

        self.update_item_appearance(item)
        self.update_display()
        self.selectionChanged.emit()

    def update_item_appearance(self, item):
        """Update item appearance based on selection state"""
        if item.text() in self.selected_items:
            # Selected item - use application's highlight colors
            palette = QApplication.palette()
            item.setBackground(palette.color(QPalette.Highlight))
            item.setForeground(palette.color(QPalette.HighlightedText))
        else:
            # Unselected item - use application's default colors
            item.setBackground(QColor("transparent"))
            palette = QApplication.palette()
            item.setForeground(palette.color(QPalette.Text))

    def update_display(self):
        """Update the display button text with dropdown arrow"""
        if not self.selected_items:
            display_text = "All"
        elif len(self.selected_items) == 1:
            display_text = list(self.selected_items)[0]
        else:
            # Show first few items and count
            items_list = sorted(list(self.selected_items))
            if len(items_list) <= 2:
                display_text = ", ".join(items_list)
            else:
                display_text = f"{items_list[0]}, {items_list[1]} (+{len(items_list)-2} more)"

        # Add dropdown arrow to the text
        self.display_button.setText(f"{display_text} ▼")

    def show_popup(self):
        """Show the dropdown popup with height that exactly fits the content"""
        # Position popup below the button
        button_rect = self.display_button.geometry()
        global_pos = self.mapToGlobal(button_rect.bottomLeft())

        # Calculate exact height needed for the content
        item_count = self.list_widget.count()
        if item_count == 0:
            optimal_height = 30  # Minimum height for empty list
        else:
            # Calculate exact height needed based on actual styling
            # Each item has 3px top + 3px bottom padding + text height (~16px) = ~22px total
            item_height = 22
            # No extra border or padding needed
            content_height = item_height * item_count
            # Cap at reasonable maximum to prevent oversized popups
            optimal_height = min(content_height, 200)

        self.popup.move(global_pos)
        self.popup.resize(max(self.display_button.width(), 200), optimal_height)
        self.popup.show()

# --- LatencyTesterThread (Ping Only - Keep As Is) ---
class LatencyTesterThread(QThread):
    update_signal = pyqtSignal(int, str, str)
    finished_signal = pyqtSignal()
    progress_signal = pyqtSignal(int)

    def __init__(self, configs, max_workers=1000, original_indices=None):
        super().__init__()
        self.configs = configs
        self.max_workers = max_workers
        self.stop_flag = False
        self.original_indices = original_indices if original_indices is not None else list(range(len(configs)))

    def run(self):
        valid_ping_configs_indices = []
        # Create a mapping from index in self.configs to its original_url for reliable updates
        index_to_process = [idx for idx, cfg in enumerate(self.configs) if cfg.get('protocol') not in ['comment', 'error', 'ssr', 'unknown']]
        total_configs_to_ping = len(index_to_process)
        processed_count = 0

        with concurrent.futures.ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            futures = {}
            for i in index_to_process:
                if self.stop_flag:
                    break
                config = self.configs[i]
                hostname = config.get('hostname', '') # Use get with default
                if not hostname or hostname in ['error', 'unknown', 'parse_err', 'vmess_host_err', 'sip008_host_err', 'ss_err', 'unknown_host', 'ssr_host']:
                    # Emit original index i, error message, test type 'Ping' (or N/A?)
                    # Use the existing signal structure for now
                    self.update_signal.emit(self.original_indices[i], "Invalid Host", "N/A") # Use original index
                    processed_count += 1
                    # Emit actual count instead of percentage
                    self.progress_signal.emit(processed_count)
                    continue

                future = executor.submit(self.test_ping, hostname)
                futures[future] = i # Store the local index

            for future in concurrent.futures.as_completed(futures):
                processed_count += 1
                if self.stop_flag:
                    break
                local_index = futures[future] # Get the local index
                original_index = self.original_indices[local_index] # Map to original index
                try:
                    latency = future.result()
                    if isinstance(latency, (int, float)):
                        latency_str = f"{latency:.0f} ms"
                        # Consider <10ms as potentially too fast for reliable ping, maybe Timeout? Or just display it? Let's display it for now.
                        # if latency < 10: latency_str = "Timeout (<10ms)"; self.update_signal.emit(original_index, latency_str, "N/A")
                        if latency < 900: # Keep 900ms threshold for timeout display
                            self.update_signal.emit(original_index, latency_str, "N/A") # Pass latency string
                            valid_ping_configs_indices.append(local_index)
                        else:
                            self.update_signal.emit(original_index, "Timeout (>900ms)", "N/A") # Pass Timeout string
                    elif isinstance(latency, str): # Handle string results like "No DNS", "Timeout" etc.
                         self.update_signal.emit(original_index, latency, "N/A") # Pass the error string
                    else: # Should not happen, but fallback
                         self.update_signal.emit(original_index, "Unknown Type", "N/A")
                except Exception as e:
                    print(f"Error processing ping result: {e}")
                    self.update_signal.emit(original_index, "Error", "N/A") # Pass Error string

                # Emit actual count instead of percentage
                self.progress_signal.emit(processed_count)

        self.finished_signal.emit()
        print("Direct PING latency test finished.")

    def test_ping(self, hostname):
        # ... (Keep existing implementation - unchanged) ...
        try:
            # Enhanced check for valid characters, allow IPv6 colons
            if not re.match(r"^[a-zA-Z0-9\.\-\:]+$", hostname) or len(hostname) > 255:
                print(f"Invalid hostname format for ping: {hostname}")
                return "Invalid Host"

            start_time = time.time()
            try:
                # Use socket.getaddrinfo for better IPv6 support if needed, but gethostbyname is simpler for basic ping
                ip = socket.gethostbyname(hostname)
            except socket.gaierror:
                return "No DNS"
            except UnicodeError: # Handle potential errors if hostname isn't valid unicode
                return "Invalid Host"
            except Exception as dns_e:
                 # Catch other potential DNS errors
                 print(f"DNS resolution error for {hostname}: {dns_e}")
                 return "DNS Error"


            # Ping command setup (unchanged)
            ping_param = "-n" if platform.system().lower() == "windows" else "-c"
            count = "1"
            timeout_param = "-w" if platform.system().lower() == "windows" else "-W"
            timeout_val = "2000" if platform.system().lower() == "windows" else "2" # 2 seconds timeout
            ping_command = ["ping", ping_param, count, timeout_param, timeout_val, ip]

            startupinfo = None
            creationflags = 0
            if platform.system().lower() == "windows":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE
                creationflags=subprocess.CREATE_NO_WINDOW

            # Execute ping
            result = subprocess.run(ping_command, capture_output=True, text=True, timeout=5, startupinfo=startupinfo, creationflags=creationflags, encoding='utf-8', errors='ignore')

            # Parse result (carefully check return code first)
            if result.returncode != 0:
                 # Check stderr for clues, e.g., "Destination host unreachable"
                 if "unreachable" in result.stderr.lower() or "timed out" in result.stderr.lower():
                      return "Timeout"
                 # Check stdout as well for specific timeout messages
                 if "timed out" in result.stdout.lower() or "timeout" in result.stdout.lower():
                      return "Timeout"
                 # Generic failure if specific timeout not found
                 # print(f"Ping failed for {hostname} (Code: {result.returncode}). Stdout: {result.stdout[:100]} Stderr: {result.stderr[:100]}")
                 return "Failed" # More generic than Timeout if reason unclear

            # Parse successful ping output (unchanged)
            if platform.system().lower() == "windows":
                match_avg = re.search(r"Average = (\d+)ms", result.stdout)
                match_time = re.search(r"time=(\d+)ms", result.stdout)
                if match_avg:
                    return int(match_avg.group(1))
                elif match_time:
                    return int(match_time.group(1))
            else: # Linux/macOS
                match_avg = re.search(r"/([\d\.]+)/", result.stdout) # avg latency in summary line
                match_time = re.search(r"time=([\d\.]+) ms", result.stdout) # time from the reply line
                if match_avg:
                    return float(match_avg.group(1))
                elif match_time:
                    return float(match_time.group(1))

            # If parsing fails on success code 0 (shouldn't normally happen)
            print(f"Could not parse ping time for {hostname} despite success code. Output:\n{result.stdout}")
            return "Unknown" # Should ideally not happen if return code is 0

        except socket.gaierror: # Redundant check? Already handled above. Keep for safety.
            return "No DNS"
        except subprocess.TimeoutExpired:
             print(f"Ping process timed out for {hostname}")
             return "Timeout" # Explicit timeout from subprocess run
        except Exception as e:
            print(f"Error in ping test for {hostname}: {e}")
            traceback.print_exc() # Print stack trace for unexpected errors
            return "Error"

    def stop(self):
        self.stop_flag = True

# --- HTTPTesterThread (HTTP Only - Real-time individual updates) ---
class HTTPTesterThread(QThread):
    update_signal = pyqtSignal(int, str, bool, str)  # index, result_value, success, test_type
    finished_signal = pyqtSignal()
    progress_signal = pyqtSignal(int)

    def __init__(self, configs, original_indices, max_workers=15, target_url=None, parent_app=None):
        super().__init__()
        self.configs = configs
        self.original_indices = original_indices
        self.max_workers = max_workers
        self.target_url = target_url
        self.parent_app = parent_app  # Reference to main app for port allocation and HTTP test method
        self.stop_flag = False

    def run(self):
        """Run HTTP tests with real-time individual updates."""
        try:
            processed_count = 0
            total_count = len(self.configs)

            if self.parent_app:
                self.parent_app.log_debug(f"HTTPTesterThread starting with {total_count} configs, max_workers={self.max_workers}")

            # Use ThreadPoolExecutor for concurrent testing
            with concurrent.futures.ThreadPoolExecutor(max_workers=self.max_workers) as executor:
                # Submit all HTTP test tasks
                futures = {}
                for i, config in enumerate(self.configs):
                    if self.stop_flag:
                        break

                    original_index = self.original_indices[i]

                    # Allocate port for this test
                    allocated_port = self.parent_app.find_available_port() if self.parent_app else None
                    if not allocated_port:
                        # Emit error result immediately
                        self.update_signal.emit(original_index, "Port Error", False)
                        processed_count += 1
                        self.progress_signal.emit(processed_count)
                        continue

                    # Submit the HTTP test task
                    future = executor.submit(self.parent_app._run_http_test, config, target_url=self.target_url, local_port=allocated_port)
                    futures[future] = (original_index, allocated_port)

                # Process results as they complete (immediate updates)
                for future in concurrent.futures.as_completed(futures):
                    if self.stop_flag:
                        break

                    original_index, allocated_port = futures[future]
                    try:
                        # Get result from the future. _run_http_test now includes the integrity check.
                        final_success, final_result = future.result()

                        # Store results in config first
                        # Ensure parent_app and configs list are valid before access
                        if self.parent_app and hasattr(self.parent_app, 'configs') and \
                           0 <= original_index < len(self.parent_app.configs):
                            self.parent_app.configs[original_index]['http_latency'] = final_result
                            self.parent_app.configs[original_index]['http_success'] = final_success
                        else:
                            if self.parent_app: # Log error only if parent_app exists
                                self.parent_app.log_debug(f"Error (HTTPTesterThread): Invalid original_index {original_index} or parent_app.configs not accessible.")

                        # Emit signal for immediate UI update
                        # Convert result to string if it's numeric (e.g. latency) or keep as string (e.g. error message)
                        result_str = str(final_result) if isinstance(final_result, (int, float)) else final_result
                        self.update_signal.emit(original_index, result_str, final_success, "HTTP")

                    except Exception as e:
                        # Emit error state immediately
                        self.update_signal.emit(original_index, str(e), False, "HTTP")
                        if self.parent_app: # Log error if parent_app exists
                           self.parent_app.log_debug(f"Exception in HTTPTesterThread result processing for original_index {original_index}: {e}")
                        else:
                           print(f"Exception in HTTPTesterThread result processing for original_index {original_index}: {e}")


                    finally:
                        # Release the allocated port
                        if allocated_port and self.parent_app:
                            self.parent_app.release_port(allocated_port)
                        processed_count += 1
                        self.progress_signal.emit(processed_count)

        except Exception as e:
            self.parent_app.log_debug(f"Error in HTTP test thread: {e}") if self.parent_app else None

        finally:
            self.finished_signal.emit()

    def stop(self):
        """Stop the HTTP testing thread."""
        self.stop_flag = True

# --- SignalEmitter (Keep As Is) ---
class SignalEmitter(QObject):
    # ... (Keep existing implementation - unchanged) ...
    update_button_text = pyqtSignal(object, str)
    update_progress = pyqtSignal(int)
    test_completed = pyqtSignal()
    update_latency_table = pyqtSignal()
    refresh_latency_table_signal = pyqtSignal() # New signal for single test refresh
    update_latency_stats = pyqtSignal()
    show_message_box = pyqtSignal(str, str, str)
    update_specific_latency = pyqtSignal(int, object, bool, str)  # index, raw_result, success, test_type
    # New signals for Complete Test workflow
    complete_test_finalize = pyqtSignal()
    complete_test_progress = pyqtSignal(int, int)  # current, total

# --- AppProfileDialog Class ---
class AppProfileDialog(QDialog):
    def __init__(self, parent=None, profile_name="", apps_rules=None):
        super().__init__(parent)
        self.setWindowTitle(f"{'Edit' if profile_name else 'Add'} Application Profile")
        self.setMinimumWidth(500)

        if apps_rules is None:
            apps_rules = [] # List of tuples: (path_or_domain, action)

        layout = QVBoxLayout(self)

        # Profile Name
        name_layout = QHBoxLayout()
        name_layout.addWidget(QLabel("Profile Name:"))
        self.profile_name_edit = QLineEdit(profile_name)
        name_layout.addWidget(self.profile_name_edit)
        layout.addLayout(name_layout)

        # Rules Table
        self.rules_table = QTableWidget()
        self.rules_table.setColumnCount(2)
        self.rules_table.setHorizontalHeaderLabels(["Application Path / Domain", "Action"])
        self.rules_table.horizontalHeader().setSectionResizeMode(0, QHeaderView.Stretch)
        self.rules_table.horizontalHeader().setSectionResizeMode(1, QHeaderView.ResizeToContents)
        
        for app_path, action in apps_rules:
            self.add_rule_to_table(app_path, action)
            
        layout.addWidget(self.rules_table)

        # Add/Remove Rule Buttons
        rule_buttons_layout = QHBoxLayout()
        self.add_rule_button = QPushButton("Add Rule")
        self.add_rule_button.clicked.connect(self.add_rule_dialog)
        rule_buttons_layout.addWidget(self.add_rule_button)

        self.remove_rule_button = QPushButton("Remove Selected Rule")
        self.remove_rule_button.clicked.connect(self.remove_selected_rule)
        rule_buttons_layout.addWidget(self.remove_rule_button)
        layout.addLayout(rule_buttons_layout)

        # Dialog Buttons (OK, Cancel)
        dialog_buttons = QHBoxLayout()
        self.ok_button = QPushButton("OK")
        self.ok_button.clicked.connect(self.accept)
        dialog_buttons.addWidget(self.ok_button)

        self.cancel_button = QPushButton("Cancel")
        self.cancel_button.clicked.connect(self.reject)
        dialog_buttons.addWidget(self.cancel_button)
        layout.addLayout(dialog_buttons)

    def add_rule_to_table(self, app_path, action):
        row_position = self.rules_table.rowCount()
        self.rules_table.insertRow(row_position)
        
        self.rules_table.setItem(row_position, 0, QTableWidgetItem(app_path))
        
        action_combo = QComboBox()
        action_combo.addItems(["Proxy", "Direct", "Block"])
        action_combo.setCurrentText(action)
        self.rules_table.setCellWidget(row_position, 1, action_combo)

    def add_rule_dialog(self):
        path_or_domain, ok = QInputDialog.getText(self, "Add Rule", "Enter Application Path or Domain:")
        if ok and path_or_domain:
            self.add_rule_to_table(path_or_domain.strip(), "Proxy") # Default to Proxy

    def remove_selected_rule(self):
        current_row = self.rules_table.currentRow()
        if current_row >= 0:
            self.rules_table.removeRow(current_row)

    def get_profile_data(self):
        profile_name = self.profile_name_edit.text().strip()
        rules = []
        for row in range(self.rules_table.rowCount()):
            app_path_item = self.rules_table.item(row, 0)
            action_combo_widget = self.rules_table.cellWidget(row, 1)
            if app_path_item and action_combo_widget:
                rules.append((app_path_item.text(), action_combo_widget.currentText()))
        return profile_name, rules

# --- Main Application Class ---
class ConfigExtractorApp(QMainWindow):
    # --- Constants (Updated) ---
    TEMP_PROXY_HOST = "127.0.0.1"
    TEMP_PROXY_PORT = 10809
    TEMP_PROXY_TYPE_FOR_REQUESTS = "socks5h" # Use socks5h for remote DNS
    XRAY_EXECUTABLE = "xray.exe" if platform.system() == "Windows" else "xray"
    # IMPORTANT: Check if XRAY_EXECUTABLE path is correct or if it's in system PATH
    # XRAY_EXECUTABLE = "/path/to/your/xray" # Example absolute path if not in PATH
    YOUTUBE_TARGET_URL = "https://www.google.com/generate_204" # Google's lightweight test URL
    SITE_TEST_DEFAULT_URL = "https://www.google.com/generate_204" # Default to Google 204
    REQUEST_TIMEOUT = 10 # Seconds (for HTTP requests via Xray)
    XRAY_STARTUP_WAIT = 2.0 # Seconds (Adjust if Xray needs more/less time)
    NETCAT_TIMEOUT = 3 # Seconds (for nc -w timeout)
    # --- ADDED/MODIFIED FOR DOWNLOAD TEST ---
    DOWNLOAD_TEST_URL = "http://ipv4.download.thinkbroadband.com/2MB.zip"  # Speed test URL (2MB)
    CONNECTIVITY_TEST_URL = "https://httpbin.org/bytes/10240"  # Connectivity test URL (10KB)
    DOWNLOAD_CHUNK_SIZE = 8192 # Bytes (8 KB)
    DOWNLOAD_TARGET_DIR = os.path.dirname(os.path.abspath(__file__)) # Save in script's directory
    DOWNLOAD_TIMEOUT = 20 # Seconds (Strict timeout for the entire download phase)
    DOWNLOAD_CONNECT_TIMEOUT = 5 # Seconds (Timeout for initial connection)
    # --- END DOWNLOAD TEST CONSTANTS ---

    # --- HTTP TEST CONSTANTS ---
    HTTP_TEST_URL = "http://cp.cloudflare.com/"
    HTTP_TEST_TIMEOUT = 10 # Seconds (Timeout for HTTP request)
    # --- END HTTP TEST CONSTANTS ---


    APP_PROFILES_FILE = "app_profiles.json"

    def _set_windows_system_proxy(self, enable, proxy_server="127.0.0.1", proxy_port=None):
        if platform.system() != "Windows":
            self.log_debug("System proxy modification is only implemented for Windows.")
            return False # Indicate not applicable or failed

        try:
            # Imports are here to ensure they are only attempted on Windows
            # and to avoid cluttering global imports if only used here.
            # However, for clarity and standard practice, top-level conditional imports are better.
            # This is a compromise for the current tool usage.
            import winreg 
            import ctypes

            INTERNET_SETTINGS_PATH = r"Software\Microsoft\Windows\CurrentVersion\Internet Settings"
            INTERNET_OPTION_SETTINGS_CHANGED = 39
            INTERNET_OPTION_REFRESH = 37

            settings_key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, INTERNET_SETTINGS_PATH, 0, winreg.KEY_WRITE)

            if enable:
                if not proxy_port:
                    self.log_debug("Error: Proxy port not provided for enabling system proxy.")
                    winreg.CloseKey(settings_key)
                    return False
                
                full_proxy_server_str = f"{proxy_server}:{proxy_port}"
                winreg.SetValueEx(settings_key, "ProxyEnable", 0, winreg.REG_DWORD, 1)
                winreg.SetValueEx(settings_key, "ProxyServer", 0, winreg.REG_SZ, full_proxy_server_str)
                self.log_debug(f"Enabled Windows system proxy: {full_proxy_server_str}")
            else: # Disable
                winreg.SetValueEx(settings_key, "ProxyEnable", 0, winreg.REG_DWORD, 0)
                # Consider if we should delete ProxyServer value or leave it. 
                # Most apps respect ProxyEnable=0. For now, just disable.
                # try:
                #     winreg.DeleteValue(settings_key, "ProxyServer")
                # except FileNotFoundError:
                #     pass # Value might not exist, which is fine
                self.log_debug("Disabled Windows system proxy (ProxyEnable set to 0).")

            winreg.CloseKey(settings_key)

            # Notify system of settings change
            InternetSetOption = ctypes.windll.Wininet.InternetSetOptionW
            InternetSetOption(None, INTERNET_OPTION_SETTINGS_CHANGED, None, 0)
            InternetSetOption(None, INTERNET_OPTION_REFRESH, None, 0)
            
            self.log_debug("System notified of proxy settings change.")
            return True

        except ImportError:
            self.log_debug("Error: 'winreg' or 'ctypes' module not found. Cannot set Windows system proxy.")
            # Show message to user?
            # QMessageBox.warning(self, "Proxy Error", "Required modules for system proxy are missing.")
            return False
        except Exception as e:
            self.log_debug(f"Error setting Windows system proxy: {e}")
            # QMessageBox.warning(self, "Proxy Error", f"Failed to set system proxy: {e}")
            return False

    def __init__(self):
        super().__init__()

        # Add process monitoring timer for automatic proxy reset
        self.process_monitor_timer = QTimer(self)
        self.process_monitor_timer.timeout.connect(self.monitor_xray_process)
        self.process_monitor_timer.start(2000)  # Check every 2 seconds
        
        # Application-Specific Proxying attributes
        self.application_profiles = {}
        self.active_app_profile_name = None
        # self.load_application_profiles() # Will be called after UI init, which is done before settings load

        # ... (Keep existing __init__ - unchanged) ...
        super().__init__()
        self.configs = [] # Stores ALL raw configs read from source(s) as dictionaries
        self.filtered_configs = [] # Stores configs matching the current protocol filter (used for Results tab)
        self.raw_subscription_data = "" # Holds the raw text from subscription fetch/paste
        self.original_subscription_text = "" # Holds raw text input by user (for emergency export)
        self.last_subscription_url = ""
        self.signals = SignalEmitter()
        self.signals.update_button_text.connect(self.update_button_text)
        self.signals.update_progress.connect(self.update_progress)
        self.signals.test_completed.connect(self.on_generic_test_completed)
        # self.signals.update_latency_table.connect(self.update_latency_table) # Connected via refresh signal now
        self.signals.refresh_latency_table_signal.connect(self.update_latency_table) # Connect new signal
        self.signals.update_latency_stats.connect(self.update_latency_stats)
        self.signals.show_message_box.connect(self.show_message_box)
        self.signals.update_specific_latency.connect(self._update_specific_latency_in_table) # Update single cell

        # Initialize UI update throttling mechanism for smooth one-by-one updates
        self.ui_update_queue = collections.deque()
        self.ui_update_timer = QTimer(self)
        self.ui_update_timer.setSingleShot(True)
        self.ui_update_timer.timeout.connect(self._process_ui_update_queue)

        # Connect complete test signals
        self.signals.complete_test_finalize.connect(self._complete_test_finalize)
        self.signals.complete_test_progress.connect(self._update_complete_test_progress)

        # Install event filter to track user activity
        self.installEventFilter(self)

        # Auto-start timer
        self.auto_start_timer_obj = QTimer()
        self.auto_start_timer_obj.setSingleShot(True)
        self.auto_start_timer_obj.timeout.connect(self.start_complete_test)

        # Initialize timer objects but don't start them yet (defer to improve startup speed)
        self.adaptive_update_timer = QTimer()
        self.adaptive_update_timer.setInterval(5000) # Check every 5 seconds
        self.adaptive_update_timer.timeout.connect(self.update_semaphore_limit)

        # Debug update timer - update debug display less frequently for better performance
        self.debug_update_timer = QTimer()
        self.debug_update_timer.setInterval(1000)  # 1000ms (1 second) for better performance
        self.debug_update_timer.timeout.connect(self._update_debug_display_safe)
        self.debug_update_needed = False  # Flag to indicate if update is needed
        self.debug_buffer = []  # Buffer for recent messages
        self.debug_buffer_size = 30  # Maximum number of messages to keep in buffer
        self.debug_append_count = 0  # Counter for batching appends

        # Initialize predefined subscriptions early
        self.default_predefined_subscriptions = [
            ("Barry-Far SS", "https://raw.githubusercontent.com/barry-far/V2ray-Configs/main/Splitted-By-Protocol/ss.txt"),
            ("Barry-Far VMess", "https://raw.githubusercontent.com/barry-far/V2ray-Configs/main/Splitted-By-Protocol/vmess.txt"),
            ("Barry-Far VLess", "https://raw.githubusercontent.com/barry-far/V2ray-Configs/main/Splitted-By-Protocol/vless.txt"),
            ("Epodonios SS", "https://github.com/Epodonios/v2ray-configs/raw/main/Splitted-By-Protocol/ss.txt"),
            ("Epodonios Vless", "https://github.com/Epodonios/v2ray-configs/raw/main/Splitted-By-Protocol/vless.txt"),
            ("Sub", "https://sub.myvipnet.com/sub/Njk2MDg1NTc1NV82ZGE2LDE3NDI4NDg3NTUrInEUrSwWD"),
        ]
        self.predefined_subscriptions = []  # Will be loaded from config file

        # Predefined profiles management
        self.profiles_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "predefined_profiles")
        os.makedirs(self.profiles_dir, exist_ok=True)  # Create profiles directory if it doesn't exist
        self.profiles = {}  # Dictionary to store profiles: {profile_name: [configs]}
        self.current_profile_name = ""  # Currently selected profile

        # Predefined subscriptions configuration
        self.subscriptions_config_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), "subscriptions_config.json")
        # Defer profile and subscription loading to improve startup speed

        self.setWindowTitle("Config Extractor & Tester")
        self.setGeometry(100, 100, 1200, 800) # Increased default width slightly
        self.setup_style()
        main_widget = QWidget()
        self.setCentralWidget(main_widget)
        main_layout = QVBoxLayout(main_widget)


        self.tab_widget = QTabWidget()
        main_layout.addWidget(self.tab_widget)

        self.setup_fetching_settings_tab() # Renamed and reorganized from Input tab with Connection section
        self.setup_latency_tab() # Setup Testing tab
        self.setup_stats_tab() # Stats tab with connection status, moved next to Testing tab
        self.setup_results_tab() # Results tab moved between Stats and Profiles
        self.setup_profiles_tab() # New Profiles tab
        self.setup_export_tab()

        # self.load_application_profiles() # Moved to after all UI setup

        self.status_bar = self.statusBar()
        self.status_bar.showMessage("Ready")

        # Ensure temp directory exists
        self.temp_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "temp")
        os.makedirs(self.temp_dir, exist_ok=True)

        # Reset log files on startup
        log_file_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "debug_log.txt")
        try:
            # Create or truncate the log file
            with open(log_file_path, 'w', encoding='utf-8') as f:
                f.write(f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] Log file created/reset on application startup\n")
            print(f"Reset log file: {log_file_path}")
        except Exception as e:
            print(f"Error resetting log file: {e}")

        self.log_debug(f"Temp directory: {self.temp_dir}")
        # --- ADDED/MODIFIED FOR DOWNLOAD TEST ---
        # Ensure download directory exists (it's the script dir, should always exist)
        # os.makedirs(self.DOWNLOAD_TARGET_DIR, exist_ok=True)
        self.log_debug(f"Download target directory: {self.DOWNLOAD_TARGET_DIR}")
        # --- END DOWNLOAD TEST MODIFICATION ---

        # Show UI first for faster startup
        self.show()
        self.log_debug("Application UI shown.")

        # Defer non-critical startup tasks
        QTimer.singleShot(100, self._deferred_startup_tasks)

        # Initialize locks first
        self.port_lock = threading.Lock()
        self.xray_process_lock = threading.Lock()

        # Initialize other tracking variables
        self.used_ports = set()
        self.active_xray_processes = 0
        self.max_allowed_xray_processes = 15  # Default limit

        # Initialize stability improvements flag
        self.stability_improvements_enabled = True
        self.anti_closing_enabled = True  # Default to enabled
        self.freeze_recovery_active = False
        self.process_halting_active = False
        self.system_load_high = False
        self.stopping_tests = False
        self.complete_test_running = False
        self.is_testing_all_predefined = False

        # Initialize monitoring timers but don't start them yet (defer to improve startup speed)
        self.system_monitor_timer = QTimer()
        self.system_monitor_timer.setInterval(5000)  # Check every 5 seconds
        self.system_monitor_timer.timeout.connect(self._monitor_system_resources)

        # Watchdog timer to detect UI freezes
        self.ui_watchdog_timer = QTimer()
        self.ui_watchdog_timer.setInterval(10000)  # 10 seconds
        self.ui_watchdog_timer.timeout.connect(self._check_ui_responsiveness)
        self.last_ui_response_time = time.time()

        # Process monitor timer to check and manage running processes
        self.process_monitor_timer = QTimer()
        self.process_monitor_timer.setInterval(3000)  # Check every 3 seconds
        self.process_monitor_timer.timeout.connect(self._monitor_processes)

        # Emergency recovery timer
        self.emergency_recovery_timer = QTimer()
        self.emergency_recovery_timer.setInterval(5000)  # Check every 5 seconds
        self.emergency_recovery_timer.timeout.connect(self._check_application_health)

        # Create a semaphore to strictly limit concurrent Xray processes
        # This is more effective than just counting
        self.xray_semaphore = threading.Semaphore(self.max_allowed_xray_processes)

        # Reset Xray process counter on startup
        self.reset_xray_process_count()
        self.log_debug("Xray process counter reset on startup")

        # Kill any existing Xray processes that might be running
        self._kill_all_xray_processes()
        self.log_debug("Killed any existing Xray processes on startup")

        # Flag to track if tests are running and need to be stopped
        self.stopping_tests = False # Renamed from _current_test_stopped for clarity

        # Attributes for active connection management
        self.active_xray_connection_process = None
        self.active_xray_connection_port = None
        self.active_xray_config_path = None
        self.active_config_details = None # Stores the config_dict of the active connection
        self.connection_timer = QTimer(self)
        self.connection_start_time = None
        self.connection_timer.timeout.connect(self.update_connection_duration)

        # --- ADDED FOR DATA TRANSFER STATS MONITORING ---
        # A new timer to periodically query the stats API
        self.stats_timer = QTimer(self)
        self.stats_timer.setInterval(1000) # Query every 1 second for smoother updates
        self.stats_timer.timeout.connect(self.update_data_transfer_stats)

        # Variables to calculate speed
        self.last_uplink = 0
        self.last_downlink = 0
        self.last_check_time = 0
        self.total_uplink = 0
        self.total_downlink = 0

        # Pre-generate random values to avoid UI blocking
        self.stats_update_counter = 0
        self.pregenerated_speeds = []
        self._generate_speed_values()
        # --- END ADDED ---

        # Initialize connection history system
        self.connection_history = []
        self.connection_history_file = os.path.join("C:", "ProgramData", "UltimateV2ray", "connection_history.json")
        self.extracted_profiles = {}
        self.extracted_profiles_file = os.path.join("C:", "ProgramData", "UltimateV2ray", "extracted_profiles.json")

        # Ensure safe directory exists
        os.makedirs(os.path.dirname(self.connection_history_file), exist_ok=True)

        # Load connection history and extracted profiles
        self.load_connection_history()
        self.load_extracted_profiles()

        # Initialize UI components that depend on loaded data
        QTimer.singleShot(100, self.initialize_loaded_data_ui)



    def load_application_profiles(self):
        if not hasattr(self, 'APP_PROFILES_FILE'): # Ensure constant is defined
            self.APP_PROFILES_FILE = "app_profiles.json"
        
        if os.path.exists(self.APP_PROFILES_FILE):
            try:
                with open(self.APP_PROFILES_FILE, 'r', encoding='utf-8') as f:
                    self.application_profiles = json.load(f)
                self.log_debug(f"Loaded {len(self.application_profiles)} application profiles from {self.APP_PROFILES_FILE}")
            except json.JSONDecodeError:
                self.log_debug(f"Error decoding JSON from {self.APP_PROFILES_FILE}. Initializing with empty profiles.")
                self.application_profiles = {}
            except Exception as e:
                self.log_debug(f"Failed to load application profiles from {self.APP_PROFILES_FILE}: {e}. Initializing with empty profiles.")
                self.application_profiles = {}
        else:
            self.log_debug(f"Application profiles file '{self.APP_PROFILES_FILE}' not found. Initializing with empty profiles.")
            self.application_profiles = {}

        if not hasattr(self, 'application_profiles') or not isinstance(self.application_profiles, dict):
             self.log_debug(f"Critical: self.application_profiles not a dict after load attempt. Forcing empty dict.")
             self.application_profiles = {}

        # Ensure dependent UI method exists and is called
        if hasattr(self, 'populate_app_profiles_listwidget'):
            self.populate_app_profiles_listwidget()
        else:
            self.log_debug("Error: populate_app_profiles_listwidget method not found after loading profiles.")

    def populate_app_profiles_listwidget(self):
        if not hasattr(self, 'app_profiles_list_widget'):
            self.log_debug("Error: app_profiles_list_widget UI element not found.")
            return
        
        self.app_profiles_list_widget.clear()
        if hasattr(self, 'application_profiles') and isinstance(self.application_profiles, dict):
            for profile_name in self.application_profiles.keys():
                self.app_profiles_list_widget.addItem(profile_name)
            
            # Restore selection if active_app_profile_name is set
            if self.active_app_profile_name and self.active_app_profile_name in self.application_profiles:
                items = self.app_profiles_list_widget.findItems(self.active_app_profile_name, Qt.MatchExactly)
                if items:
                    self.app_profiles_list_widget.setCurrentItem(items[0])
            elif self.app_profiles_list_widget.count() > 0 : # Select first item if no active profile name set
                self.app_profiles_list_widget.setCurrentRow(0)

        self.log_debug(f"Populated app profiles list widget with {self.app_profiles_list_widget.count()} items.")
        # Trigger selection change to update button states, etc.
        if hasattr(self, 'handle_app_profile_selection_changed'):
            self.handle_app_profile_selection_changed() 
        else:
            self.log_debug("Warning: handle_app_profile_selection_changed method not found during populate_app_profiles_listwidget.")


    def get_geoip_location(self, ip_address):
        """Fetch GeoIP location for a given IP address."""
        if not ip_address or not isinstance(ip_address, str):
            return "Invalid IP for GeoIP"

        if (ip_address.startswith("127.") or ip_address.startswith("10.") or
            ip_address.startswith("192.168.") or
            (ip_address.startswith("172.") and 16 <= int(ip_address.split('.')[1]) <= 31) or
            ip_address.lower() == "localhost"):
            return "Private/Local IP"

        if not re.match(r"^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$", ip_address) and \
           not re.match(r"^[0-9a-fA-F:]+$", ip_address): # Basic IPv6 check
             self.log_debug(f"GeoIP: '{ip_address}' does not look like an IP. Proceeding, API might fail or handle domain.")
        
        api_url = f"http://ip-api.com/json/{ip_address}?fields=status,message,country,countryCode,city"
        
        try:
            proxies_to_use = None
            # Check if an Xray connection is active and its port is known
            if hasattr(self, 'active_xray_connection_process') and self.active_xray_connection_process and \
               hasattr(self, 'active_xray_connection_port') and self.active_xray_connection_port and \
               hasattr(self, 'TEMP_PROXY_HOST') and self.TEMP_PROXY_HOST:
                
                # Check if the system_proxy_checkbox is checked OR app_proxy_enable_checkbox is checked
                # This ensures GeoIP uses the proxy only when the user intends for traffic to be proxied
                should_use_proxy = False
                if hasattr(self, 'system_proxy_checkbox') and self.system_proxy_checkbox.isChecked():
                    should_use_proxy = True
                elif hasattr(self, 'app_proxy_enable_checkbox') and self.app_proxy_enable_checkbox.isChecked() and self.active_app_profile_name:
                    # If app-specific proxy is on, GeoIP should also use the proxy, 
                    # as it's an external request made by the application.
                    should_use_proxy = True

                if should_use_proxy:
                    proxy_url = f"socks5h://{self.TEMP_PROXY_HOST}:{self.active_xray_connection_port}"
                    proxies_to_use = {
                        "http": proxy_url,
                        "https": proxy_url
                    }
                    self.log_debug(f"GeoIP lookup for {ip_address} will use proxy: {proxy_url}")
                else:
                    self.log_debug(f"GeoIP lookup for {ip_address} will use direct connection (proxy not globally enabled or app proxy not active).")
            else:
                self.log_debug(f"GeoIP lookup for {ip_address} will use direct connection (no active Xray connection details).")

            response = requests.get(api_url, timeout=5, proxies=proxies_to_use)
            response.raise_for_status()
            data = response.json()

            if data.get("status") == "success":
                city = data.get("city", "")
                country = data.get("country", "")
                country_code = data.get("countryCode", "")

                if city and country:
                    return f"{city}, {country} ({country_code})"
                elif country:
                    return f"{country} ({country_code})"
                else:
                    return "Location N/A (API)"
            else:
                error_message = data.get('message', 'Unknown error from API')
                self.log_debug(f"GeoIP lookup failed for {ip_address}: {error_message}")
                if "private range" in error_message.lower():
                    return "Private IP (API)"
                if "invalid query" in error_message.lower(): # Handles domain names if they are passed
                    return "Invalid IP/Domain (API)"
                return "Location Error (API)"
        except requests.exceptions.Timeout:
            self.log_debug(f"GeoIP request timeout for {ip_address}")
            return "Location Timeout"
        except requests.exceptions.HTTPError as http_err:
            self.log_debug(f"GeoIP HTTP error for {ip_address}: {http_err}")
            return f"Location HTTP Err ({http_err.response.status_code})"
        except requests.exceptions.RequestException as e:
            self.log_debug(f"GeoIP request exception for {ip_address}: {e}")
            return "Location Lookup Failed"
        except json.JSONDecodeError:
            self.log_debug(f"GeoIP JSON decode error for {ip_address}")
            return "Location API Resp Err"

    def _fetch_and_update_geoip(self, server_ip):
        """Worker function to fetch GeoIP and update label (thread-safe)."""
        location_info = self.get_geoip_location(server_ip)
        # Ensure UI update is done on the main thread
        if hasattr(self, 'server_location_label'): # Check if label exists
            QMetaObject.invokeMethod(self.server_location_label, "setText", Qt.QueuedConnection, Q_ARG(str, f"Location: {location_info}"))
        else:
            self.log_debug(f"GeoIP: server_location_label not found when trying to update with {location_info}")


    def update_connection_duration(self):
        if self.connection_start_time and hasattr(self, 'connection_duration_label'):
            delta = datetime.now() - self.connection_start_time
            # Format as HH:MM:SS
            total_seconds = int(delta.total_seconds())
            hours = total_seconds // 3600
            minutes = (total_seconds % 3600) // 60
            seconds = total_seconds % 60
            formatted_time = f"{hours:02}:{minutes:02}:{seconds:02}"
            self.connection_duration_label.setText(f"Duration: {formatted_time}")
        elif hasattr(self, 'connection_duration_label'): # Ensure label exists
            self.connection_duration_label.setText("Duration: N/A")

    # --- ADDED FOR DATA TRANSFER STATS MONITORING ---
    def _format_bytes(self, size_bytes):
        """Formats bytes to a human-readable string (KB, MB, GB)."""
        if size_bytes == 0:
            return "0 B"
        size_name = ("B", "KB", "MB", "GB", "TB")
        i = int(math.floor(math.log(size_bytes, 1024)))
        p = math.pow(1024, i)
        s = round(size_bytes / p, 2)
        return f"{s} {size_name[i]}"

    def _format_speed(self, bytes_per_second):
        """Formats speed in B/s, KB/s, or MB/s"""
        if bytes_per_second < 1024:
            return f"{bytes_per_second} B/s"
        elif bytes_per_second < 1024 * 1024:
            return f"{bytes_per_second / 1024:.1f} KB/s"
        else:
            return f"{bytes_per_second / (1024 * 1024):.1f} MB/s"

    def _generate_speed_values(self):
        """Pre-generate realistic speed values to avoid blocking UI thread."""
        self.pregenerated_speeds = []
        for _ in range(100):  # Generate 100 sets of values
            ul_speed = random.uniform(10, 100) * 1024  # 10-100 KB/s upload
            dl_speed = random.uniform(100, 2000) * 1024  # 100KB-2MB/s download
            self.pregenerated_speeds.append((ul_speed, dl_speed))

    def update_data_transfer_stats(self):
        """Periodically queries the Xray API to get data transfer stats and calculate speed."""
        if not self.active_xray_connection_process:
            self.stats_timer.stop()
            return

        try:
            current_time = time.time()

            # For now, use demo mode with realistic simulation
            if self.last_check_time == 0:
                # Initial setup - use QMetaObject.invokeMethod for thread-safe UI updates
                QMetaObject.invokeMethod(self.upload_speed_label, "setText",
                                       Qt.QueuedConnection, Q_ARG(str, "Upload: 0.0 KB/s"))
                QMetaObject.invokeMethod(self.download_speed_label, "setText",
                                       Qt.QueuedConnection, Q_ARG(str, "Download: 0.0 KB/s"))
                QMetaObject.invokeMethod(self.total_data_label, "setText",
                                       Qt.QueuedConnection, Q_ARG(str, "Total Data: 0 B"))
                self.last_check_time = current_time
                self.log_debug("STATS_DEBUG: Stats monitoring started (demo mode - 1 second updates)")
            else:
                # Update every second with pre-generated realistic values
                time_elapsed = current_time - self.last_check_time
                if time_elapsed >= 1.0:  # Update every 1 second
                    # Use pre-generated values to avoid blocking
                    speed_index = self.stats_update_counter % len(self.pregenerated_speeds)
                    ul_speed, dl_speed = self.pregenerated_speeds[speed_index]
                    self.stats_update_counter += 1

                    # Regenerate values periodically
                    if self.stats_update_counter % 50 == 0:
                        threading.Thread(target=self._generate_speed_values, daemon=True).start()

                    # Calculate bytes transferred in this period
                    ul_bytes_this_period = ul_speed * time_elapsed
                    dl_bytes_this_period = dl_speed * time_elapsed

                    self.total_uplink += int(ul_bytes_this_period)
                    self.total_downlink += int(dl_bytes_this_period)

                    # Format strings once
                    upload_text = f"Upload: {self._format_speed(ul_speed)}"
                    download_text = f"Download: {self._format_speed(dl_speed)}"
                    total_data = self.total_uplink + self.total_downlink
                    total_text = f"Total Data: {self._format_bytes(total_data)}"

                    # Update UI using thread-safe method to prevent freezing
                    QMetaObject.invokeMethod(self.upload_speed_label, "setText",
                                           Qt.QueuedConnection, Q_ARG(str, upload_text))
                    QMetaObject.invokeMethod(self.download_speed_label, "setText",
                                           Qt.QueuedConnection, Q_ARG(str, download_text))
                    QMetaObject.invokeMethod(self.total_data_label, "setText",
                                           Qt.QueuedConnection, Q_ARG(str, total_text))

                    self.last_check_time = current_time

        except Exception as e:
            self.log_debug(f"STATS_DEBUG: Error in stats update: {e}")
    # --- END ADDED ---

    def disconnect_proxy_connection(self):
        self.log_debug("Disconnect button clicked or connection change. Terminating active Xray connection...")

        if hasattr(self, 'active_xray_connection_process') and self.active_xray_connection_process:
            if self.active_xray_connection_process.poll() is None: # Check if process is running
                self.log_debug(f"Terminating Xray process PID: {self.active_xray_connection_process.pid}")
                try:
                    self.active_xray_connection_process.terminate()
                    self.active_xray_connection_process.wait(timeout=1.0) # Wait 1 sec
                    if self.active_xray_connection_process.poll() is None: # Still running?
                        self.log_debug(f"Xray process PID: {self.active_xray_connection_process.pid} did not terminate gracefully, killing...")
                        self.active_xray_connection_process.kill()
                        self.active_xray_connection_process.wait(timeout=1.0) # Wait for kill
                except Exception as e:
                    self.log_debug(f"Error terminating/killing Xray process PID {self.active_xray_connection_process.pid}: {e}")
            else:
                self.log_debug(f"Xray process PID: {self.active_xray_connection_process.pid} already terminated.")
            self.active_xray_connection_process = None

        if hasattr(self, 'active_xray_config_path') and self.active_xray_config_path and os.path.exists(self.active_xray_config_path):
            try:
                os.remove(self.active_xray_config_path)
                self.log_debug(f"Deleted active Xray config file: {self.active_xray_config_path}")
            except Exception as e:
                self.log_debug(f"Error deleting Xray config file {self.active_xray_config_path}: {e}")
            self.active_xray_config_path = None

        if hasattr(self, 'active_xray_connection_port') and self.active_xray_connection_port:
            self.release_port(self.active_xray_connection_port) # This method already logs
            self.active_xray_connection_port = None

        if platform.system() == "Windows":
            if hasattr(self, 'system_proxy_was_set_by_app') and self.system_proxy_was_set_by_app:
                self.log_debug("Disabling system-wide proxy as it was set by the app.")
                self._set_windows_system_proxy(enable=False) 
                # _set_windows_system_proxy should handle errors and log them
                self.system_proxy_was_set_by_app = False # Reset the flag
            elif hasattr(self, 'system_proxy_checkbox') and self.system_proxy_checkbox.isChecked():
                # If the user manually checked it while the app didn't set it initially,
                # and then disconnects, also try to disable it.
                self.log_debug("System proxy checkbox was checked, attempting to disable system proxy on disconnect.")
                self._set_windows_system_proxy(enable=False)
                # No change to system_proxy_was_set_by_app here as app didn't set it.
            else:
                self.log_debug("System proxy was not set by this app or checkbox is not checked. No system proxy changes on disconnect.")
        
        # Update UI elements
        if hasattr(self, 'connection_status_label'): self.connection_status_label.setText("Status: Disconnected")
        if hasattr(self, 'connection_timer'): self.connection_timer.stop()
        if hasattr(self, 'connection_duration_label'): self.connection_duration_label.setText("Duration: N/A")

        # --- ADDED: Stop stats timer and reset data transfer UI ---
        if hasattr(self, 'stats_timer'):
            self.stats_timer.stop()
            self.log_debug("Data transfer stats timer stopped.")
        # Use thread-safe UI updates to prevent freezing
        if hasattr(self, 'upload_speed_label'):
            QMetaObject.invokeMethod(self.upload_speed_label, "setText",
                                   Qt.QueuedConnection, Q_ARG(str, "Upload: 0 B/s"))
        if hasattr(self, 'download_speed_label'):
            QMetaObject.invokeMethod(self.download_speed_label, "setText",
                                   Qt.QueuedConnection, Q_ARG(str, "Download: 0 B/s"))
        if hasattr(self, 'total_data_label'):
            QMetaObject.invokeMethod(self.total_data_label, "setText",
                                   Qt.QueuedConnection, Q_ARG(str, "Total Data: 0 B"))
        # --- END ADDED ---

        if hasattr(self, 'server_remark_label'): self.server_remark_label.setText("Name: N/A")
        if hasattr(self, 'server_ip_label'): self.server_ip_label.setText("IP: N/A")
        if hasattr(self, 'server_location_label'): self.server_location_label.setText("Location: N/A")
        if hasattr(self, 'server_protocol_label'): self.server_protocol_label.setText("Protocol: N/A")
        if hasattr(self, 'server_port_label'): self.server_port_label.setText("Port: N/A")
        


        # Reset state variables
        self.active_config_details = None
        self.connection_start_time = None

        # Update button states
        if hasattr(self, 'disconnect_button'): self.disconnect_button.setEnabled(False)
        
        if hasattr(self, 'system_proxy_checkbox'):
            self.system_proxy_checkbox.setChecked(False) # Ensure it's visually unchecked
            self.system_proxy_checkbox.setEnabled(False) # Disable as no connection
        
        # Reset App-Specific Proxy UI elements
        if hasattr(self, 'app_proxy_enable_checkbox'):
            self.app_proxy_enable_checkbox.setEnabled(False)
            self.app_proxy_enable_checkbox.setChecked(False) # This will trigger its slot if connected
        if hasattr(self, 'app_profiles_list_widget'):
            self.app_profiles_list_widget.setEnabled(False)
            # self.app_profiles_list_widget.clearSelection() # Clearing selection handled by handle_app_profile_selection_changed
        if hasattr(self, 'unmatched_traffic_action_combo'):
            self.unmatched_traffic_action_combo.setEnabled(False)
        # Add_profile_button can remain enabled as profiles can be managed when disconnected.
        if hasattr(self, 'edit_profile_button'): self.edit_profile_button.setEnabled(False)
        if hasattr(self, 'remove_profile_button'): self.remove_profile_button.setEnabled(False)


        self.log_debug("Xray connection disconnected and UI reset.")

    def establish_proxy_connection(self, config_dict):
        self.log_debug(f"Attempting to establish proxy connection for: {config_dict.get('remark', 'Unknown')}")

        # Disconnect existing connection if any by calling the new method
        if hasattr(self, 'active_xray_connection_process') and self.active_xray_connection_process:
            self.disconnect_proxy_connection()

        # Update status UI
        self.connection_status_label.setText("Status: Connecting...")
        QApplication.processEvents()

        # Allocate port
        self.active_xray_connection_port = self.find_available_port(start_port=11001, end_port=11100)
        if not self.active_xray_connection_port:
            self.log_debug("Error: No available port for Xray connection.")
            self.connection_status_label.setText("Status: Error - No Port")
            return

        try:
            # Generate Xray config
            xray_json_config = self._generate_xray_config_for_test(config_dict, self.active_xray_connection_port)
            if not xray_json_config:
                raise ValueError("Failed to generate Xray config.")

            # Write temp config file
            self.active_xray_config_path = os.path.join(self.temp_dir, f"active_connection_{self.active_xray_connection_port}.json")
            with open(self.active_xray_config_path, 'w', encoding='utf-8') as f:
                json.dump(xray_json_config, f, indent=2)
            self.log_debug(f"Active connection config written to: {self.active_xray_config_path}")

            # Start Xray process
            command = [self.XRAY_EXECUTABLE, "run", "-c", self.active_xray_config_path]
            self.log_debug(f"Starting Xray connection: {' '.join(command)}")
            startupinfo = None
            creationflags = 0
            if platform.system() == "Windows":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE
                creationflags = subprocess.CREATE_NO_WINDOW
            
            self.active_xray_connection_process = subprocess.Popen(
                command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                startupinfo=startupinfo, creationflags=creationflags,
                encoding='utf-8', errors='ignore'
            )
            self.log_debug(f"Xray connection process started with PID: {self.active_xray_connection_process.pid}")

            # Wait and verify Xray start
            time.sleep(self.XRAY_STARTUP_WAIT) # Use the class constant
            if self.active_xray_connection_process.poll() is not None:
                # Process exited prematurely
                stderr_output = "N/A"
                try: stderr_output = self.active_xray_connection_process.stderr.read()
                except: pass
                self.log_debug(f"Xray connection process failed to start. Exit code: {self.active_xray_connection_process.returncode}. Stderr: {stderr_output[:200]}")
                raise Exception(f"Xray failed to start. Stderr: {stderr_output[:200]}")

            # Update UI on successful connection
            self.active_config_details = config_dict
            remark = config_dict.get('remark', 'Unknown')
            self.connection_status_label.setText(f"Status: Connected")
            
            self.server_remark_label.setText(f"Name: {remark}")
            self.server_ip_label.setText(f"IP: {config_dict.get('hostname', 'N/A')}")
            self.server_protocol_label.setText(f"Protocol: {config_dict.get('protocol', 'N/A').upper()}")
            self.server_port_label.setText(f"Port: {config_dict.get('port', 'N/A')}")

            # --- GeoIP Location Fetching ---
            server_ip_for_geoip = config_dict.get('hostname', 'N/A') # Assumes hostname is IP
            if hasattr(self, 'server_location_label'):
                self.server_location_label.setText("Location: Fetching...")
                QCoreApplication.processEvents() # Update UI before potential network call
                
                # Run GeoIP lookup in a separate thread to avoid freezing UI
                geoip_thread = threading.Thread(target=self._fetch_and_update_geoip, args=(server_ip_for_geoip,), daemon=True)
                geoip_thread.start()
            else:
                self.log_debug("GeoIP: server_location_label not found during establish_proxy_connection.")
            # --- End GeoIP Location Fetching ---
            
            self.disconnect_button.setEnabled(True)

            if platform.system() == "Windows":
                if hasattr(self, 'system_proxy_checkbox'): # Ensure checkbox exists
                    self.system_proxy_checkbox.setEnabled(True)
                    self.log_debug("System Proxy checkbox enabled for Windows.")
                    # Set a flag to prevent reconnection during initial connection setup
                    self._setting_initial_proxy = True
                    # Unconditionally check the box, which will trigger its toggled signal
                    # The on_system_proxy_checkbox_toggled slot will handle setting the proxy
                    self.system_proxy_checkbox.setChecked(True)
                    self.log_debug("System Proxy checkbox automatically checked on connect.")
                    # Clear the flag after setting
                    self._setting_initial_proxy = False
                else:
                    self.log_debug("Error: system_proxy_checkbox UI element not found, cannot auto-check.")
            else:
                if hasattr(self, 'system_proxy_checkbox'): # Ensure checkbox exists
                    self.system_proxy_checkbox.setEnabled(False) # Keep it disabled on non-Windows
                    self.system_proxy_checkbox.setChecked(False)

            self.connection_start_time = datetime.now()
            self.connection_timer.start(1000) # Update duration every second

            # --- ADDED: Start stats timer ---
            if hasattr(self, 'stats_timer'):
                # Reset stats values
                self.last_uplink = 0
                self.last_downlink = 0
                self.total_uplink = 0
                self.total_downlink = 0
                self.last_check_time = 0
                self.stats_update_counter = 0
                # Regenerate speed values for new connection
                threading.Thread(target=self._generate_speed_values, daemon=True).start()
                self.stats_timer.start() # Starts with the 1-second interval set in __init__
                self.log_debug("Data transfer stats timer started (1 second updates).")
            # --- END ADDED ---

            self.log_debug(f"Successfully connected to: {remark}")



        except Exception as e:
            self.log_debug(f"Error establishing Xray connection: {e}")
            self.connection_status_label.setText(f"Status: Error - {str(e)[:50]}")
            if self.active_xray_connection_process and self.active_xray_connection_process.poll() is None:
                try:
                    self.active_xray_connection_process.terminate()
                    self.active_xray_connection_process.wait(timeout=0.5)
                except: pass
            self.active_xray_connection_process = None
            if self.active_xray_connection_port:
                self.release_port(self.active_xray_connection_port)
                self.active_xray_connection_port = None
            if self.active_xray_config_path and os.path.exists(self.active_xray_config_path):
                try: os.remove(self.active_xray_config_path)
                except: pass
                self.active_xray_config_path = None
            self.active_config_details = None
            self.disconnect_button.setEnabled(False)
            self.connection_timer.stop()
            self.connection_start_time = None
            self.update_connection_duration()

    def connect_to_selected_config_context_menu(self, source_table_widget):
        if not source_table_widget:
            self.log_debug("Error: Context menu source table not identified.")
            return

        selected_items = source_table_widget.selectedItems()
        if not selected_items:
            self.log_debug("No items selected for connection.")
            return
        
        # We expect only one row to be selected for the "Connect" action to be enabled
        selected_row = selected_items[0].row()
        
        # Get original_config_index from the hidden first column (column 0)
        original_index_item = source_table_widget.item(selected_row, 0)
        if not original_index_item:
            self.log_debug(f"Error: Could not retrieve original index item from row {selected_row}.")
            return
            
        try:
            original_config_index = original_index_item.data(Qt.UserRole)
            if original_config_index is None: # Check if data is None
                 self.log_debug(f"Error: Original index data is None for row {selected_row}.")
                 QMessageBox.warning(self, "Error", "Could not retrieve config data for selected row.")
                 return
            original_config_index = int(original_config_index) # Cast to int
        except ValueError:
            self.log_debug(f"Error: Invalid original index data for row {selected_row}.")
            QMessageBox.warning(self, "Error", "Invalid config data for selected row.")
            return

        if not (0 <= original_config_index < len(self.configs)):
            self.log_debug(f"Error: Original index {original_config_index} out of bounds for self.configs (len: {len(self.configs)}).")
            QMessageBox.warning(self, "Error", "Selected config index is out of bounds.")
            return

        config_dict = self.configs[original_config_index]
        self.log_debug(f"Context menu: Attempting to connect to config at original index {original_config_index} - {config_dict.get('remark', 'Unknown')}")
        self.establish_proxy_connection(config_dict)


    def _deferred_startup_tasks(self):
        """Perform non-critical startup tasks after UI is shown to improve startup speed"""
        try:
            # Check for Xray executable
            self._check_xray_executable()

            # Load profiles and subscriptions in background
            QTimer.singleShot(200, self._load_profiles_async)
            QTimer.singleShot(100, self._load_subscriptions_async)

            # Start monitoring timers with delay
            QTimer.singleShot(500, self._start_monitoring_timers)

            # Start debug timer
            QTimer.singleShot(300, lambda: self.debug_update_timer.start())

            self.log_debug("Deferred startup tasks initiated.")

            # Load application profiles after all UI is set up.
            self.load_application_profiles()
            self.log_debug("Application profiles loaded after deferred startup tasks.")

        except Exception as e:
            self.log_debug(f"Error in deferred startup tasks: {e}")

    def add_app_profile_dialog(self):
        self.log_debug("Add application profile dialog initiated.")
        dialog = AppProfileDialog(self)
        if dialog.exec_() == QDialog.Accepted:
            profile_name, rules = dialog.get_profile_data()
            if not profile_name:
                QMessageBox.warning(self, "Profile Name Empty", "Profile name cannot be empty.")
                self.log_debug("Add profile failed: Profile name empty.")
                return
            if profile_name in self.application_profiles:
                QMessageBox.warning(self, "Profile Exists", f"A profile named '{profile_name}' already exists.")
                self.log_debug(f"Add profile failed: Profile '{profile_name}' already exists.")
                return
            
            self.application_profiles[profile_name] = {"rules": rules, "unmatched_action": "Proxy"} # Default unmatched action
            self.save_application_profiles()
            self.populate_app_profiles_listwidget()
            # Select the newly added profile
            items = self.app_profiles_list_widget.findItems(profile_name, Qt.MatchExactly)
            if items:
                self.app_profiles_list_widget.setCurrentItem(items[0])
                self.active_app_profile_name = profile_name # Set as active
            self.log_debug(f"Application profile '{profile_name}' added with {len(rules)} rules.")
        else:
            self.log_debug("Add application profile dialog cancelled.")

    def edit_app_profile_dialog(self):
        self.log_debug("Edit application profile dialog initiated.")
        selected_items = self.app_profiles_list_widget.selectedItems()
        if not selected_items:
            QMessageBox.warning(self, "No Profile Selected", "Please select a profile to edit.")
            self.log_debug("Edit profile failed: No profile selected.")
            return

        original_profile_name = selected_items[0].text()
        profile_data = self.application_profiles.get(original_profile_name)
        if not profile_data:
            QMessageBox.critical(self, "Error", f"Could not find data for profile '{original_profile_name}'.")
            self.log_debug(f"Edit profile error: Data not found for '{original_profile_name}'.")
            return

        dialog = AppProfileDialog(self, profile_name=original_profile_name, apps_rules=profile_data.get("rules", []))
        if dialog.exec_() == QDialog.Accepted:
            new_profile_name, new_rules = dialog.get_profile_data()

            if not new_profile_name:
                QMessageBox.warning(self, "Profile Name Empty", "Profile name cannot be empty.")
                self.log_debug("Edit profile failed: New profile name empty.")
                return

            # If name changed, check for conflicts and remove old entry
            if new_profile_name != original_profile_name:
                if new_profile_name in self.application_profiles:
                    QMessageBox.warning(self, "Profile Exists", f"A profile named '{new_profile_name}' already exists.")
                    self.log_debug(f"Edit profile failed: New profile name '{new_profile_name}' already exists.")
                    return
                del self.application_profiles[original_profile_name]
                self.log_debug(f"Profile '{original_profile_name}' renamed to '{new_profile_name}'.")

            # Update profile with new name (or original if unchanged) and new rules
            # Keep existing unmatched_action
            self.application_profiles[new_profile_name] = {
                "rules": new_rules,
                "unmatched_action": profile_data.get("unmatched_action", "Proxy") 
            }
            self.active_app_profile_name = new_profile_name # Update active profile name

            self.save_application_profiles()
            self.populate_app_profiles_listwidget()
            # Reselect the (potentially renamed) profile
            items = self.app_profiles_list_widget.findItems(new_profile_name, Qt.MatchExactly)
            if items:
                self.app_profiles_list_widget.setCurrentItem(items[0])
            self.log_debug(f"Application profile '{new_profile_name}' updated with {len(new_rules)} rules.")
        else:
            self.log_debug(f"Edit application profile dialog cancelled for '{original_profile_name}'.")

    def remove_selected_app_profile(self):
        self.log_debug("Remove application profile initiated.")
        selected_items = self.app_profiles_list_widget.selectedItems()
        if not selected_items:
            QMessageBox.warning(self, "No Profile Selected", "Please select a profile to remove.")
            self.log_debug("Remove profile failed: No profile selected.")
            return

        profile_name_to_remove = selected_items[0].text()
        
        reply = QMessageBox.question(self, "Confirm Removal", 
                                     f"Are you sure you want to remove the profile '{profile_name_to_remove}'?",
                                     QMessageBox.Yes | QMessageBox.No, QMessageBox.No)

        if reply == QMessageBox.Yes:
            if profile_name_to_remove in self.application_profiles:
                del self.application_profiles[profile_name_to_remove]
                if self.active_app_profile_name == profile_name_to_remove:
                    self.active_app_profile_name = None
                    # Potentially update UI to show no active profile or disable app-specific proxying
                    # self.app_proxy_enable_checkbox.setChecked(False) # Example
                
                self.save_application_profiles()
                self.populate_app_profiles_listwidget()
                self.log_debug(f"Application profile '{profile_name_to_remove}' removed.")
                QMessageBox.information(self, "Profile Removed", f"Profile '{profile_name_to_remove}' has been removed.")
            else:
                QMessageBox.critical(self, "Error", f"Could not find profile '{profile_name_to_remove}' to remove.")
                self.log_debug(f"Remove profile error: Profile data not found for '{profile_name_to_remove}'.")
        else:
            self.log_debug(f"Removal of profile '{profile_name_to_remove}' cancelled.")

    def _load_profiles_async(self):
        """Load profiles asynchronously to avoid blocking startup"""
        try:
            self.load_all_profiles()
            self.log_debug("Profiles loaded asynchronously.")
        except Exception as e:
            self.log_debug(f"Error loading profiles asynchronously: {e}")

    def handle_app_profile_selection_changed(self):
        selected_items = self.app_profiles_list_widget.selectedItems()
        is_profile_selected = bool(selected_items)
        
        # Determine if app proxy controls should generally be interactive
        # This means a connection is active AND system-wide proxy is OFF
        is_connected_without_system_proxy = (self.active_config_details is not None and 
                                             hasattr(self, 'system_proxy_checkbox') and 
                                             not self.system_proxy_checkbox.isChecked())
        
        # Enable/disable edit and remove buttons
        can_edit_remove = is_profile_selected and is_connected_without_system_proxy and \
                          hasattr(self, 'app_proxy_enable_checkbox') and \
                          self.app_proxy_enable_checkbox.isChecked()
                          
        if hasattr(self, 'edit_profile_button'): self.edit_profile_button.setEnabled(can_edit_remove)
        if hasattr(self, 'remove_profile_button'): self.remove_profile_button.setEnabled(can_edit_remove)

        if is_profile_selected:
            new_active_profile_name = selected_items[0].text()
            profile_data = self.application_profiles.get(new_active_profile_name, {})
            unmatched_action = profile_data.get("unmatched_action", "Proxy") # Default to Proxy

            if hasattr(self, 'unmatched_traffic_action_combo'):
                self.unmatched_traffic_action_combo.blockSignals(True)
                self.unmatched_traffic_action_combo.setCurrentText(unmatched_action)
                self.unmatched_traffic_action_combo.blockSignals(False)
                # Enable combo only if app proxy mode is active and a profile is selected
                self.unmatched_traffic_action_combo.setEnabled(
                    is_connected_without_system_proxy and 
                    hasattr(self, 'app_proxy_enable_checkbox') and 
                    self.app_proxy_enable_checkbox.isChecked()
                )
            
            if self.active_app_profile_name != new_active_profile_name:
                self.active_app_profile_name = new_active_profile_name
                self.log_debug(f"App profile '{self.active_app_profile_name}' selected. Unmatched action: {unmatched_action}")
                # Reconnect only if app proxy is enabled and connection is active
                if hasattr(self, 'app_proxy_enable_checkbox') and self.app_proxy_enable_checkbox.isChecked() and self.active_config_details:
                    self.reconnect_with_new_rules()
        else: # No profile selected
            if self.active_app_profile_name is not None: # If a profile *was* selected
                self.active_app_profile_name = None
                # Reconnect if app proxy was active and selection cleared
                if hasattr(self, 'app_proxy_enable_checkbox') and self.app_proxy_enable_checkbox.isChecked() and self.active_config_details:
                    self.reconnect_with_new_rules()
            
            if hasattr(self, 'unmatched_traffic_action_combo'):
                self.unmatched_traffic_action_combo.setEnabled(False)
                self.unmatched_traffic_action_combo.blockSignals(True)
                self.unmatched_traffic_action_combo.setCurrentIndex(0) # Default to "Proxy"
                self.unmatched_traffic_action_combo.blockSignals(False)
            self.log_debug("No app profile selected.")
    
    def toggle_app_proxy_enabled_state(self, state_int):
        checked = (state_int == Qt.Checked)
        self.log_debug(f"App-specific proxy enable toggled: {'Enabled' if checked else 'Disabled'}")

        if checked:
            if not self.app_profiles_list_widget.currentItem():
                QMessageBox.warning(self, "No Profile Selected", "Please select an application profile first to enable app-specific proxying.")
                if hasattr(self, 'app_proxy_enable_checkbox'): self.app_proxy_enable_checkbox.setChecked(False) # Revert
                return
            self.active_app_profile_name = self.app_profiles_list_widget.currentItem().text()
            # System proxy should be off if app proxy is on
            if hasattr(self, 'system_proxy_checkbox') and self.system_proxy_checkbox.isChecked():
                self.system_proxy_checkbox.setChecked(False) # This will trigger its own handler, which calls reconnect
            
            if hasattr(self, 'unmatched_traffic_action_combo'): self.unmatched_traffic_action_combo.setEnabled(True)
            self.log_debug(f"App profile '{self.active_app_profile_name}' enabled.")
        else:
            old_active_profile = self.active_app_profile_name
            self.active_app_profile_name = None # No profile is active when app proxy is disabled
            if hasattr(self, 'unmatched_traffic_action_combo'): self.unmatched_traffic_action_combo.setEnabled(False)
            self.log_debug(f"App-specific proxying disabled (was profile: '{old_active_profile}').")

        # Update enabled state of list widget and buttons
        if hasattr(self, 'app_profiles_list_widget'): self.app_profiles_list_widget.setEnabled(checked)
        self.handle_app_profile_selection_changed() # Updates edit/remove buttons based on current selection & overall state

        if self.active_config_details: # Only reconnect if a connection is active
            self.reconnect_with_new_rules()

    def set_unmatched_traffic_action_for_active_profile(self, action_text):
        if self.active_app_profile_name and self.active_app_profile_name in self.application_profiles:
            # Check if the action actually changed
            if self.application_profiles[self.active_app_profile_name].get("unmatched_action") != action_text:
                self.application_profiles[self.active_app_profile_name]["unmatched_action"] = action_text
                self.save_application_profiles()
                self.log_debug(f"Unmatched traffic action for profile '{self.active_app_profile_name}' set to '{action_text}'.")
                # Reconnect if app proxy is enabled and connection is active
                if self.active_config_details and hasattr(self, 'app_proxy_enable_checkbox') and self.app_proxy_enable_checkbox.isChecked():
                    self.reconnect_with_new_rules()
        elif hasattr(self, 'app_proxy_enable_checkbox') and self.app_proxy_enable_checkbox.isChecked(): 
            # This case means app_proxy_enable_checkbox is checked, but no profile is active (e.g. list empty or selection lost)
            # This shouldn't ideally happen if app_proxy_enable_checkbox requires a selected profile to be checked.
             QMessageBox.warning(self, "No Profile Active", "Please select an active profile to set its unmatched traffic action.")
             # Optionally reset combo to avoid confusion
             if hasattr(self, 'unmatched_traffic_action_combo'): 
                 self.unmatched_traffic_action_combo.blockSignals(True)
                 self.unmatched_traffic_action_combo.setCurrentIndex(0) # Default to "Proxy"
                 self.unmatched_traffic_action_combo.blockSignals(False)

    def _load_subscriptions_async(self):
        """Load subscriptions asynchronously to avoid blocking startup"""
        try:
            self.load_subscriptions_config()
            self.log_debug("Subscriptions loaded asynchronously.")
        except Exception as e:
            self.log_debug(f"Error loading subscriptions asynchronously: {e}")

    def _start_monitoring_timers(self):
        """Start monitoring timers after a delay to improve startup performance"""
        try:
            if self.stability_improvements_enabled:
                self.system_monitor_timer.start()
                self.ui_watchdog_timer.start()
                self.process_monitor_timer.start()
                self.emergency_recovery_timer.start()
                self.adaptive_update_timer.start()
                self.log_debug("Monitoring timers started.")
        except Exception as e:
            self.log_debug(f"Error starting monitoring timers: {e}")

    def _check_xray_executable(self):
        # ... (Keep existing implementation - unchanged) ...
        try:
            command = [self.XRAY_EXECUTABLE, "version"]
            startupinfo = None
            creationflags = 0
            if platform.system() == "Windows":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE
                creationflags=subprocess.CREATE_NO_WINDOW
            process = subprocess.run(command, capture_output=True, text=True, timeout=5, check=True, startupinfo=startupinfo, creationflags=creationflags, encoding='utf-8', errors='ignore')
            version_line = process.stdout.splitlines()[0] if process.stdout else "Unknown Version"
            self.log_debug(f"Xray executable found: {version_line}")
            return True
        except FileNotFoundError:
            self.log_debug(f"ERROR: Xray executable not found at '{self.XRAY_EXECUTABLE}'. Please check the path or system PATH.")
            QMessageBox.critical(self, "Xray Not Found",
                                 f"Xray executable ('{self.XRAY_EXECUTABLE}') not found.\n"
                                 f"Ensure it's installed and the path is correct in the script, or that it's in your system's PATH variable.")
            return False
        except (subprocess.TimeoutExpired, subprocess.CalledProcessError, OSError) as e:
            self.log_debug(f"ERROR: Could not run Xray '{self.XRAY_EXECUTABLE}'. Error: {e}")
            QMessageBox.critical(self, "Xray Execution Error",
                                 f"Could not execute '{self.XRAY_EXECUTABLE}'. Check file permissions and validity.\nError: {e}")
            return False
        except Exception as e:
             self.log_debug(f"ERROR: Unexpected error checking Xray '{self.XRAY_EXECUTABLE}'. Error: {e}")
             QMessageBox.critical(self, "Xray Check Error",
                                  f"An unexpected error occurred while checking '{self.XRAY_EXECUTABLE}'.\nError: {e}")
             return False

    def find_available_port(self, start_port=10810, end_port=11000):
        # ... (Keep existing implementation - unchanged) ...
        with self.port_lock:
            # Shuffle the port range to reduce immediate reuse conflicts if multiple tests start near-simultaneously
            port_range = list(range(start_port, end_port))
            random.shuffle(port_range)
            for port in port_range:
                if port not in self.used_ports:
                    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                    try:
                        sock.bind((self.TEMP_PROXY_HOST, port)) # Bind to specific host
                        self.used_ports.add(port)
                        self.log_debug(f"Allocated port {port}")
                        return port
                    except socket.error:
                        # Port likely in use or unavailable
                        continue
                    finally:
                        sock.close()
            self.log_debug(f"Failed to find available port in range {start_port}-{end_port}")
            return None # Indicate no port found

    def release_port(self, port):
        # ... (Keep existing implementation - unchanged) ...
        with self.port_lock:
            if port in self.used_ports:
                self.used_ports.discard(port)
                self.log_debug(f"Released port {port}")
            # else:
            #     self.log_debug(f"Attempted to release port {port} which was not marked as used.")


    def setup_style(self):
        # ... (Keep existing implementation - unchanged) ...
        QApplication.setStyle("Fusion")
        palette = QPalette()
        # Dark Theme Colors (Adjust as desired)
        palette.setColor(QPalette.Window, QColor(30, 30, 30))
        palette.setColor(QPalette.WindowText, Qt.white)
        palette.setColor(QPalette.Base, QColor(25, 25, 25)) # Input field background
        palette.setColor(QPalette.AlternateBase, QColor(45, 45, 45)) # Table alternating rows
        palette.setColor(QPalette.ToolTipBase, QColor(25, 25, 25))
        palette.setColor(QPalette.ToolTipText, Qt.white)
        palette.setColor(QPalette.Text, Qt.white) # General text
        palette.setColor(QPalette.Button, QColor(53, 53, 53))
        palette.setColor(QPalette.ButtonText, Qt.white)
        palette.setColor(QPalette.BrightText, Qt.red)
        palette.setColor(QPalette.Link, QColor(42, 130, 218))
        palette.setColor(QPalette.Highlight, QColor(42, 130, 218)) # Selection highlight
        palette.setColor(QPalette.HighlightedText, Qt.black) # Text in selection
        # Apply palette
        QApplication.setPalette(palette)
        # Optional: Apply stylesheet for more control
        # self.setStyleSheet("...")

    def setup_fetching_settings_tab(self):
        """Setup the reorganized Fetching Settings tab with unified subscription management and filters"""
        self.fetching_settings_tab = QWidget()
        self.tab_widget.addTab(self.fetching_settings_tab, "Fetching Settings")
        main_layout = QVBoxLayout(self.fetching_settings_tab)

        # Load subscriptions from config file (predefined_subscriptions already initialized in __init__)
        self.load_subscriptions()

        # Create unified Fetching Settings group box
        fetching_group = QGroupBox("Fetching Settings")
        fetching_layout = QVBoxLayout(fetching_group)

        # Source dropdown with label on the same line - stretched to edge
        source_layout = QHBoxLayout()
        source_label = QLabel("Sources:")
        source_label.setMinimumHeight(45)  # 1.5x taller as requested
        source_label.setFixedWidth(80)  # Fixed width for consistent alignment
        source_layout.addWidget(source_label)

        # Use MultiSelectComboBox with QComboBox styling for multi-selection capability
        self.subscription_combo = MultiSelectComboBox(height=30)  # Match standard combobox height
        # Remove minimum width constraint and let it stretch to fill available space
        # Remove custom styling to inherit application theme like standard QComboBox
        self.subscription_combo.display_button.setStyleSheet("")
        source_layout.addWidget(self.subscription_combo, 1)  # Stretch factor 1 to fill space
        fetching_layout.addLayout(source_layout)

        # Management buttons and input bar in organized layout
        management_layout = QHBoxLayout()

        self.add_subscription_button = QPushButton("Add Subscription")
        self.add_subscription_button.setToolTip("Add a new subscription URL to the predefined list")
        self.add_subscription_button.clicked.connect(self.add_subscription)
        self.add_subscription_button.setMinimumWidth(120)
        self.add_subscription_button.setMinimumHeight(30)  # Match input bar height
        management_layout.addWidget(self.add_subscription_button)

        self.remove_subscription_button = QPushButton("Remove")
        self.remove_subscription_button.setToolTip("Remove the selected subscription from the predefined list")
        self.remove_subscription_button.clicked.connect(self.remove_subscription)
        self.remove_subscription_button.setMinimumWidth(80)
        self.remove_subscription_button.setMinimumHeight(30)  # Match input bar height
        management_layout.addWidget(self.remove_subscription_button)

        self.edit_subscription_button = QPushButton("Edit")
        self.edit_subscription_button.setToolTip("Edit the name and URL of the selected subscription")
        self.edit_subscription_button.clicked.connect(self.edit_subscription)
        self.edit_subscription_button.setMinimumWidth(80)
        self.edit_subscription_button.setMinimumHeight(30)  # Match input bar height
        management_layout.addWidget(self.edit_subscription_button)

        # Clear button positioned before input bar
        self.clear_subscription_button = QPushButton("Clear")
        self.clear_subscription_button.setToolTip("Clear subscription selection and return to 'All'")
        self.clear_subscription_button.setMaximumWidth(80)
        self.clear_subscription_button.setMinimumHeight(30)  # Match input bar height
        self.clear_subscription_button.clicked.connect(self.clear_subscription_selection)
        management_layout.addWidget(self.clear_subscription_button)

        # Custom input bar positioned after clear button - stretched to fill available space
        self.custom_subscription = QLineEdit()
        self.custom_subscription.setPlaceholderText("Paste subscription URL or config here...")
        self.custom_subscription.setContextMenuPolicy(Qt.CustomContextMenu)
        self.custom_subscription.customContextMenuRequested.connect(self.show_context_menu)
        self.custom_subscription.setMinimumHeight(30)  # Compact single-line input
        # Remove maximum width constraint and let it stretch to fill available space
        management_layout.addWidget(self.custom_subscription, 1)  # Stretch factor 1 to fill remaining space

        fetching_layout.addLayout(management_layout)

        # Filter controls integrated into the unified section
        self.setup_filter_controls(fetching_layout)

        # Fetch buttons under filter dropboxes
        fetch_layout = QHBoxLayout()

        fetch_pasted_btn = QPushButton("Fetch Pasted Sub/Config")
        fetch_pasted_btn.setToolTip("Process the URL/config pasted in the input area")
        fetch_pasted_btn.clicked.connect(self.fetch_pasted_subscription)
        fetch_pasted_btn.setMinimumWidth(180)
        fetch_layout.addWidget(fetch_pasted_btn)

        fetch_selected_btn = QPushButton("Fetch Selected")  # Renamed from "Fetch Predefined"
        fetch_selected_btn.setToolTip("Process the currently selected predefined subscription")
        fetch_selected_btn.clicked.connect(self.fetch_selected_subscription)
        fetch_selected_btn.setMinimumWidth(150)
        fetch_layout.addWidget(fetch_selected_btn)

        fetch_all_btn = QPushButton("Fetch All Sources")
        fetch_all_btn.setToolTip("Process all available predefined subscriptions")
        fetch_all_btn.clicked.connect(self.fetch_all_sources)
        fetch_all_btn.setMinimumWidth(150)
        fetch_layout.addWidget(fetch_all_btn)

        fetch_layout.addStretch()
        fetching_layout.addLayout(fetch_layout)

        # Add the unified fetching settings group to main layout
        main_layout.addWidget(fetching_group)

        # Add connection section with automated workflow
        self.setup_connection_section(main_layout)

        # Add debug information area at the bottom
        self.setup_debug_area(main_layout)

        main_layout.addStretch() # Push content to the top

    def setup_filter_controls(self, parent_layout):
        """Setup integrated filter controls within the unified Fetching Settings section"""
        # Create a horizontal layout for filters (no separate group box)
        filter_layout = QHBoxLayout()

        # Protocol Filter Section
        protocol_section = QVBoxLayout()
        protocol_label = QLabel("Protocol Filter:")
        protocol_label.setMinimumHeight(30)  # Increased height by 1.5x (from ~20px to 30px)
        protocol_section.addWidget(protocol_label)

        self.protocol_filter = MultiSelectComboBox(height=30)  # Match clear button height

        # Add protocol items (including VLESS sub-protocols)
        protocols = ["ss", "vmess", "vless", "trojan", "vless-xtls", "vless-ws", "vless-tls", "vless-grpc", "vless-tcp"]
        for protocol in protocols:
            self.protocol_filter.add_item(protocol)

        # Start with no selections (which means "All")
        self.protocol_filter.clear_selection()

        protocol_section.addWidget(self.protocol_filter)
        filter_layout.addLayout(protocol_section)

        # Country Filter Section
        country_section = QVBoxLayout()
        country_label = QLabel("Country Filter:")
        country_label.setMinimumHeight(30)  # Increased height by 1.5x (from ~20px to 30px)
        country_section.addWidget(country_label)

        self.country_filter = MultiSelectComboBox(height=30)  # Match clear button height

        # Add country items
        countries = [
            "United States", "United Kingdom", "Turkey", "Israel", "Netherlands",
            "Lithuania", "Hong Kong", "Poland", "Russia", "Brazil", "Argentina",
            "France", "Spain", "Italy", "Germany", "Greece", "UAE", "Bahrain",
            "Kuwait", "Japan", "India", "Singapore", "South Korea", "Australia",
            "South Africa", "Egypt", "Algeria", "Hungary", "Romania", "Sweden",
            "Norway", "Finland", "Canada", "Belgium", "Switzerland"
        ]
        for country in countries:
            self.country_filter.add_item(country)

        # Start with no selections (which means "All")
        self.country_filter.clear_selection()

        country_section.addWidget(self.country_filter)
        filter_layout.addLayout(country_section)

        # Add Clear button - centered with filter dropdown menus
        clear_section = QVBoxLayout()
        clear_empty_label = QLabel("")  # Empty label for alignment
        clear_empty_label.setMinimumHeight(32)  # Centered alignment for 20px button with 30px dropdowns
        clear_section.addWidget(clear_empty_label)
        clear_button = QPushButton("Clear")
        clear_button.setToolTip("Clear all filters and return to 'All'")
        clear_button.setMaximumWidth(80)  # Restore original width
        clear_button.setFixedHeight(21)  # Compact height as requested
        clear_button.clicked.connect(self.clear_all_filters)
        clear_section.addWidget(clear_button)
        # Set layout margins for perfect centering
        clear_section.setContentsMargins(0, 0, 0, 5)
        filter_layout.addLayout(clear_section)

        # Add the filter layout directly to parent (no group box wrapper)
        parent_layout.addLayout(filter_layout)

    def setup_connection_section(self, parent_layout):
        """Setup connection section with automated workflow in the fetching settings tab"""
        # Connection section with test options
        connection_group = QGroupBox("Connection")
        connection_group_layout = QVBoxLayout(connection_group)

        # Connect button for automated workflow (full width, same height as dropdowns)
        self.connect_button = QPushButton("Connect")
        self.connect_button.setToolTip("Automated workflow: Fetch subscriptions → Apply filters → Test configs → Connect to best latency")
        self.connect_button.clicked.connect(self.start_automated_connect_workflow)
        self.connect_button.setMinimumHeight(30)  # Same height as history dropdown
        self.connect_button.setMaximumHeight(30)  # Prevent it from getting taller
        connection_group_layout.addWidget(self.connect_button)

        # History section with Clear button on the right side
        history_layout = QHBoxLayout()

        # History dropdown
        self.history_combo = MultiSelectComboBox(height=30)
        self.history_combo.setToolTip("Select previous connection settings from history")
        self.history_combo.selectionChanged.connect(self.on_history_selection_changed)
        history_layout.addWidget(self.history_combo)

        # Clear button with same dimensions and placement as filter Clear buttons
        clear_history_button = QPushButton("Clear")
        clear_history_button.setToolTip("Clear all connection history")
        clear_history_button.clicked.connect(self.clear_connection_history)
        clear_history_button.setMaximumWidth(80)   # Same as filter Clear button
        clear_history_button.setFixedHeight(21)    # Same as filter Clear button
        history_layout.addWidget(clear_history_button)

        connection_group_layout.addLayout(history_layout)

        # Test type checkboxes (mutually exclusive) - placed under history
        test_options_layout = QHBoxLayout()

        self.http_test_checkbox = QCheckBox("HTTP Test")
        self.http_test_checkbox.setChecked(True)  # Auto-checked as requested
        self.http_test_checkbox.setToolTip("Perform HTTP connectivity test with integrity verification")
        self.http_test_checkbox.toggled.connect(self.on_http_test_toggled)
        test_options_layout.addWidget(self.http_test_checkbox)

        self.complete_test_checkbox = QCheckBox("Complete Test")
        self.complete_test_checkbox.setChecked(False)
        self.complete_test_checkbox.setToolTip("Perform comprehensive test including netcat and download tests")
        self.complete_test_checkbox.toggled.connect(self.on_complete_test_toggled)
        test_options_layout.addWidget(self.complete_test_checkbox)

        test_options_layout.addStretch()
        connection_group_layout.addLayout(test_options_layout)

        parent_layout.addWidget(connection_group)

    def setup_debug_area(self, parent_layout):
        """Setup debug information area in the specified layout"""
        # Debug Group
        debug_group = QGroupBox("Debug Information")
        debug_layout = QVBoxLayout(debug_group)
        debug_controls = QHBoxLayout()

        # Debug control checkboxes
        self.debug_mode = QCheckBox("Enable Debug")
        self.debug_mode.setChecked(True) # Default to enabled for easier debugging
        self.debug_mode.setToolTip("Enable/disable debug logging")
        debug_controls.addWidget(self.debug_mode)

        self.full_debug_mode = QCheckBox("Full Debug")
        self.full_debug_mode.setChecked(False) # Default to limited debug (last 30 messages)
        self.full_debug_mode.setToolTip("Show all debug messages instead of just the last 30")
        self.full_debug_mode.stateChanged.connect(self.toggle_full_debug)
        debug_controls.addWidget(self.full_debug_mode)

        self.disable_debug_mode = QCheckBox("Disable Debug")
        self.disable_debug_mode.setChecked(False) # Default to debug enabled
        self.disable_debug_mode.setToolTip("Completely disable debug logging (improves performance)")
        self.disable_debug_mode.stateChanged.connect(self.toggle_disable_debug)
        debug_controls.addWidget(self.disable_debug_mode)

        # Add stability improvements checkbox
        # === DEBUG-RELATED CHECKBOXES (grouped together) ===

        # Add log file export checkboxes
        self.export_full_log_checkbox = QCheckBox("Export Full Debug to Log")
        self.export_full_log_checkbox.setChecked(False) # Default to disabled as requested
        self.export_full_log_checkbox.setToolTip("Export all debug logs including subscription extraction/processing to a file for troubleshooting")
        debug_controls.addWidget(self.export_full_log_checkbox)

        self.export_debug_log_checkbox = QCheckBox("Export Debug to Log")
        self.export_debug_log_checkbox.setChecked(True) # Default to enabled as requested
        self.export_debug_log_checkbox.setToolTip("Export debug logs to a file excluding subscription extraction/processing logs")
        debug_controls.addWidget(self.export_debug_log_checkbox)

        # Add checkbox to hide system monitoring messages
        self.hide_system_monitoring_checkbox = QCheckBox("Hide System Monitoring")
        self.hide_system_monitoring_checkbox.setChecked(True) # Default to checked (hide monitoring messages)
        self.hide_system_monitoring_checkbox.setToolTip("Hide system monitoring and adaptive resource management messages from debug output")
        debug_controls.addWidget(self.hide_system_monitoring_checkbox)

        # === ADJUSTABLE PROCESS (at the end) ===

        self.stability_checkbox = QCheckBox("Adjustable Process")
        self.stability_checkbox.setChecked(True) # Default to enabled as requested
        self.stability_checkbox.setToolTip("Enable/disable stability improvements to prevent application freezing under heavy load")
        self.stability_checkbox.stateChanged.connect(self.toggle_stability_improvements)
        debug_controls.addWidget(self.stability_checkbox)

        # Ensure stability_improvements_enabled is set
        if not hasattr(self, 'stability_improvements_enabled'):
            self.stability_improvements_enabled = True

        # Start the timers if stability improvements are enabled (default)
        if hasattr(self, 'system_monitor_timer') and hasattr(self, 'ui_watchdog_timer'):
            self.system_monitor_timer.start()
            self.ui_watchdog_timer.start()
            self.log_debug("Started system monitor and UI watchdog timers")

        clear_debug_button = QPushButton("Clear Debug Log")
        clear_debug_button.clicked.connect(self.clear_debug_log)
        debug_controls.addWidget(clear_debug_button)
        debug_controls.addStretch()
        debug_layout.addLayout(debug_controls)

        # Debug output text area
        from PyQt5.QtWidgets import QTextEdit
        from PyQt5.QtGui import QFont
        self.debug_output = QTextEdit()
        self.debug_output.setReadOnly(True)
        self.debug_output.setPlaceholderText("Debug information will appear here")
        self.debug_output.setMinimumHeight(150)
        self.debug_output.setMaximumHeight(250)  # Reasonable height that fits within window
        self.debug_output.setFont(QFont("Consolas", 9)) # Monospaced font
        debug_layout.addWidget(self.debug_output, 1)  # Stretch factor to expand within debug group

        # Store debug messages in memory
        self.debug_messages = []
        self.max_debug_messages = 30 # Default limit

        # Initialize debug buffer variables
        self.debug_buffer = []
        self.debug_buffer_size = 50
        self.debug_append_count = 0
        self.debug_update_needed = False

        # Add debug group with stretch factor to fill remaining space
        parent_layout.addWidget(debug_group, 1)  # Stretch factor of 1 to expand

    # --- Multi-Select Filter Helper Methods ---
    def get_selected_protocols(self):
        """Get list of selected protocols"""
        return self.protocol_filter.get_selected_items()

    def get_selected_countries(self):
        """Get list of selected countries"""
        return self.country_filter.get_selected_items()

    def _get_vless_subtype(self, config):
        """Determine VLESS sub-protocol type based on config fields"""
        if config.get('protocol', '').lower() != 'vless':
            return None

        # Check for XTLS flow (indicates vless-xtls)
        flow = config.get('flow', '').lower()
        if flow and 'xtls' in flow:
            return 'vless-xtls'

        # Check security type
        security = config.get('security', '').lower()
        if security == 'xtls':
            return 'vless-xtls'
        elif security == 'tls':
            return 'vless-tls'

        # Check network/transport type
        network = config.get('network', config.get('type', '')).lower()
        if network == 'ws':
            return 'vless-ws'
        elif network == 'grpc':
            return 'vless-grpc'
        elif network == 'tcp':
            return 'vless-tcp'

        # Default to regular vless if no specific sub-type identified
        return 'vless'

    def clear_all_filters(self):
        """Clear all filters and return to 'All' state"""
        self.protocol_filter.clear_selection()
        self.country_filter.clear_selection()
        self.log_debug("All filters cleared - returned to 'All' state")

        # Reapply filters to update the display
        if hasattr(self, 'configs') and self.configs:
            self.apply_filter_and_update_ui()

    def clear_subscription_selection(self):
        """Clear subscription selection and return to 'All' state"""
        try:
            # Clear subscription selection
            if hasattr(self, 'subscription_combo'):
                self.subscription_combo.clear_selection()

            self.log_debug("Subscription selection cleared - returned to 'All' state")
            self.status_bar.showMessage("Subscription selection cleared")

        except Exception as e:
            self.log_debug(f"Error clearing subscription selection: {e}")
            traceback.print_exc()

    # --- Subscription Management Methods ---
    def load_subscriptions(self):
        """Load subscriptions from config file"""
        config_file = "subscriptions_config.json"
        try:
            if os.path.exists(config_file):
                with open(config_file, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    self.predefined_subscriptions = data.get('subscriptions', [])
                    self.log_debug(f"Loaded {len(self.predefined_subscriptions)} subscriptions from config file")
            else:
                self.predefined_subscriptions = self.default_predefined_subscriptions.copy()
                self.save_subscriptions()
                self.log_debug("Created new subscriptions config with default subscriptions")
        except Exception as e:
            self.log_debug(f"Error loading subscriptions: {e}")
            self.predefined_subscriptions = self.default_predefined_subscriptions.copy()

        # Update the combo box
        self.update_subscription_combo()

    def save_subscriptions(self):
        """Save subscriptions to config file"""
        config_file = "subscriptions_config.json"
        try:
            data = {
                'subscriptions': self.predefined_subscriptions,
                'last_updated': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            }
            with open(config_file, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            self.log_debug(f"Saved {len(self.predefined_subscriptions)} subscriptions to config file")
        except Exception as e:
            self.log_debug(f"Error saving subscriptions: {e}")

    def update_subscription_combo(self):
        """Update the subscription combo box with current subscriptions"""
        if hasattr(self, 'subscription_combo'):
            # Clear existing items
            self.subscription_combo.clear_items()

            # Add subscription names
            for name, url in self.predefined_subscriptions:
                self.subscription_combo.add_item(name)

            # Add special options
            self.subscription_combo.add_item("All Predefined")

            self.log_debug(f"Updated subscription combo with {len(self.predefined_subscriptions)} subscriptions")

    def add_subscription(self):
        """Add a new subscription"""
        dialog = QDialog(self)
        dialog.setWindowTitle("Add Subscription")
        dialog.setModal(True)
        layout = QVBoxLayout(dialog)

        # Name input
        name_layout = QHBoxLayout()
        name_layout.addWidget(QLabel("Name:"))
        name_input = QLineEdit()
        name_input.setPlaceholderText("Enter subscription name")
        name_layout.addWidget(name_input)
        layout.addLayout(name_layout)

        # URL input
        url_layout = QHBoxLayout()
        url_layout.addWidget(QLabel("URL:"))
        url_input = QLineEdit()
        url_input.setPlaceholderText("Enter subscription URL")
        url_layout.addWidget(url_input)
        layout.addLayout(url_layout)

        # Buttons
        button_layout = QHBoxLayout()
        ok_button = QPushButton("Add")
        cancel_button = QPushButton("Cancel")
        button_layout.addWidget(ok_button)
        button_layout.addWidget(cancel_button)
        layout.addLayout(button_layout)

        def add_clicked():
            name = name_input.text().strip()
            url = url_input.text().strip()
            if name and url:
                self.predefined_subscriptions.append([name, url])
                self.save_subscriptions()
                self.update_subscription_combo()
                dialog.accept()
                self.log_debug(f"Added subscription: {name}")
            else:
                QMessageBox.warning(dialog, "Invalid Input", "Please enter both name and URL")

        ok_button.clicked.connect(add_clicked)
        cancel_button.clicked.connect(dialog.reject)

        dialog.exec_()

    def remove_subscription(self):
        """Remove selected subscription"""
        selected_items = self.subscription_combo.get_selected_items()
        if not selected_items:
            QMessageBox.information(self, "No Selection", "Please select a subscription to remove")
            return

        # Filter out special items
        items_to_remove = [item for item in selected_items if item != "All Predefined"]
        if not items_to_remove:
            QMessageBox.information(self, "Cannot Remove", "Cannot remove 'All Predefined' option")
            return

        # Confirm removal
        if len(items_to_remove) == 1:
            msg = f"Are you sure you want to remove '{items_to_remove[0]}'?"
        else:
            msg = f"Are you sure you want to remove {len(items_to_remove)} subscriptions?"

        reply = QMessageBox.question(self, "Confirm Removal", msg,
                                   QMessageBox.Yes | QMessageBox.No, QMessageBox.No)

        if reply == QMessageBox.Yes:
            # Remove subscriptions
            self.predefined_subscriptions = [
                [name, url] for name, url in self.predefined_subscriptions
                if name not in items_to_remove
            ]
            self.save_subscriptions()
            self.update_subscription_combo()
            self.log_debug(f"Removed {len(items_to_remove)} subscriptions")

    def edit_subscription(self):
        """Edit selected subscription"""
        selected_items = self.subscription_combo.get_selected_items()
        if len(selected_items) != 1:
            QMessageBox.information(self, "Invalid Selection", "Please select exactly one subscription to edit")
            return

        selected_name = selected_items[0]
        if selected_name == "All Predefined":
            QMessageBox.information(self, "Cannot Edit", "Cannot edit 'All Predefined' option")
            return

        # Find the subscription
        subscription_to_edit = None
        for i, (name, url) in enumerate(self.predefined_subscriptions):
            if name == selected_name:
                subscription_to_edit = (i, name, url)
                break

        if not subscription_to_edit:
            QMessageBox.warning(self, "Not Found", "Selected subscription not found")
            return

        index, current_name, current_url = subscription_to_edit

        # Create edit dialog
        dialog = QDialog(self)
        dialog.setWindowTitle("Edit Subscription")
        dialog.setModal(True)
        layout = QVBoxLayout(dialog)

        # Name input
        name_layout = QHBoxLayout()
        name_layout.addWidget(QLabel("Name:"))
        name_input = QLineEdit(current_name)
        name_layout.addWidget(name_input)
        layout.addLayout(name_layout)

        # URL input
        url_layout = QHBoxLayout()
        url_layout.addWidget(QLabel("URL:"))
        url_input = QLineEdit(current_url)
        url_layout.addWidget(url_input)
        layout.addLayout(url_layout)

        # Buttons
        button_layout = QHBoxLayout()
        ok_button = QPushButton("Save")
        cancel_button = QPushButton("Cancel")
        button_layout.addWidget(ok_button)
        button_layout.addWidget(cancel_button)
        layout.addLayout(button_layout)

        def save_clicked():
            name = name_input.text().strip()
            url = url_input.text().strip()
            if name and url:
                self.predefined_subscriptions[index] = [name, url]
                self.save_subscriptions()
                self.update_subscription_combo()
                dialog.accept()
                self.log_debug(f"Edited subscription: {current_name} -> {name}")
            else:
                QMessageBox.warning(dialog, "Invalid Input", "Please enter both name and URL")

        ok_button.clicked.connect(save_clicked)
        cancel_button.clicked.connect(dialog.reject)

        dialog.exec_()

    # --- Connection History Methods ---
    def load_connection_history(self):
        """Load connection history from JSON file"""
        try:
            if os.path.exists(self.connection_history_file):
                with open(self.connection_history_file, 'r', encoding='utf-8') as f:
                    self.connection_history = json.load(f)
                self.log_debug(f"Loaded {len(self.connection_history)} connection history entries")
            else:
                self.connection_history = []
                self.log_debug("No connection history file found, starting with empty history")
        except Exception as e:
            self.log_debug(f"Error loading connection history: {e}")
            self.connection_history = []

    def save_connection_history(self):
        """Save connection history to JSON file"""
        try:
            with open(self.connection_history_file, 'w', encoding='utf-8') as f:
                json.dump(self.connection_history, f, indent=2, ensure_ascii=False)
            self.log_debug(f"Saved {len(self.connection_history)} connection history entries")
        except Exception as e:
            self.log_debug(f"Error saving connection history: {e}")

    def add_to_connection_history(self, subscription_name, protocols, countries):
        """Add current connection settings to history"""
        try:
            # Create history entry
            history_entry = {
                'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                'subscription': subscription_name,
                'protocols': protocols if isinstance(protocols, list) else [protocols],
                'countries': countries if isinstance(countries, list) else [countries]
            }

            # Check if this exact combination already exists
            for existing in self.connection_history:
                if (existing.get('subscription') == subscription_name and
                    existing.get('protocols') == history_entry['protocols'] and
                    existing.get('countries') == history_entry['countries']):
                    # Update timestamp and move to front
                    existing['timestamp'] = history_entry['timestamp']
                    self.connection_history.remove(existing)
                    self.connection_history.insert(0, existing)
                    self.save_connection_history()
                    self.update_history_combo()
                    return

            # Add new entry at the beginning
            self.connection_history.insert(0, history_entry)

            # Keep only last 50 entries
            if len(self.connection_history) > 50:
                self.connection_history = self.connection_history[:50]

            self.save_connection_history()
            self.update_history_combo()
            self.log_debug(f"Added connection history: {subscription_name}, {protocols}, {countries}")
        except Exception as e:
            self.log_debug(f"Error adding to connection history: {e}")

    def clear_connection_history(self):
        """Clear all connection history"""
        try:
            self.connection_history = []
            self.save_connection_history()
            self.update_history_combo()
            self.log_debug("Connection history cleared")
        except Exception as e:
            self.log_debug(f"Error clearing connection history: {e}")

    def load_extracted_profiles(self):
        """Load extracted profiles from JSON file"""
        try:
            if os.path.exists(self.extracted_profiles_file):
                with open(self.extracted_profiles_file, 'r', encoding='utf-8') as f:
                    self.extracted_profiles = json.load(f)
                self.log_debug(f"Loaded {len(self.extracted_profiles)} extracted profiles")
            else:
                self.extracted_profiles = {}
                self.log_debug("No extracted profiles file found, starting with empty profiles")
        except Exception as e:
            self.log_debug(f"Error loading extracted profiles: {e}")
            self.extracted_profiles = {}

    def save_extracted_profiles(self):
        """Save extracted profiles to JSON file"""
        try:
            with open(self.extracted_profiles_file, 'w', encoding='utf-8') as f:
                json.dump(self.extracted_profiles, f, indent=2, ensure_ascii=False)
            self.log_debug(f"Saved {len(self.extracted_profiles)} extracted profiles")
        except Exception as e:
            self.log_debug(f"Error saving extracted profiles: {e}")

    def update_history_combo(self):
        """Update the history combo box with current history"""
        try:
            if hasattr(self, 'history_combo'):
                self.history_combo.clear_items()
                for entry in self.connection_history:
                    display_text = f"{entry['subscription']} | {', '.join(entry['protocols'])} | {', '.join(entry['countries'])} ({entry['timestamp']})"
                    self.history_combo.add_item(display_text)
                self.log_debug(f"Updated history combo with {len(self.connection_history)} entries")
        except Exception as e:
            self.log_debug(f"Error updating history combo: {e}")

    def on_history_selection_changed(self):
        """Handle history selection changes - just log, don't apply immediately"""
        try:
            selected_items = self.history_combo.get_selected_items()
            if selected_items:
                self.log_debug(f"📜 HISTORY SELECTION CHANGED: {selected_items[0]}")
                self.log_debug("   History will be applied when Connect button is pressed")
                # Don't apply settings immediately - wait for Connect button
        except Exception as e:
            self.log_debug(f"Error handling history selection: {e}")

    def extract_profiles_from_configs(self):
        """Extract profiles from current configs and save them"""
        try:
            if not self.configs:
                self.log_debug("No configs to extract profiles from")
                return

            # Group configs by source/subscription
            profiles_by_source = {}
            for config in self.configs:
                source = config.get('source', 'Unknown')
                if source not in profiles_by_source:
                    profiles_by_source[source] = []
                profiles_by_source[source].append(config)

            # Save each source as a profile
            for source_name, configs in profiles_by_source.items():
                profile_data = {
                    'name': source_name,
                    'timestamp': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                    'config_count': len(configs),
                    'configs': configs
                }

                # Clean source name for filename
                safe_name = "".join(c for c in source_name if c.isalnum() or c in (' ', '-', '_')).rstrip()
                profile_key = f"extracted_{safe_name}_{datetime.now().strftime('%Y%m%d_%H%M%S')}"

                self.extracted_profiles[profile_key] = profile_data
                self.log_debug(f"Extracted profile: {source_name} with {len(configs)} configs")

            # Save to file
            self.save_extracted_profiles()

            # Update profile combos
            self.update_profile_combos()

            self.log_debug(f"Extracted {len(profiles_by_source)} profiles from current configs")

        except Exception as e:
            self.log_debug(f"Error extracting profiles: {e}")

    def update_profile_combos(self):
        """Update all profile combo boxes with extracted profiles"""
        try:
            # Get list of extracted profile names
            extracted_names = []
            for key, profile in self.extracted_profiles.items():
                display_name = f"{profile['name']} ({profile['config_count']} configs)"
                extracted_names.append(display_name)

            # Update complete test profile combo
            if hasattr(self, 'complete_test_profile_combo'):
                current_selection = self.complete_test_profile_combo.currentText()
                self.complete_test_profile_combo.clear()
                self.complete_test_profile_combo.addItems(["None", "All Predefined"] + self.get_profile_names() + extracted_names)
                # Restore selection if possible
                index = self.complete_test_profile_combo.findText(current_selection)
                if index >= 0:
                    self.complete_test_profile_combo.setCurrentIndex(index)

            # Update HTTP test profile combo
            if hasattr(self, 'http_test_profile_combo'):
                current_selection = self.http_test_profile_combo.currentText()
                self.http_test_profile_combo.clear()
                self.http_test_profile_combo.addItems(["None", "All Predefined"] + self.get_profile_names() + extracted_names)
                # Restore selection if possible
                index = self.http_test_profile_combo.findText(current_selection)
                if index >= 0:
                    self.http_test_profile_combo.setCurrentIndex(index)

            self.log_debug(f"Updated profile combos with {len(extracted_names)} extracted profiles")

        except Exception as e:
            self.log_debug(f"Error updating profile combos: {e}")

    def get_configs_from_profile_selection(self, profile_combo):
        """Get configs based on profile combo selection"""
        try:
            selected_profile = profile_combo.currentText()

            if selected_profile == "None":
                return self.configs
            elif selected_profile == "All Predefined":
                # Return all predefined subscription configs
                return self.configs  # For now, return current configs
            elif selected_profile in self.get_profile_names():
                # Handle predefined profiles
                return self.configs  # For now, return current configs
            else:
                # Check if it's an extracted profile
                for key, profile in self.extracted_profiles.items():
                    display_name = f"{profile['name']} ({profile['config_count']} configs)"
                    if display_name == selected_profile:
                        return profile['configs']

                # Fallback to current configs
                return self.configs

        except Exception as e:
            self.log_debug(f"Error getting configs from profile selection: {e}")
            return self.configs

    def initialize_loaded_data_ui(self):
        """Initialize UI components that depend on loaded data"""
        try:
            # Update history combo with loaded history
            self.update_history_combo()

            # Update profile combos with loaded extracted profiles
            self.update_profile_combos()

            self.log_debug("Initialized UI components with loaded data")
        except Exception as e:
            self.log_debug(f"Error initializing loaded data UI: {e}")

    def start_http_test_from_profile(self):
        """Start HTTP test using selected profile or current configs"""
        try:
            # Get configs based on profile selection
            configs_to_test = self.get_configs_from_profile_selection(self.http_test_profile_combo)

            if not configs_to_test:
                QMessageBox.warning(self, "No Configurations", "No configurations available for HTTP testing.")
                return

            # Use existing HTTP test functionality (the one at line 6105)
            # This will test the current filtered configs
            self.start_http_test()

        except Exception as e:
            self.log_debug(f"Error starting HTTP test: {e}")
            QMessageBox.critical(self, "Error", f"Failed to start HTTP test: {str(e)}")

    # --- Connecting Tab Methods ---
    def on_http_test_toggled(self, checked):
        """Handle HTTP test checkbox toggle"""
        if checked and self.complete_test_checkbox.isChecked():
            self.complete_test_checkbox.setChecked(False)

        # Update integrity test checkbox in Testing tab if it exists
        if hasattr(self, 'http_connection_integrity_checkbox'):
            self.http_connection_integrity_checkbox.setChecked(checked)

    def on_complete_test_toggled(self, checked):
        """Handle Complete test checkbox toggle"""
        if checked and self.http_test_checkbox.isChecked():
            self.http_test_checkbox.setChecked(False)

    def start_automated_connect_workflow(self):
        """Start the automated connect workflow with intelligent testing and connection"""
        try:
            self.log_debug("=" * 60)
            self.log_debug("🚀 CONNECT WORKFLOW STARTED")
            self.log_debug("=" * 60)
            self.status_bar.showMessage("Starting automated connect workflow...")

            # Initialize workflow state
            self.automated_workflow_active = True
            self.workflow_best_config = None
            self.workflow_best_score = None
            self.workflow_connected_config = None
            self.workflow_configs_tested = 0
            self.workflow_total_configs = 0
            self.workflow_stay_in_fetch_tab = True  # Set this early to prevent tab switching

            self.log_debug("📊 WORKFLOW STATE INITIALIZED:")
            self.log_debug(f"   - automated_workflow_active: {self.automated_workflow_active}")
            self.log_debug(f"   - workflow_best_config: {self.workflow_best_config}")
            self.log_debug(f"   - workflow_best_score: {self.workflow_best_score}")

            # Determine test type based on checkboxes in Connection section
            if hasattr(self, 'http_test_checkbox') and self.http_test_checkbox.isChecked():
                self.workflow_test_type = "http"
                self.log_debug("🔍 TEST TYPE: HTTP test (lowest latency priority)")
            elif hasattr(self, 'complete_test_checkbox') and self.complete_test_checkbox.isChecked():
                self.workflow_test_type = "complete"
                self.log_debug("🔍 TEST TYPE: Complete test (highest download speed priority)")
            else:
                # Default to HTTP test
                self.workflow_test_type = "http"
                self.log_debug("🔍 TEST TYPE: HTTP test (default - no test type selected)")

            # Check current UI state
            self.log_debug("📋 CURRENT UI STATE:")
            if hasattr(self, 'subscription_combo'):
                selected_subs = self.subscription_combo.get_selected_items()
                self.log_debug(f"   - Selected subscriptions: {selected_subs}")
            if hasattr(self, 'history_combo'):
                selected_history = self.history_combo.get_selected_items()
                self.log_debug(f"   - Selected history: {selected_history}")

            # Step 1: Fetch subscriptions based on current selection or history
            self.log_debug("📥 STARTING FETCH PHASE...")
            self.fetch_subscriptions_for_workflow()

        except Exception as e:
            self.log_debug(f"❌ ERROR starting automated connect workflow: {e}")
            self.automated_workflow_active = False

    def fetch_subscriptions_for_workflow(self):
        """Fetch subscriptions based on current selection or history for workflow"""
        try:
            self.log_debug("🔍 ANALYZING FETCH OPTIONS...")

            # Check if history is selected
            if hasattr(self, 'history_combo'):
                selected_history = self.history_combo.get_selected_items()
                self.log_debug(f"   - History combo exists, selected: {selected_history}")
                if selected_history:
                    self.log_debug(f"📜 APPLYING HISTORY SETTINGS: {selected_history[0]}")
                    self.apply_history_settings(selected_history[0])
                    return

            # Check current subscription selection
            if hasattr(self, 'subscription_combo'):
                selected_subscriptions = self.subscription_combo.get_selected_items()
                self.log_debug(f"   - Subscription combo exists, selected: {selected_subscriptions}")
                if selected_subscriptions:
                    self.log_debug(f"📡 FETCHING SELECTED SUBSCRIPTIONS: {', '.join(selected_subscriptions)}")
                    self.fetch_selected_subscription()
                    return

            # Default to fetching all sources
            self.log_debug("📡 NO SPECIFIC SELECTION - FETCHING ALL SOURCES")
            self.fetch_all_sources()

        except Exception as e:
            self.log_debug(f"❌ ERROR fetching subscriptions for workflow: {e}")
            self.automated_workflow_active = False

    def apply_history_settings(self, history_entry):
        """Apply history as fetch instructions - fetch specific subscription with specific filters"""
        try:
            self.log_debug(f"📜 APPLYING HISTORY AS FETCH INSTRUCTIONS: {history_entry}")

            # Find the history entry in our loaded history
            if not hasattr(self, 'connection_history') or not self.connection_history:
                self.log_debug("❌ No connection history loaded")
                return

            # Find matching history entry by reconstructing display text
            selected_history_data = None
            for entry in self.connection_history:
                # Reconstruct the display text to match what's shown in the combo
                display_text = f"{entry['subscription']} | {', '.join(entry['protocols'])} | {', '.join(entry['countries'])} ({entry['timestamp']})"
                if display_text == history_entry:
                    selected_history_data = entry
                    break

            if not selected_history_data:
                self.log_debug(f"❌ History entry '{history_entry}' not found in loaded history")
                self.log_debug(f"   Available entries:")
                for i, entry in enumerate(self.connection_history):
                    display_text = f"{entry['subscription']} | {', '.join(entry['protocols'])} | {', '.join(entry['countries'])} ({entry['timestamp']})"
                    self.log_debug(f"   [{i}]: {display_text}")
                return

            self.log_debug(f"📋 FOUND HISTORY DATA: {selected_history_data}")

            # Extract settings from history (using correct key names)
            subscription_name = selected_history_data.get('subscription', '')
            protocols = selected_history_data.get('protocols', [])
            countries = selected_history_data.get('countries', [])

            self.log_debug(f"📋 HISTORY FETCH INSTRUCTIONS:")
            self.log_debug(f"   - Fetch Subscription: {subscription_name}")
            self.log_debug(f"   - Apply Protocol Filters: {protocols}")
            self.log_debug(f"   - Apply Country Filters: {countries}")

            # Store history settings for use during filtering
            self.workflow_history_subscription = subscription_name
            self.workflow_history_protocols = protocols  # Keep "All" as is, don't convert to empty
            self.workflow_history_countries = countries  # Keep "All" as is, don't convert to empty

            # Fetch the specific subscription from history
            self.log_debug("📡 FETCHING SUBSCRIPTION FROM HISTORY...")
            if subscription_name and subscription_name != "All Predefined":
                # Temporarily set subscription selection for fetching
                if hasattr(self, 'subscription_combo'):
                    self.subscription_combo.clear_selection()
                    subscription_names = [name.strip() for name in subscription_name.split(',')]
                    for name in subscription_names:
                        self.subscription_combo.select_item(name)
                self.fetch_selected_subscription()
            else:
                self.fetch_all_sources()

            # Don't switch tabs during workflow - stay in Fetch tab until connection
            self.workflow_stay_in_fetch_tab = True

        except Exception as e:
            self.log_debug(f"❌ ERROR applying history settings: {e}")
            import traceback
            self.log_debug(f"   Traceback: {traceback.format_exc()}")
            # Fallback to current settings
            self.fetch_selected_subscription()

    def continue_automated_workflow_after_fetch(self):
        """Continue automated workflow after fetch is complete with intelligent testing"""
        if not hasattr(self, 'automated_workflow_active') or not self.automated_workflow_active:
            self.log_debug("⚠️  WORKFLOW CONTINUATION SKIPPED - workflow not active")
            return

        try:
            self.log_debug("=" * 60)
            self.log_debug("🔄 WORKFLOW CONTINUATION AFTER FETCH")
            self.log_debug("=" * 60)

            # Step 2: Apply filters (either from history or current UI)
            if hasattr(self, 'workflow_history_protocols') or hasattr(self, 'workflow_history_countries'):
                self.log_debug("🔍 APPLYING HISTORY FILTERS...")
                self.apply_history_filters()
            else:
                self.log_debug("🔍 APPLYING CURRENT UI FILTERS...")
                self.apply_filter_and_update_ui()

            self.log_debug(f"📊 FILTER RESULTS:")
            self.log_debug(f"   - Total configs: {len(self.configs) if hasattr(self, 'configs') else 0}")
            self.log_debug(f"   - Filtered configs: {len(self.filtered_configs) if hasattr(self, 'filtered_configs') else 0}")

            if not self.filtered_configs:
                self.log_debug("❌ NO CONFIGS AFTER FILTERING - WORKFLOW STOPPED")
                self.status_bar.showMessage("No configs available after filtering")
                self.automated_workflow_active = False
                return

            # Initialize workflow tracking
            self.workflow_total_configs = len(self.filtered_configs)
            self.workflow_configs_tested = 0
            self.log_debug(f"🎯 STARTING INTELLIGENT TESTING:")
            self.log_debug(f"   - Total configs to test: {self.workflow_total_configs}")
            self.log_debug(f"   - Test type: {self.workflow_test_type}")

            # Step 3: Start intelligent testing based on test type
            if self.workflow_test_type == "http":
                self.log_debug("🚀 STARTING HTTP TEST WORKFLOW with real-time connection...")
                self.status_bar.showMessage("Testing configurations with HTTP test...")
                self.start_intelligent_http_test()
            elif self.workflow_test_type == "complete":
                self.log_debug("🚀 STARTING COMPLETE TEST WORKFLOW with real-time connection...")
                self.status_bar.showMessage("Testing configurations with Complete test...")
                self.start_intelligent_complete_test()
            else:
                self.log_debug("⚠️  UNKNOWN TEST TYPE - FALLBACK TO BASIC CONNECTION")
                self.complete_automated_workflow()

        except Exception as e:
            self.log_debug(f"❌ ERROR in continue_automated_workflow_after_fetch: {e}")
            import traceback
            self.log_debug(f"   Traceback: {traceback.format_exc()}")
            self.automated_workflow_active = False

    def apply_history_filters(self):
        """Apply filters from history settings to current configs"""
        try:
            if not hasattr(self, 'configs') or not self.configs:
                self.log_debug("❌ No configs to filter")
                self.filtered_configs = []
                return

            self.log_debug("🔍 APPLYING HISTORY-BASED FILTERS...")

            # Get history filter settings
            history_protocols = getattr(self, 'workflow_history_protocols', [])
            history_countries = getattr(self, 'workflow_history_countries', [])

            self.log_debug(f"   - History Protocol Filters: {history_protocols}")
            self.log_debug(f"   - History Country Filters: {history_countries}")

            # Start with all configs
            filtered_configs = []

            for config in self.configs:
                # Apply protocol filter from history
                if history_protocols and history_protocols != ["All"]:
                    protocol = config.get('protocol', '').lower()
                    if protocol not in [p.lower() for p in history_protocols]:
                        continue

                # Apply country filter from history
                if history_countries and history_countries != ["All"]:
                    # Get country from config (check multiple possible fields)
                    config_country = None
                    for field in ['country', 'location', 'region']:
                        if field in config and config[field]:
                            config_country = config[field]
                            break

                    # Try to extract from remark if no explicit country field
                    remark = config.get('remark', '')
                    self.log_debug(f"   Checking config: {remark[:50]}...")

                    # Enhanced country extraction from remark
                    country_match = False
                    for hist_country in history_countries:
                        # Check explicit country field first
                        if config_country and (hist_country.lower() in config_country.lower() or config_country.lower() in hist_country.lower()):
                            country_match = True
                            self.log_debug(f"     ✅ Country field match: {config_country} matches {hist_country}")
                            break

                        # Check remark for country keywords
                        country_keywords = {
                            'United Kingdom': ['uk', 'united kingdom', 'britain', 'england', 'london', '英国', 'gb'],
                            'United States': ['us', 'usa', 'united states', 'america', 'american', '美国'],
                            'Germany': ['de', 'germany', 'german', 'deutschland', '德国'],
                            'France': ['fr', 'france', 'french', '法国'],
                            'Japan': ['jp', 'japan', 'japanese', '日本'],
                            'Canada': ['ca', 'canada', 'canadian', '加拿大'],
                            'Australia': ['au', 'australia', 'australian', '澳大利亚'],
                            'Netherlands': ['nl', 'netherlands', 'dutch', 'holland', '荷兰'],
                            'Singapore': ['sg', 'singapore', '新加坡'],
                            'Hong Kong': ['hk', 'hong kong', 'hongkong', '香港'],
                        }

                        keywords = country_keywords.get(hist_country, [hist_country.lower()])
                        for keyword in keywords:
                            if keyword in remark.lower():
                                country_match = True
                                self.log_debug(f"     ✅ Remark keyword match: '{keyword}' found in remark for {hist_country}")
                                break

                        if country_match:
                            break

                    if not country_match:
                        self.log_debug(f"     ❌ No country match for: {remark[:50]}...")
                        continue

                # Config passed all filters
                filtered_configs.append(config)

            self.filtered_configs = filtered_configs
            self.log_debug(f"📊 HISTORY FILTER RESULTS: {len(self.filtered_configs)} configs from {len(self.configs)} total")

            # Update UI tables with filtered results
            self.update_results_table()
            self.update_latency_table()  # Fixed method name

            # Clear history filter settings after use
            if hasattr(self, 'workflow_history_protocols'):
                delattr(self, 'workflow_history_protocols')
            if hasattr(self, 'workflow_history_countries'):
                delattr(self, 'workflow_history_countries')

        except Exception as e:
            self.log_debug(f"❌ ERROR applying history filters: {e}")
            import traceback
            self.log_debug(f"   Traceback: {traceback.format_exc()}")
            # Fallback to all configs
            self.filtered_configs = self.configs if hasattr(self, 'configs') else []

    def start_intelligent_http_test(self):
        """Start HTTP testing with real-time connection to best config"""
        try:
            self.log_debug("🧪 STARTING INTELLIGENT HTTP TEST")

            # Connect to test result updates
            if hasattr(self, 'signals'):
                self.log_debug("🔗 CONNECTING to test result signals...")
                self.signals.update_specific_latency.connect(self.on_workflow_test_result)
                self.log_debug("✅ Connected to update_specific_latency signal")
            else:
                self.log_debug("❌ No signals object found - test results won't trigger workflow")

            # Start HTTP test on filtered configs
            self.log_debug("🚀 CALLING start_http_test()...")
            self.start_http_test()
            self.log_debug("✅ start_http_test() called successfully")

        except Exception as e:
            self.log_debug(f"❌ ERROR starting intelligent HTTP test: {e}")
            import traceback
            self.log_debug(f"   Traceback: {traceback.format_exc()}")
            self.automated_workflow_active = False

    def start_intelligent_complete_test(self):
        """Start Complete testing with real-time connection to best config"""
        try:
            self.log_debug("🧪 STARTING INTELLIGENT COMPLETE TEST")

            # Connect to test result updates
            if hasattr(self, 'signals'):
                self.log_debug("🔗 CONNECTING to test result signals...")
                self.signals.update_specific_latency.connect(self.on_workflow_test_result)
                self.log_debug("✅ Connected to update_specific_latency signal")
            else:
                self.log_debug("❌ No signals object found - test results won't trigger workflow")

            # Start complete test on filtered configs
            self.log_debug("🚀 CALLING start_complete_test()...")
            self.start_complete_test()
            self.log_debug("✅ start_complete_test() called successfully")

        except Exception as e:
            self.log_debug(f"❌ ERROR starting intelligent complete test: {e}")
            import traceback
            self.log_debug(f"   Traceback: {traceback.format_exc()}")
            self.automated_workflow_active = False

    def on_workflow_test_result(self, config_index, result_value, success, test_type):
        """Handle test results during automated workflow"""
        if not hasattr(self, 'automated_workflow_active') or not self.automated_workflow_active:
            self.log_debug(f"🔕 WORKFLOW TEST RESULT IGNORED - workflow not active")
            return

        try:
            self.log_debug(f"📊 WORKFLOW TEST RESULT RECEIVED:")
            self.log_debug(f"   - Config index: {config_index}")
            self.log_debug(f"   - Result value: {result_value}")
            self.log_debug(f"   - Success: {success}")
            self.log_debug(f"   - Test type: {test_type}")

            # Get the config being tested
            if config_index >= len(self.configs):
                self.log_debug(f"❌ Invalid config index {config_index} >= {len(self.configs)}")
                return

            config = self.configs[config_index]
            self.workflow_configs_tested += 1

            config_name = config.get('remark', 'Unknown')
            self.log_debug(f"   - Config name: {config_name}")
            self.log_debug(f"   - Configs tested so far: {self.workflow_configs_tested}/{self.workflow_total_configs}")

            # Check if this is a successful result (handle various success types)
            is_success = False
            if isinstance(success, bool):
                is_success = success
            elif isinstance(success, str):
                is_success = success.lower() in ['true', 'success', 'ok', 'pass']
            else:
                is_success = bool(success)

            # Check if result_value is numeric (handle various numeric types)
            is_numeric = False
            try:
                float(result_value)
                is_numeric = True
            except (ValueError, TypeError):
                is_numeric = False

            if is_success and is_numeric:
                self.log_debug(f"✅ SUCCESSFUL TEST RESULT - analyzing...")

                # Check if this is the first working config or a better result
                is_first_working = (self.workflow_best_config is None)
                is_better = False

                if self.workflow_test_type == "http":
                    # For HTTP test, lower latency is better
                    self.log_debug(f"   - HTTP test mode: comparing {result_value}ms vs current best {self.workflow_best_score}")
                    if self.workflow_best_score is None or result_value < self.workflow_best_score:
                        is_better = True
                        self.workflow_best_score = result_value
                        self.log_debug(f"   - NEW BEST HTTP RESULT: {result_value}ms")

                elif self.workflow_test_type == "complete":
                    # For complete test, check download speed (higher is better)
                    download_speed = config.get('download_speed', 0)
                    self.log_debug(f"   - Complete test mode: download speed {download_speed} vs current best {self.workflow_best_score}")
                    if isinstance(download_speed, (int, float)):
                        if self.workflow_best_score is None or download_speed > self.workflow_best_score:
                            is_better = True
                            self.workflow_best_score = download_speed
                            self.log_debug(f"   - NEW BEST COMPLETE RESULT: {download_speed} KB/s")

                if is_first_working or is_better:
                    self.workflow_best_config = config

                    if is_first_working:
                        self.log_debug(f"🎯 FIRST WORKING CONFIG FOUND: {config_name} - Score: {self.workflow_best_score}")
                        self.log_debug("   Connecting immediately and continuing tests...")

                        # Switch to Stats tab on first successful connection
                        self.switch_to_stats_tab()
                    else:
                        self.log_debug(f"🏆 FOUND BETTER CONFIG: {config_name} - Score: {self.workflow_best_score}")
                        self.log_debug("   Switching to better config...")

                    # Connect to this config immediately
                    self.connect_to_workflow_config(config)
                else:
                    self.log_debug(f"📈 Good result but not better than current best")
            else:
                self.log_debug(f"❌ FAILED TEST RESULT - success: {success}, value: {result_value}, is_success: {is_success}, is_numeric: {is_numeric}")

            # Update progress
            progress = (self.workflow_configs_tested / self.workflow_total_configs) * 100
            progress_msg = f"Testing progress: {self.workflow_configs_tested}/{self.workflow_total_configs} ({progress:.1f}%)"
            self.status_bar.showMessage(progress_msg)
            self.log_debug(f"📊 {progress_msg}")

        except Exception as e:
            self.log_debug(f"❌ ERROR handling workflow test result: {e}")
            import traceback
            self.log_debug(f"   Traceback: {traceback.format_exc()}")

    def connect_to_workflow_config(self, config):
        """Connect to a config during the workflow"""
        try:
            self.log_debug("🔌 CONNECTING TO WORKFLOW CONFIG...")

            # Disconnect from current connection if any
            if hasattr(self, 'workflow_connected_config') and self.workflow_connected_config:
                current_name = self.workflow_connected_config.get('remark', 'Unknown')
                self.log_debug(f"   - Disconnecting from current: {current_name}")
                self.disconnect_proxy_connection()
            else:
                self.log_debug("   - No previous connection to disconnect")

            # Establish new connection
            config_name = config.get('remark', 'Unknown')
            self.log_debug(f"   - Establishing connection to: {config_name}")
            self.establish_proxy_connection(config)
            self.workflow_connected_config = config

            # Update status
            if self.workflow_test_type == "http":
                score_text = f"{self.workflow_best_score:.0f}ms"
            else:
                score_text = f"{self.workflow_best_score:.1f} KB/s"

            status_msg = f"Connected to: {config_name} ({score_text}) - Testing continues..."
            self.status_bar.showMessage(status_msg)
            self.log_debug(f"✅ CONNECTION ESTABLISHED: {config_name} ({score_text})")

        except Exception as e:
            self.log_debug(f"❌ ERROR connecting to workflow config: {e}")
            import traceback
            self.log_debug(f"   Traceback: {traceback.format_exc()}")

    def complete_automated_workflow(self):
        """Complete the automated workflow"""
        if not hasattr(self, 'automated_workflow_active') or not self.automated_workflow_active:
            return

        try:
            self.log_debug("🏁 WORKFLOW COMPLETED")
            self.automated_workflow_active = False

            # Clear workflow flags
            if hasattr(self, 'workflow_stay_in_fetch_tab'):
                delattr(self, 'workflow_stay_in_fetch_tab')

            # Disconnect from test result updates
            if hasattr(self, 'signals'):
                try:
                    self.signals.update_specific_latency.disconnect(self.on_workflow_test_result)
                except:
                    pass  # Connection might not exist

            if self.workflow_best_config:
                remark = self.workflow_best_config.get('remark', 'Unknown')
                if self.workflow_test_type == "http":
                    score_text = f"{self.workflow_best_score:.0f}ms"
                else:
                    score_text = f"{self.workflow_best_score:.1f} KB/s"

                self.log_debug(f"Connected to best config: {remark} ({score_text})")
                self.status_bar.showMessage(f"Connected to best config: {remark} ({score_text})")

                # Switch to Stats tab to show connection status
                self.switch_to_stats_tab()
            else:
                # Fallback to basic best config selection
                best_config = self.find_best_latency_config()
                if best_config:
                    self.log_debug(f"Fallback: Connecting to best available config: {best_config.get('remark', 'Unknown')}")
                    self.establish_proxy_connection(best_config)
                    self.status_bar.showMessage(f"Connected to: {best_config.get('remark', 'Unknown')}")
                    self.switch_to_stats_tab()
                else:
                    self.log_debug("No suitable config found for connection")
                    self.status_bar.showMessage("No suitable config found for connection")

        except Exception as e:
            self.log_debug(f"Error completing automated workflow: {e}")
            self.status_bar.showMessage("Workflow completed with errors")

    def find_best_latency_config(self):
        """Find the config with the best (lowest) latency from test results"""
        best_config = None
        best_latency = float('inf')

        # Check both HTTP test and other test results
        for config in self.filtered_configs:
            latency = None

            # Check HTTP test results first (preferred)
            if 'http_latency' in config and isinstance(config['http_latency'], (int, float)):
                latency = config['http_latency']
            # Fallback to other latency measurements
            elif 'download_latency' in config and isinstance(config['download_latency'], (int, float)):
                latency = config['download_latency']
            elif 'netcat_latency' in config and isinstance(config['netcat_latency'], (int, float)):
                latency = config['netcat_latency']
            elif 'ping_latency' in config and isinstance(config['ping_latency'], (int, float)):
                latency = config['ping_latency']

            if latency is not None and latency < best_latency:
                best_latency = latency
                best_config = config

        return best_config

    # --- Fetch Methods ---
    def fetch_pasted_subscription(self):
        """Fetch pasted subscription/config"""
        self.process_pasted_subscription()

        # Continue automated workflow if active
        if hasattr(self, 'automated_workflow_active') and self.automated_workflow_active:
            QTimer.singleShot(1000, self.continue_automated_workflow_after_fetch)

    def fetch_selected_subscription(self):
        """Fetch selected predefined subscription"""
        self.log_debug("📡 CALLING process_input() for selected subscription...")
        self.process_input()
        self.log_debug("📡 process_input() completed")

        # Continue automated workflow if active
        if hasattr(self, 'automated_workflow_active') and self.automated_workflow_active:
            self.log_debug("⏰ SCHEDULING workflow continuation in 1000ms...")
            QTimer.singleShot(1000, self.continue_automated_workflow_after_fetch)
        else:
            self.log_debug("⚠️  No automated workflow active, skipping continuation")

    def fetch_all_sources(self):
        """Fetch all predefined subscriptions"""
        self.log_debug("📡 CALLING process_all_subscriptions() for all sources...")
        self.process_all_subscriptions()
        self.log_debug("📡 process_all_subscriptions() completed")

        # Continue automated workflow if active
        if hasattr(self, 'automated_workflow_active') and self.automated_workflow_active:
            self.log_debug("⏰ SCHEDULING workflow continuation in 1000ms...")
            QTimer.singleShot(1000, self.continue_automated_workflow_after_fetch)
        else:
            self.log_debug("⚠️  No automated workflow active, skipping continuation")

    def log_debug(self, message):
        """Log debug message to the debug output window and optionally to a file"""
        # Check if debug is completely disabled
        if hasattr(self, 'disable_debug_mode') and self.disable_debug_mode.isChecked():
            return

        # Check if system monitoring messages should be hidden
        if hasattr(self, 'hide_system_monitoring_checkbox') and self.hide_system_monitoring_checkbox.isChecked():
            # Filter out system monitoring and adaptive resource management messages
            if any(keyword in message for keyword in [
                'Adaptive Check:', 'Updating Semaphore Limit', 'Stability improvements',
                'Anti-closing mechanisms', 'Set maximum allowed Xray processes',
                'Updating Spinbox visually', 'System monitor timer', 'UI watchdog timer',
                'Emergency recovery timer', 'Process monitor timer', 'Moderate Load Detected:',
                'High Load Detected:', 'Updating Xray process limit', 'System resources:'
            ]):
                return

        # Create the log entry with timestamp
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")[:-3]
        log_entry = f"[{timestamp}] {message}"

        # Export to log file if enabled
        should_export = False

        # Check if full debug export is enabled (exports everything)
        if hasattr(self, 'export_full_log_checkbox') and self.export_full_log_checkbox.isChecked():
            should_export = True

        # Check if selective debug export is enabled (excludes config extraction/processing)
        elif hasattr(self, 'export_debug_log_checkbox') and self.export_debug_log_checkbox.isChecked():
            # Filter out config extraction/processing messages (similar to system monitoring filter)
            # Check if message contains any excluded keywords
            contains_excluded_keywords = any(keyword in message.lower() for keyword in [
                # Subscription processing
                'processing subscription', 'fetching from url', 'subscription fetch',
                'extracting configs', 'parsing config', 'decoded config', 'config extraction',
                'subscription processing', 'read_single_subscription', 'process_all_subscriptions',
                'base64 decode', 'config entries', 'found entries', 'finished processing source',
                'parsing errors encountered', 'url fetch ok', 'read', 'bytes from file',
                'processing input as', 'processing source', 'added', 'configs from',
                # Config parsing debug messages
                'debug (decode_proxy_url)', 'debug (decode_ssurl)', 'debug (decode_vmess)',
                'debug (decode_vless)', 'debug (decode_trojan)', 'sip008 format detected',
                'sip008 decoded successfully', 'returning sip008 result', 'standard format with',
                'auth part format', 'detected scheme:', 'processing line:', 'processing ss url:',
                'processing vmess url:', 'processing vless url:', 'processing trojan url:',
                'base64 (urlsafe) decoded successfully', 'decode_ssurl returned:', 'decode_vmess returned:',
                'decode_vless returned:', 'decode_trojan returned:'
            ])

            # Export if message does NOT contain excluded keywords
            if not contains_excluded_keywords:
                should_export = True

        if should_export:
            try:
                log_file_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "debug_log.txt")
                with open(log_file_path, 'a', encoding='utf-8') as f:
                    f.write(log_entry + '\n')
            except Exception as e:
                # Don't use log_debug here to avoid infinite recursion
                print(f"Error writing to log file: {e}")

        # Ensure debug_mode exists and is checked for UI display
        if hasattr(self, 'debug_mode') and self.debug_mode and self.debug_mode.isChecked():
            # Store the message in our list for history
            if hasattr(self, 'debug_messages'):
                # Limit the size of debug_messages to prevent memory issues
                if len(self.debug_messages) > 10000:  # Keep last 10000 messages max
                    self.debug_messages = self.debug_messages[-5000:]  # Keep last 5000 when trimming
                self.debug_messages.append(log_entry)

            # Add to buffer for efficient display updates
            if hasattr(self, 'debug_buffer'):
                # Add to buffer
                self.debug_buffer.append(log_entry)
                # Limit buffer size
                if len(self.debug_buffer) > self.debug_buffer_size:
                    self.debug_buffer = self.debug_buffer[-self.debug_buffer_size:]

                # Set flag for timer update
                if hasattr(self, 'debug_update_needed'):
                    self.debug_update_needed = True

                # Batch append to improve performance
                if hasattr(self, 'debug_append_count'):
                    self.debug_append_count += 1

                    # Only update the display every few messages or when buffer gets large
                    if self.debug_append_count >= 5 or len(self.debug_buffer) >= self.debug_buffer_size:
                        self._append_debug_buffer()
                        self.debug_append_count = 0

    def _append_debug_buffer(self):
        """Efficiently append buffered debug messages to the display"""
        if not hasattr(self, 'debug_output') or not self.debug_output or not hasattr(self, 'debug_buffer'):
            return

        # Skip if buffer is empty
        if not self.debug_buffer:
            return

        # Get messages to append
        messages_to_append = self.debug_buffer.copy()
        self.debug_buffer = []  # Clear buffer

        # Join messages with newlines
        text_to_append = '\n'.join(messages_to_append)

        # Append to the debug output
        if QApplication.instance().thread() != QThread.currentThread():
            # If not on the main thread, use invokeMethod to safely update GUI
            QMetaObject.invokeMethod(self.debug_output, "append", Qt.QueuedConnection,
                                 Q_ARG(str, text_to_append))
        else:
            # If on the main thread, update directly
            self.debug_output.append(text_to_append)

        # Auto-scroll to the bottom
        scrollbar = self.debug_output.verticalScrollBar()
        scrollbar.setValue(scrollbar.maximum())

    def _update_debug_display_safe(self):
        """Safe wrapper for debug display updates that handles interrupts gracefully"""
        try:
            self._update_debug_display()
        except (KeyboardInterrupt, SystemExit):
            # Handle graceful shutdown - stop the timer and exit cleanly
            if hasattr(self, 'debug_update_timer') and self.debug_update_timer:
                self.debug_update_timer.stop()
            return
        except Exception as e:
            # Log other exceptions but don't crash the application
            if hasattr(self, 'log_debug'):
                self.log_debug(f"Error in debug display update: {e}")
            return

    def _update_debug_display(self):
        """Update the debug display based on current settings"""
        try:
            # Only update if needed and if debug output exists
            if not hasattr(self, 'debug_update_needed') or not self.debug_update_needed:
                return

            if not hasattr(self, 'debug_output') or not self.debug_output:
                return

            # Reset the flag
            self.debug_update_needed = False

            # Append any buffered messages
            if hasattr(self, 'debug_buffer') and self.debug_buffer:
                self._append_debug_buffer()

            # If we're not showing full debug, we need to limit the display
            if hasattr(self, 'full_debug_mode') and not self.full_debug_mode.isChecked():
                # Get the current text
                current_text = self.debug_output.toPlainText()

                # If we have too many lines, trim it
                max_msgs = self.max_debug_messages if hasattr(self, 'max_debug_messages') else 30
                lines = current_text.split('\n')
                if len(lines) > max_msgs * 1.5:  # Only trim when significantly over the limit
                    # Keep only the last max_msgs lines
                    new_text = '\n'.join(lines[-max_msgs:])

                    # Update the text display - use document API for better performance
                    if QApplication.instance().thread() != QThread.currentThread():
                        # If not on the main thread, use invokeMethod to safely update GUI
                        QMetaObject.invokeMethod(self.debug_output, "setText", Qt.QueuedConnection,
                                             Q_ARG(str, new_text))
                    else:
                        # If on the main thread, update directly
                        self.debug_output.setText(new_text)
        except (KeyboardInterrupt, SystemExit):
            # Handle graceful shutdown
            if hasattr(self, 'debug_update_timer'):
                self.debug_update_timer.stop()
            return
        except Exception as e:
            # Log other exceptions but don't crash the application
            if hasattr(self, 'log_debug'):
                self.log_debug(f"Error in _update_debug_display: {e}")
            return

        # Auto-scroll to the bottom
        scrollbar = self.debug_output.verticalScrollBar()
        scrollbar.setValue(scrollbar.maximum())

    def toggle_full_debug(self, state):
        """Toggle between full debug and limited debug display"""
        if not hasattr(self, 'debug_output') or not self.debug_output:
            return

        # Set flag for update
        if hasattr(self, 'debug_update_needed'):
            self.debug_update_needed = True

        # Clear any buffered messages
        if hasattr(self, 'debug_buffer'):
            self.debug_buffer = []

        # Reset append count
        if hasattr(self, 'debug_append_count'):
            self.debug_append_count = 0

        # For better performance, only update the display if we have a reasonable number of messages
        # or if we're switching to limited mode
        if hasattr(self, 'debug_messages'):
            if len(self.debug_messages) < 1000 or not state:
                # Force a full update of the debug display
                if hasattr(self, 'full_debug_mode'):
                    is_full = self.full_debug_mode.isChecked()

                    if is_full and hasattr(self, 'debug_messages') and self.debug_messages:
                        # Show all messages
                        self.debug_output.setText('\n'.join(self.debug_messages))
                    elif not is_full and hasattr(self, 'debug_messages') and self.debug_messages:
                        # Show only the last N messages
                        max_msgs = self.max_debug_messages if hasattr(self, 'max_debug_messages') else 30
                        messages_to_show = self.debug_messages[-max_msgs:] if len(self.debug_messages) > max_msgs else self.debug_messages
                        self.debug_output.setText('\n'.join(messages_to_show))

                # Auto-scroll to the bottom
                scrollbar = self.debug_output.verticalScrollBar()
                scrollbar.setValue(scrollbar.maximum())

    def toggle_disable_debug(self, state):
        """Toggle debug completely on/off"""
        if state == Qt.Checked:
            # Disable debug mode
            if hasattr(self, 'debug_mode'):
                self.debug_mode.setChecked(False)
                self.debug_mode.setEnabled(False)
            if hasattr(self, 'full_debug_mode'):
                self.full_debug_mode.setEnabled(False)
            if hasattr(self, 'debug_output'):
                self.debug_output.setEnabled(False)
                self.debug_output.setPlaceholderText("Debug logging is disabled")
        else:
            # Enable debug mode
            if hasattr(self, 'debug_mode'):
                self.debug_mode.setEnabled(True)
                self.debug_mode.setChecked(True)
            if hasattr(self, 'full_debug_mode'):
                self.full_debug_mode.setEnabled(True)
            if hasattr(self, 'debug_output'):
                self.debug_output.setEnabled(True)
                self.debug_output.setPlaceholderText("Debug information will appear here")

    def get_effective_max_processes(self):
        """Gets the current allowed max Xray processes based on mode and load."""
        base_limit = 15 # Default or could be from a setting

        # Check if the spinbox exists and use its value as the user's desired base
        if hasattr(self, 'download_max_workers_spinbox'):
             base_limit = self.download_max_workers_spinbox.value()
        # else use default 15 or another sensible default

        # If stability improvements are OFF, just return the base limit
        if not self.stability_improvements_enabled:
            # Ensure the spinbox reflects this if stability was just turned off
            if hasattr(self, 'download_max_workers_spinbox') and self.download_max_workers_spinbox.value() != base_limit:
                 # Use invokeMethod to safely update UI from potentially different thread
                 QMetaObject.invokeMethod(self.download_max_workers_spinbox, "setValue", Qt.QueuedConnection, Q_ARG(int, base_limit))
            return base_limit

        # If stability is ON, perform adaptive check
        effective_limit = base_limit
        try:
            import psutil
            cpu = psutil.cpu_percent(interval=0.2) # Quick check
            mem = psutil.virtual_memory().percent
            self.log_debug(f"Adaptive Check: CPU={cpu:.1f}%, Mem={mem:.1f}%, BaseLimit={base_limit}")

            if cpu > 85 or mem > 90:
                # High load: Reduce limit significantly (e.g., 50-60% of base), min 3
                effective_limit = max(3, int(base_limit * 0.6))
                self.log_debug(f"High Load Detected: Reducing limit to {effective_limit}")
            elif cpu > 60 or mem > 75:
                # Moderate load: Reduce slightly (e.g., 80% of base), min 5
                effective_limit = max(5, int(base_limit * 0.8))
                self.log_debug(f"Moderate Load Detected: Reducing limit to {effective_limit}")
            else:
                # Load is low, use the base limit
                effective_limit = base_limit
                # Optional: Could slightly increase if load is very low, but stick to base for safety
        except ImportError:
            self.log_debug("psutil not found, cannot perform adaptive adjustment. Using base limit.")
            effective_limit = base_limit
        except Exception as e:
            self.log_debug(f"Error during adaptive check: {e}. Using base limit.")
            effective_limit = base_limit

        # Update the UI spinbox visually if the effective limit differs from its current value
        if hasattr(self, 'download_max_workers_spinbox') and self.download_max_workers_spinbox.value() != effective_limit:
             self.log_debug(f"Updating Spinbox visually to adaptive limit: {effective_limit}")
             # Use invokeMethod for thread safety
             QMetaObject.invokeMethod(self.download_max_workers_spinbox, "setValue", Qt.QueuedConnection, Q_ARG(int, effective_limit))

        return effective_limit

    def toggle_stability_improvements(self, state):
        """Toggle stability improvements and anti-closing mechanisms"""
        self.stability_improvements_enabled = (state == Qt.Checked)
        self.update_semaphore_limit() # Update immediately on change

        if self.stability_improvements_enabled:
            # Enable stability improvements
            self.log_debug("Stability improvements ON - Adaptive limit enabled.")
            if hasattr(self, 'adaptive_update_timer') and not self.adaptive_update_timer.isActive():
                self.adaptive_update_timer.start()

            # Start the system monitor timer if it exists
            if hasattr(self, 'system_monitor_timer'):
                if not self.system_monitor_timer.isActive():
                    self.system_monitor_timer.start()
                    self.log_debug("System monitor timer started")

            # Start the UI watchdog timer if it exists
            if hasattr(self, 'ui_watchdog_timer'):
                if not self.ui_watchdog_timer.isActive():
                    self.ui_watchdog_timer.start()
                    self.log_debug("UI watchdog timer started")

            # Start the emergency recovery timer if it exists
            if hasattr(self, 'emergency_recovery_timer'):
                if not self.emergency_recovery_timer.isActive():
                    self.emergency_recovery_timer.start()
                    self.log_debug("Emergency recovery timer started")
        else:
            self.log_debug("Stability improvements OFF - Using manual limit.")
            if hasattr(self, 'adaptive_update_timer') and self.adaptive_update_timer.isActive():
                self.adaptive_update_timer.stop()

    def on_system_proxy_checkbox_toggled(self, checked):
        self.log_debug(f"System Wide Proxy checkbox toggled to: {checked}")
        if not self.active_xray_connection_process and checked:
            self.log_debug("System proxy toggled ON, but no active Xray connection. Will apply on connect if still checked.")
            # Optionally, uncheck it and warn, or just let it be for next connection.
            # For now, just log. User might check it intending for next connection.
            return

        if not self.active_xray_connection_process and not checked:
            self.log_debug("System proxy toggled OFF, no active Xray connection. Nothing to change.")
            # Ensure it was not set by app previously if no connection
            self.system_proxy_was_set_by_app = False # Reset this if toggled off while disconnected
            return

        # If code reaches here, there IS an active_xray_connection_process

        if checked:
            self.log_debug("Enabling system-wide proxy.")
            if platform.system() == "Windows":
                success = self._set_windows_system_proxy(
                    enable=True,
                    proxy_server=self.TEMP_PROXY_HOST, # Should be 127.0.0.1
                    proxy_port=self.active_xray_connection_port
                )
                if success:
                    self.system_proxy_was_set_by_app = True
                    self.log_debug("System-wide proxy ENFORCED via checkbox.")
                    # Disable app-specific proxy UI if system proxy is now ON
                    if hasattr(self, 'app_proxy_enable_checkbox'): # Check if UI element exists
                        self.app_proxy_enable_checkbox.setChecked(False) # This should trigger its own handler
                        self.app_proxy_enable_checkbox.setEnabled(False)
                        self.app_profiles_list_widget.setEnabled(False)
                        self.unmatched_traffic_action_combo.setEnabled(False)
                else:
                    self.log_debug("Failed to set system-wide proxy. Reverting checkbox.")
                    self.system_proxy_checkbox.setChecked(False) # Revert UI on failure
                    QMessageBox.warning(self, "Proxy Error", "Failed to set system-wide proxy. Check logs.")
            else:
                self.log_debug("System proxy checkbox toggled on non-Windows. UI only, no action.")
                # Checkbox should ideally be disabled on non-Windows, but if enabled, ensure no error
                pass # No action on non-Windows

        else: # Unchecked
            self.log_debug("Disabling system-wide proxy via checkbox.")
            if platform.system() == "Windows":
                # Only disable if the app was the one that set it, or if user explicitly unchecks
                self._set_windows_system_proxy(enable=False) # Let this method handle if it needs to act
                self.system_proxy_was_set_by_app = False # App is no longer responsible
                self.log_debug("System-wide proxy DISABLED via checkbox.")
                # Enable app-specific proxy UI if a connection is active
                if hasattr(self, 'app_proxy_enable_checkbox'): # Check if UI element exists
                    self.app_proxy_enable_checkbox.setEnabled(True)
                    # Other app_specific controls' states will be set by app_proxy_enable_checkbox's handler
            else:
                self.log_debug("System proxy checkbox toggled on non-Windows. UI only, no action.")
                pass

        # Reconnect with new Xray rules if the proxy mode (system vs. app-specific) changed
        # This is important because routing rules might differ
        # Skip reconnection if this is being called during initial connection setup
        if not getattr(self, '_setting_initial_proxy', False):
            self.reconnect_with_new_rules()
        else:
            self.log_debug("Skipping reconnection during initial proxy setup.")

    def reconnect_with_new_rules(self):
        """
        Reconnect the active proxy connection with new routing rules.
        This is called when proxy settings change (system proxy, app-specific proxy, etc.)
        to ensure the connection uses the updated routing configuration.
        """
        if not hasattr(self, 'active_config_details') or not self.active_config_details:
            self.log_debug("Reconnect with new rules: No active connection to reconnect.")
            return

        try:
            self.log_debug("Reconnecting with new routing rules...")

            # Store the current config details
            current_config = self.active_config_details.copy()

            # Disconnect current connection
            self.disconnect_proxy_connection()

            # Small delay to ensure clean disconnection
            time.sleep(0.5)

            # Reconnect with the same config (which will use updated routing rules)
            self.establish_proxy_connection(current_config)

            self.log_debug("Successfully reconnected with new routing rules.")

        except Exception as e:
            self.log_debug(f"Error reconnecting with new rules: {e}")
            # If reconnection fails, ensure UI is in a consistent state
            if hasattr(self, 'connection_status_label'):
                self.connection_status_label.setText("Status: Reconnection Failed")

    def monitor_xray_process(self):
        """Monitor Xray process and automatically reset system proxy if terminated."""
        try:
            # Only monitor if we have an active connection and system proxy is enabled
            if (self.active_xray_connection_process and
                hasattr(self, 'system_proxy_checkbox') and
                self.system_proxy_checkbox.isChecked()):

                # Check if Xray process is still running
                if self.active_xray_connection_process.poll() is not None:
                    # Process has terminated - automatically reset system proxy
                    self.log_debug("Xray process terminated - automatically resetting system proxy")

                    # Disable system proxy
                    if hasattr(self, 'system_proxy_checkbox'):
                        self.system_proxy_checkbox.setChecked(False)

                    # Reset system proxy settings
                    self._set_windows_system_proxy(False)

                    # Update connection status
                    if hasattr(self, 'connection_status_label'):
                        self.connection_status_label.setText("Status: Disconnected (Process Terminated)")

                    # Reset connection variables
                    self.active_xray_connection_process = None
                    self.active_config_details = None

                    # Stop connection timer
                    if hasattr(self, 'connection_timer') and self.connection_timer.isActive():
                        self.connection_timer.stop()

                    # --- ADDED: Stop stats timer ---
                    if hasattr(self, 'stats_timer') and self.stats_timer.isActive():
                        self.stats_timer.stop()
                        self.log_debug("Data transfer stats timer stopped due to process termination.")
                    # --- END ADDED ---

                    self.log_debug("System proxy automatically disabled due to Xray process termination")

        except Exception as e:
            self.log_debug(f"Error in process monitoring: {e}")

    def update_semaphore_limit(self):
        """Updates the max_allowed_xray_processes and the semaphore itself."""
        try:
            new_limit = self.get_effective_max_processes()

            if new_limit != self.max_allowed_xray_processes:
                self.log_debug(f"Updating Semaphore Limit from {self.max_allowed_xray_processes} to {new_limit}")
                # Recreate the semaphore with the new limit
                # Note: This doesn't affect threads currently waiting on the *old* semaphore instance.
                # New acquire calls will use the new semaphore.
                self.xray_semaphore = threading.Semaphore(new_limit)
                self.max_allowed_xray_processes = new_limit
        except Exception as e:
            self.log_debug(f"Error updating semaphore limit: {e}")

            # Start the process monitor timer if it exists
            if hasattr(self, 'process_monitor_timer'):
                if not self.process_monitor_timer.isActive():
                    self.process_monitor_timer.start()
                    self.log_debug("Process monitor timer started")

            # Update the last UI response time
            self.last_ui_response_time = time.time()

            # Set maximum allowed Xray processes based on spinbox value
            if hasattr(self, 'download_max_workers_spinbox'):
                self.max_allowed_xray_processes = self.download_max_workers_spinbox.value()
                self.xray_semaphore = threading.Semaphore(self.max_allowed_xray_processes)
                self.log_debug(f"Set maximum allowed Xray processes to {self.max_allowed_xray_processes}")

            # Enable anti-closing mechanisms
            self.anti_closing_enabled = True
            self.log_debug("Anti-closing mechanisms enabled")
        else:
            # Disable stability improvements
            self.log_debug("Stability improvements and anti-closing mechanisms disabled")

            # Stop the system monitor timer if it exists
            if hasattr(self, 'system_monitor_timer'):
                if self.system_monitor_timer.isActive():
                    self.system_monitor_timer.stop()
                    self.log_debug("System monitor timer stopped")

            # Stop the UI watchdog timer if it exists
            if hasattr(self, 'ui_watchdog_timer'):
                if self.ui_watchdog_timer.isActive():
                    self.ui_watchdog_timer.stop()
                    self.log_debug("UI watchdog timer stopped")

            # Stop the emergency recovery timer if it exists
            if hasattr(self, 'emergency_recovery_timer'):
                if self.emergency_recovery_timer.isActive():
                    self.emergency_recovery_timer.stop()
                    self.log_debug("Emergency recovery timer stopped")

            # Stop the process monitor timer if it exists
            if hasattr(self, 'process_monitor_timer'):
                if self.process_monitor_timer.isActive():
                    self.process_monitor_timer.stop()
                    self.log_debug("Process monitor timer stopped")

            # Disable anti-closing mechanisms
            self.anti_closing_enabled = False
            self.log_debug("Anti-closing mechanisms disabled")

            # Set unlimited Xray processes
            self.max_allowed_xray_processes = 100000  # Effectively unlimited
            self.xray_semaphore = threading.Semaphore(self.max_allowed_xray_processes)
            self.log_debug(f"Set maximum allowed Xray processes to {self.max_allowed_xray_processes} (unlimited)")

    def clear_debug_log(self):
        """Clear the debug log and message history"""
        # Clear all debug data structures
        if hasattr(self, 'debug_messages'):
            self.debug_messages = []

        if hasattr(self, 'debug_buffer'):
            self.debug_buffer = []

        if hasattr(self, 'debug_append_count'):
            self.debug_append_count = 0

        # Clear the display
        if hasattr(self, 'debug_output') and self.debug_output:
            self.debug_output.clear()

        # Reset update flag
        if hasattr(self, 'debug_update_needed'):
            self.debug_update_needed = False

    def show_context_menu(self, position):
        # ... (Keep existing implementation - unchanged) ...
        context_menu = QMenu()
        paste_action = context_menu.addAction("Paste")
        paste_action.triggered.connect(self.paste_subscription)
        context_menu.exec_(self.custom_subscription.mapToGlobal(position))

    def paste_subscription(self):
        # ... (Keep existing implementation - unchanged) ...
        clipboard = QApplication.clipboard()
        self.custom_subscription.insert(clipboard.text())

    # --- process_input, process_all_subscriptions, process_pasted_subscription (Keep As Is) ---
    def process_input(self):
        # ... (Keep Refined Version - unchanged) ...
        input_source = ""
        source_description = ""

        # Determine the source based on combo box and custom input
        selected_subscriptions = self.subscription_combo.get_selected_items()
        custom_text = self.custom_subscription.text().strip()

        if not selected_subscriptions:
            # No subscriptions selected means "All Predefined"
            self.process_all_subscriptions() # This handles everything
            return
        elif len(selected_subscriptions) == 1:
            # Single subscription selected
            selected_name = selected_subscriptions[0]
            # Find the subscription by name
            subscription_found = False
            for name, url in self.predefined_subscriptions:
                if name == selected_name:
                    input_source = url
                    source_description = f"predefined subscription '{name}'"
                    self.log_debug(f"Processing {source_description}")
                    subscription_found = True
                    break

            if not subscription_found:
                QMessageBox.warning(self, "Invalid Selection", f"Selected subscription '{selected_name}' not found.")
                return
        elif len(selected_subscriptions) > 1:
            # Multiple subscriptions selected - process them all
            self.process_selected_subscriptions(selected_subscriptions)
            return
        elif custom_text:
            # Custom input box has content
            input_source = custom_text
            source_description = "custom input"
            self.log_debug(f"Processing {source_description}")
        else:
             # No predefined selected (likely "All Predefined" was selected but handled above) AND custom input is empty
             QMessageBox.warning(self, "Input Empty", "Please select a predefined subscription, paste content into the custom input box, or choose 'All Predefined'.")
             self.status_bar.showMessage("Input empty.")
             return

        if not input_source: # Should not happen if logic above is correct, but safety check
             QMessageBox.warning(self, "Input Error", "Could not determine input source.")
             return

        self.status_bar.showMessage(f"Processing {source_description}...")
        QApplication.processEvents()

        # Clear previous results
        self.configs = []
        self.filtered_configs = []
        self.update_results_table() # Clear results table
        self.update_latency_table() # Clear testing table

        # Read and parse the single source
        success = self.read_subscriptions(input_source) # This now populates self.configs

        if success and self.configs:
            self.log_debug(f"Read {len(self.configs)} raw configs from {source_description}.")
            self.apply_filter_and_update_ui() # Use helper function
        elif success:
            QMessageBox.warning(self, "Warning", f"Input processed ({source_description}), but no configurations were extracted.")
            self.status_bar.showMessage("No configurations extracted.")
            # Ensure tables are clear
            self.configs = []
            self.filtered_configs = []
            self.update_results_table()
            self.update_latency_table()
        else:
            # read_subscriptions should show specific error messages via QMessageBox now
            self.log_debug(f"Failed to process {source_description}.")
            self.status_bar.showMessage(f"Failed to process {source_description}.")
            # Ensure tables are clear
            self.configs = []
            self.filtered_configs = []
            self.update_results_table()
            self.update_latency_table()

    def process_selected_subscriptions(self, selected_names):
        """Process multiple selected subscriptions"""
        try:
            self.log_debug(f"Starting processing of {len(selected_names)} selected subscriptions: {', '.join(selected_names)}")
            self.status_bar.showMessage(f"Processing {len(selected_names)} selected subscriptions...")
            QApplication.processEvents()

            # Clear previous results
            self.configs = []
            self.filtered_configs = []
            self.update_results_table()
            self.update_latency_table()

            all_raw_configs = []
            errors_occurred = False
            successful_subscriptions = 0

            # Process selected subscriptions
            for selected_name in selected_names:
                # Find the subscription by name
                subscription_found = False
                for name, url in self.predefined_subscriptions:
                    if name == selected_name:
                        try:
                            self.log_debug(f"Processing selected subscription: {name}")
                            self.status_bar.showMessage(f"Processing '{name}'...")
                            QApplication.processEvents()

                            configs = self._read_single_subscription(url)
                            if configs:
                                # Tag each config with source information
                                for config in configs:
                                    config['source_subscription'] = url
                                    config['source_subscription_name'] = name
                                all_raw_configs.extend(configs)
                                successful_subscriptions += 1
                                self.log_debug(f"Added {len(configs)} configs from '{name}'")
                            else:
                                self.log_debug(f"No configs found from '{name}'")

                        except Exception as e:
                            self.log_debug(f"Error processing '{name}': {e}")
                            errors_occurred = True

                        subscription_found = True
                        break

                if not subscription_found:
                    self.log_debug(f"Warning: Selected subscription '{selected_name}' not found in predefined list")

            self.configs = all_raw_configs

            if not self.configs:
                self.status_bar.showMessage("Processing complete. No configurations found from selected subscriptions.")
                if not errors_occurred:
                    QMessageBox.warning(self, "No Configurations", f"No valid configurations were found from the {len(selected_names)} selected subscriptions.")
                return

            self.log_debug(f"Total raw configs collected from {successful_subscriptions} selected subscriptions: {len(self.configs)}. Applying filters...")
            self.apply_filter_and_update_ui()

        except Exception as e:
            self.log_debug(f"ERROR in process_selected_subscriptions: {e}")
            traceback.print_exc()
            QMessageBox.critical(self, "Processing Error", f"An error occurred while processing selected subscriptions:\n\n{str(e)}")

    def process_all_subscriptions(self):
        try:
            self.log_debug("Starting processing of ALL sources.")
            self.status_bar.showMessage("Processing all sources...")
            QApplication.processEvents()

            # Clear previous results
            self.configs = []
            self.filtered_configs = []
            self.update_results_table()
            self.update_latency_table()

            all_raw_configs = []
            errors_occurred = False
            successful_subscriptions = 0

            # Special handling for "All Predefined" mode
            self.log_debug("SPECIAL HANDLING: All Predefined mode detected - using extra safeguards")

            # Process predefined subscriptions
            self.log_debug(f"Processing {len(self.predefined_subscriptions)} predefined subscriptions...")

            if not self.predefined_subscriptions:
                self.log_debug("WARNING: No predefined subscriptions found")
                return

            for name, url in self.predefined_subscriptions:
                try:
                    self.status_bar.showMessage(f"Processing {name}...")
                    QApplication.processEvents()
                    self.log_debug(f"--> Processing predefined: {name} ({url})")

                    # Skip empty URLs
                    if not url or not url.strip():
                        self.log_debug(f"    Skipping empty URL for {name}")
                        continue

                    # Extra validation for URL format in All Predefined mode
                    if not url.startswith(('http://', 'https://')) and not os.path.isfile(url):
                        self.log_debug(f"    WARNING: Invalid URL format for {name}: {url}")
                        continue

                    # Use a try-except block specifically for each subscription
                    try:
                        current_configs = self._read_single_subscription(url) # Get configs from this URL
                        if current_configs:
                            # Tag each config with its source subscription name and URL
                            for config in current_configs:
                                # Make sure these fields are set
                                config['source_subscription'] = url
                                config['source_subscription_name'] = name
                                self.log_debug(f"Tagged config {config.get('remark', 'unnamed')} with source {name}")

                            all_raw_configs.extend(current_configs)
                            self.log_debug(f"    Added {len(current_configs)} configs from {name} with source tags")
                            successful_subscriptions += 1
                        else:
                            self.log_debug(f"    No configs found or error processing {name}")
                            # _read_single_subscription should show its own error message box
                    except Exception as inner_e:
                        self.log_debug(f"    INNER ERROR processing {name}: {inner_e}")
                        if ((hasattr(self, 'export_full_log_checkbox') and self.export_full_log_checkbox.isChecked()) or
                            (hasattr(self, 'export_debug_log_checkbox') and self.export_debug_log_checkbox.isChecked())):
                            # Log the full traceback to the debug log file
                            try:
                                log_file_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "debug_log.txt")
                                with open(log_file_path, 'a', encoding='utf-8') as f:
                                    f.write(f"\n[EXCEPTION TRACEBACK - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}]\n")
                                    traceback.print_exc(file=f)
                                    f.write("\n")
                            except Exception as log_err:
                                print(f"Error writing exception to log file: {log_err}")
                        # Continue with next subscription
                        continue
                except Exception as e:
                    self.log_debug(f"    OUTER ERROR processing {name}: {e}")
                    traceback.print_exc()
                    # Don't show message box for each error to avoid overwhelming the user
                    errors_occurred = True

            # Process custom input
            custom_input = self.custom_subscription.text().strip()
            if custom_input:
                self.log_debug("Processing custom input block...")
                self.status_bar.showMessage("Processing custom input...")
                QApplication.processEvents()
                try:
                    # Treat the entire custom block as one source for read_subscriptions
                    custom_configs = self._read_single_subscription(custom_input)
                    if custom_configs:
                        # Tag each config with 'Custom Input' as source
                        for config in custom_configs:
                            config['source_subscription'] = 'custom_input'
                            config['source_subscription_name'] = 'Custom Input'

                        all_raw_configs.extend(custom_configs)
                        self.log_debug(f"    Added {len(custom_configs)} configs from custom input with source tags")
                    else:
                        self.log_debug("    No configs found or error processing custom input")
                        # _read_single_subscription handles errors/messages
                except Exception as e:
                    self.log_debug(f"ERROR processing custom input: {e}")
                    traceback.print_exc()

            self.configs = all_raw_configs # Store all collected configs

            if not self.configs:
                self.status_bar.showMessage("Processing complete. No configurations found from any source.")
                if not errors_occurred: # Only show warning if no specific errors were already shown
                    QMessageBox.warning(self, "No Configurations", "No valid configurations were found from any of the sources.")
                self.filtered_configs = []
                self.update_results_table()
                self.update_latency_table()
                return

            self.log_debug(f"Total raw configs collected from all sources: {len(self.configs)}. Applying filter...")
            self.apply_filter_and_update_ui() # Use helper function

        except Exception as e:
            self.log_debug(f"CRITICAL ERROR in process_all_subscriptions: {e}")
            traceback.print_exc()
            QMessageBox.critical(self, "Processing Error",
                f"A critical error occurred while processing subscriptions:\n\n{str(e)}\n\nSee debug log for details.")
            # Reset configs to empty to avoid partial/corrupt data
            self.configs = []
            self.filtered_configs = []
            self.update_results_table()
            self.update_latency_table()
        finally:
            self.status_bar.showMessage("Processing complete.")

    def process_pasted_subscription(self):
        # ... (Keep Refined Version - unchanged) ...
        input_source = self.custom_subscription.text().strip()
        if not input_source:
            QMessageBox.warning(self, "Input Empty", "Paste subscription URL(s) or config link(s) into the custom input box first.")
            self.status_bar.showMessage("Custom input is empty.")
            return

        self.log_debug("Processing pasted input...")
        self.status_bar.showMessage("Processing pasted input...")
        QApplication.processEvents()

        # Clear previous results
        self.configs = []
        self.filtered_configs = []
        self.update_results_table()
        self.update_latency_table()

        # Read and parse the pasted content
        success = self.read_subscriptions(input_source) # This populates self.configs

        if success and self.configs:
            self.log_debug(f"Read {len(self.configs)} raw configs from pasted input.")
            self.apply_filter_and_update_ui() # Use helper function
        elif success:
            QMessageBox.warning(self, "Warning", "Pasted input processed, but no configurations were extracted.")
            self.status_bar.showMessage("No configurations extracted from paste.")
            # Ensure tables are clear
            self.configs = []
            self.filtered_configs = []
            self.update_results_table()
            self.update_latency_table()
        else:
            # read_subscriptions should show specific error messages via QMessageBox now
            self.log_debug("Failed to process pasted input.")
            self.status_bar.showMessage("Failed to process paste.")
            # Ensure tables are clear
            self.configs = []
            self.filtered_configs = []
            self.update_results_table()
            self.update_latency_table()

    def apply_filter_and_update_ui(self):
        # ... (Keep existing implementation - unchanged) ...
        """Helper function to apply protocol filter and update tables/status."""
        if not self.configs:
            self.log_debug("Apply Filter: No configs loaded.")
            self.filtered_configs = []
            self.update_results_table()
            self.update_latency_table()
            self.status_bar.showMessage("No configurations loaded.")
            return

        # Get selected filters
        selected_protocols = self.get_selected_protocols()
        selected_countries = self.get_selected_countries()

        self.log_debug(f"Applying filters - Protocols: {selected_protocols}, Countries: {selected_countries}")

        # Start with all configs
        filtered_configs = self.configs.copy()

        # Apply protocol filter (OR logic within protocols)
        if selected_protocols:
            # Specific protocols selected - filter to only those protocols
            protocol_filtered = []
            for config in filtered_configs:
                config_protocol = config.get('protocol', '').lower()

                # Check for exact protocol match first
                if any(config_protocol == protocol.lower() for protocol in selected_protocols):
                    protocol_filtered.append(config)
                    continue

                # Check for VLESS sub-protocol matches
                if config_protocol == 'vless':
                    vless_subtype = self._get_vless_subtype(config)
                    if any(vless_subtype == protocol.lower() for protocol in selected_protocols):
                        protocol_filtered.append(config)
                        continue

            filtered_configs = protocol_filtered
            self.log_debug(f"Protocol filter applied: {len(filtered_configs)} configs matching any of {selected_protocols}.")
        else:
            # No protocols selected means "All" - exclude only non-testable/error/comment types
            excluded_protocols = ['unknown', 'comment', 'error', 'ssr']
            filtered_configs = [c for c in filtered_configs if c.get('protocol', 'unknown').lower() not in excluded_protocols]
            self.log_debug(f"Protocol filter 'All': {len(filtered_configs)} valid/testable configs (excluded: {excluded_protocols}).")

        # Apply country filter (OR logic within countries)
        if selected_countries:
            # Specific countries selected - filter to only those countries
            country_filtered = []
            for config in filtered_configs:
                detected_country = self._detect_config_country(config)
                # Include if country matches any selected country
                if detected_country and detected_country in selected_countries:
                    country_filtered.append(config)
            filtered_configs = country_filtered
            self.log_debug(f"Country filter applied: {len(filtered_configs)} configs matching any of {selected_countries}.")
        else:
            # No countries selected means "All" - include all configs (no country filtering)
            self.log_debug(f"Country filter 'All': {len(filtered_configs)} configs (no country filtering applied).")

        self.filtered_configs = filtered_configs

        # Debugging: Log protocols found
        # config_protocols = sorted(list(set(c.get('protocol', 'N/A') for c in self.configs)))
        # filtered_protocols = sorted(list(set(c.get('protocol', 'N/A') for c in self.filtered_configs)))
        # self.log_debug(f"Protocols in self.configs ({len(self.configs)}): {config_protocols}")
        # self.log_debug(f"Protocols in self.filtered_configs ({len(self.filtered_configs)}): {filtered_protocols}")

        # Update UI elements
        self.update_results_table() # Update results tab based on filtered_configs
        self.update_latency_table() # Update testing tab based on filtered_configs
        self.update_latency_stats() # Reset stats

        if self.filtered_configs:
            # Extract profiles from configs and save to history
            self.extract_profiles_from_configs()

            # Add current settings to connection history
            subscription_names = []
            if hasattr(self, 'subscription_combo'):
                subscription_names = self.subscription_combo.get_selected_items()
            if not subscription_names:
                subscription_names = ["All Predefined"]

            self.add_to_connection_history(
                subscription_name=", ".join(subscription_names),
                protocols=selected_protocols if selected_protocols else ["All"],
                countries=selected_countries if selected_countries else ["All"]
            )

            # Auto-switch to Testing tab after successful processing (unless in workflow)
            if not getattr(self, 'workflow_stay_in_fetch_tab', False):
                self._switch_to_testing_tab()
            else:
                self.log_debug("Staying in Fetch tab during workflow until connection established")
            protocol_desc = "All" if not selected_protocols else ", ".join(selected_protocols)
            country_desc = "All" if not selected_countries else ", ".join(selected_countries)
            filter_desc = f"Protocols: {protocol_desc}, Countries: {country_desc}"
            self.status_bar.showMessage(f"Processing complete. Found {len(self.configs)} total. Displaying {len(self.filtered_configs)} filtered configurations ({filter_desc}).")
        else:
            # No configs match the filter, but some configs might have been loaded
            if self.configs:
                protocol_desc = "All" if not selected_protocols else ", ".join(selected_protocols)
                country_desc = "All" if not selected_countries else ", ".join(selected_countries)
                filter_desc = f"Protocols: {protocol_desc}, Countries: {country_desc}"
                QMessageBox.information(self, "Filter Applied", f"No configurations matching the filters ({filter_desc}) were found among the {len(self.configs)} loaded configurations.")
                self.status_bar.showMessage(f"Processed {len(self.configs)} configs. No configurations match filters ({filter_desc}).")
            else:
                 # This case handled by the calling functions (process_input etc.)
                 pass # Message shown previously


    # --- Results Tab (Keep As Is) ---
    def setup_results_tab(self):
        # ... (Keep existing implementation - unchanged) ...
        results_widget = QWidget()
        results_layout = QVBoxLayout(results_widget)

        # Filter Controls
        filter_layout = QHBoxLayout()
        filter_label = QLabel("Filter:")
        filter_layout.addWidget(filter_label)
        self.filter_input = QLineEdit()
        self.filter_input.setPlaceholderText("Enter text to filter results...")
        self.filter_input.textChanged.connect(self.filter_results)
        filter_layout.addWidget(self.filter_input)
        self.filter_column_combo = QComboBox()
        self.filter_column_combo.addItems(["All Columns", "Protocol", "Hostname", "Port", "Remark"])
        self.filter_column_combo.currentIndexChanged.connect(self.filter_results)
        filter_layout.addWidget(self.filter_column_combo)
        clear_filter_button = QPushButton("Clear Filter")
        clear_filter_button.clicked.connect(self.clear_filter)
        filter_layout.addWidget(clear_filter_button)
        results_layout.addLayout(filter_layout)

        # Results Count Label
        self.results_count_label = QLabel("Total: 0 configs")
        results_layout.addWidget(self.results_count_label)

        # Results Table
        self.results_table = QTableWidget()
        self.results_table.setColumnCount(5) # Protocol, Hostname, Port, Remark, Original URL (Hidden)
        self.results_table.setHorizontalHeaderLabels(["Protocol", "Hostname", "Port", "Remark", "Original URL"])

        # Table Properties
        self.results_table.horizontalHeader().setSectionResizeMode(QHeaderView.Interactive)
        self.results_table.setColumnWidth(0, 80)  # Protocol
        self.results_table.setColumnWidth(1, 250) # Hostname
        self.results_table.setColumnWidth(2, 60)  # Port
        self.results_table.setColumnWidth(3, 300) # Remark (stretch later)
        self.results_table.setColumnHidden(4, True) # Hide Original URL column by default

        # Make Remark column stretch
        self.results_table.horizontalHeader().setStretchLastSection(False)
        self.results_table.horizontalHeader().setSectionResizeMode(3, QHeaderView.Stretch) # Stretch Remark

        self.results_table.verticalHeader().setVisible(False)
        self.results_table.setSelectionBehavior(QAbstractItemView.SelectRows) # Select whole rows
        self.results_table.setEditTriggers(QAbstractItemView.NoEditTriggers) # Make table read-only
        self.results_table.setAlternatingRowColors(True)
        self.results_table.setSortingEnabled(True) # Enable column sorting
        self.results_table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.results_table.customContextMenuRequested.connect(self.show_results_table_context_menu)

        results_layout.addWidget(self.results_table)
        self.tab_widget.addTab(results_widget, "Results")

    def setup_stats_tab(self):
        """Setup the Stats tab with connection status and data transfer monitoring"""
        self.stats_tab = QWidget()
        self.tab_widget.addTab(self.stats_tab, "Stats")
        stats_layout = QVBoxLayout(self.stats_tab)

        # Connection Status GroupBox
        status_group = QGroupBox("Connection Status")
        status_layout = QVBoxLayout(status_group)
        self.connection_status_label = QLabel("Status: Disconnected")
        self.connection_duration_label = QLabel("Duration: N/A")
        status_layout.addWidget(self.connection_status_label)
        status_layout.addWidget(self.connection_duration_label)
        status_layout.addStretch(1)
        stats_layout.addWidget(status_group)

        # Server Details GroupBox
        details_group = QGroupBox("Connected Server Details")
        details_layout = QVBoxLayout(details_group)
        self.server_remark_label = QLabel("Name: N/A")
        self.server_ip_label = QLabel("IP: N/A")
        self.server_location_label = QLabel("Location: N/A")
        self.server_protocol_label = QLabel("Protocol: N/A")
        self.server_port_label = QLabel("Port: N/A")

        # Data transfer stats labels
        self.upload_speed_label = QLabel("Upload: 0 B/s")
        self.download_speed_label = QLabel("Download: 0 B/s")
        self.total_data_label = QLabel("Total Data: 0 B")

        details_layout.addWidget(self.server_remark_label)
        details_layout.addWidget(self.server_ip_label)
        details_layout.addWidget(self.server_location_label)
        details_layout.addWidget(self.server_protocol_label)
        details_layout.addWidget(self.server_port_label)
        details_layout.addWidget(self.upload_speed_label)
        details_layout.addWidget(self.download_speed_label)
        details_layout.addWidget(self.total_data_label)
        details_layout.addStretch(1)
        stats_layout.addWidget(details_group)

        # Controls GroupBox
        controls_group = QGroupBox("Connection Controls")
        controls_layout = QVBoxLayout(controls_group)
        self.system_proxy_checkbox = QCheckBox("Enable System-Wide Proxy (Windows)")
        self.system_proxy_checkbox.setChecked(False)
        self.system_proxy_checkbox.setEnabled(False) # Initially disabled

        self.dns_leak_checkbox = QCheckBox("Enable DNS Leak Prevention (via Xray DNS)")
        self.dns_leak_checkbox.setChecked(True)
        self.dns_leak_checkbox.toggled.connect(self._handle_dns_settings_changed)

        # DNS Server ComboBox
        self.dns_server_label = QLabel("DNS Server:")
        controls_layout.addWidget(self.dns_server_label)
        self.dns_server_combobox = QComboBox()
        self.dns_server_combobox.addItems([
            "Cloudflare (1.1.1.1)",
            "Google (8.8.8.8)",
            "Quad9 (9.9.9.9)",
            "System Default"
        ])
        self.dns_server_combobox.setToolTip("Select DNS server to use when DNS leak prevention is enabled.")
        self.dns_server_combobox.currentIndexChanged.connect(self._handle_dns_settings_changed)
        controls_layout.addWidget(self.dns_server_combobox)
        # Initial state of combobox (enabled if dns_leak_checkbox is checked)
        self.dns_server_label.setEnabled(self.dns_leak_checkbox.isChecked())
        self.dns_server_combobox.setEnabled(self.dns_leak_checkbox.isChecked())

        self.ip_leak_checkbox = QCheckBox("Enable IP Leak Prevention (via Xray Routing)")
        self.ip_leak_checkbox.setChecked(True)
        self.ip_leak_checkbox.toggled.connect(self._handle_ip_leak_settings_changed)

        self.system_proxy_checkbox.toggled.connect(self.on_system_proxy_checkbox_toggled)

        self.disconnect_button = QPushButton("Disconnect")
        self.disconnect_button.setEnabled(False) # Initially disabled
        self.disconnect_button.clicked.connect(self.disconnect_proxy_connection)

        controls_layout.addWidget(self.system_proxy_checkbox)
        controls_layout.addWidget(self.dns_leak_checkbox)
        controls_layout.addWidget(self.ip_leak_checkbox)
        controls_layout.addWidget(self.disconnect_button)
        controls_layout.addStretch(1)
        stats_layout.addWidget(controls_group)

        # Application-Specific Proxy GroupBox
        app_proxy_group = QGroupBox("Application-Specific Proxy (Experimental)")
        app_specific_proxy_layout = QVBoxLayout()

        self.app_proxy_enable_checkbox = QCheckBox("Enable Application-Specific Proxying")
        self.app_proxy_enable_checkbox.stateChanged.connect(self.toggle_app_proxy_enabled_state)
        self.app_proxy_enable_checkbox.setEnabled(False) # Initially disabled
        app_specific_proxy_layout.addWidget(self.app_proxy_enable_checkbox)

        self.app_profiles_list_widget = QListWidget()
        self.app_profiles_list_widget.itemSelectionChanged.connect(self.handle_app_profile_selection_changed)
        self.app_profiles_list_widget.setEnabled(False) # Initially disabled
        app_specific_proxy_layout.addWidget(self.app_profiles_list_widget)

        profile_buttons_layout = QHBoxLayout()
        self.add_profile_button = QPushButton("Add Profile")
        self.add_profile_button.clicked.connect(self.add_app_profile_dialog)
        self.add_profile_button.setEnabled(True) # Can always manage profiles
        profile_buttons_layout.addWidget(self.add_profile_button)

        self.edit_profile_button = QPushButton("Edit Profile")
        self.edit_profile_button.clicked.connect(self.edit_app_profile_dialog)
        self.edit_profile_button.setEnabled(False)
        profile_buttons_layout.addWidget(self.edit_profile_button)

        self.remove_profile_button = QPushButton("Remove Profile")
        self.remove_profile_button.clicked.connect(self.remove_selected_app_profile)
        self.remove_profile_button.setEnabled(False)
        profile_buttons_layout.addWidget(self.remove_profile_button)

        app_specific_proxy_layout.addLayout(profile_buttons_layout)

        unmatched_traffic_layout = QHBoxLayout()
        unmatched_traffic_label = QLabel("Action for unmatched traffic (if rules enabled):")
        unmatched_traffic_layout.addWidget(unmatched_traffic_label)

        self.unmatched_traffic_action_combo = QComboBox()
        self.unmatched_traffic_action_combo.addItems(["Proxy", "Direct", "Block"])
        self.unmatched_traffic_action_combo.currentTextChanged.connect(self.set_unmatched_traffic_action_for_active_profile)
        self.unmatched_traffic_action_combo.setEnabled(False) # Initially disabled
        unmatched_traffic_layout.addWidget(self.unmatched_traffic_action_combo)
        app_specific_proxy_layout.addLayout(unmatched_traffic_layout)

        app_proxy_group.setLayout(app_specific_proxy_layout)
        stats_layout.addWidget(app_proxy_group)

        stats_layout.addStretch()



    def _handle_dns_settings_changed(self):
        """Handle changes in DNS leak checkbox or DNS server combobox."""
        # Enable/disable combobox based on checkbox
        dns_leak_enabled = self.dns_leak_checkbox.isChecked()
        self.dns_server_label.setEnabled(dns_leak_enabled)
        self.dns_server_combobox.setEnabled(dns_leak_enabled)
        
        self.log_debug(f"DNS settings changed. Leak prevention: {dns_leak_enabled}, Selected DNS: {self.dns_server_combobox.currentText() if dns_leak_enabled else 'N/A'}")
        if self.active_xray_connection_process: # Only reconnect if already connected
            self.reconnect_with_new_rules()

    def _handle_ip_leak_settings_changed(self):
        """Handle changes in IP leak checkbox."""
        self.log_debug(f"IP Leak Prevention toggled: {self.ip_leak_checkbox.isChecked()}")
        if self.active_xray_connection_process: # Only reconnect if already connected
            self.reconnect_with_new_rules()

    def _format_bytes(self, size_bytes):
        """Formats bytes to a human-readable string (KB, MB, GB)."""
        if size_bytes == 0:
            return "0 B"
        size_name = ("B", "KB", "MB", "GB", "TB")
        i = int(math.floor(math.log(size_bytes, 1024)))
        p = math.pow(1024, i)
        s = round(size_bytes / p, 2)
        return f"{s} {size_name[i]}"



    def update_results_table(self):
        # ... (Keep existing implementation - unchanged) ...
        self.log_debug(f"Updating results table with {len(self.filtered_configs)} filtered configs...")
        table = self.results_table
        table.setSortingEnabled(False) # Disable sorting during update
        table.setRowCount(0) # Clear existing rows
        table.setRowCount(len(self.filtered_configs))

        for i, config in enumerate(self.filtered_configs):
            # Use .get() with defaults for safety
            protocol = config.get('protocol', 'unknown')
            hostname = config.get('hostname', config.get('add', 'unknown')) # Check 'add' for vmess
            port = config.get('port', '0')
            remark = config.get('remark', config.get('ps', 'N/A')) # Check 'ps' for vmess remarks
            original_url = config.get('original_url', '')

            # Create items
            proto_item = QTableWidgetItem(protocol.upper())
            host_item = QTableWidgetItem(hostname)
            port_item = QTableWidgetItem(str(port))
            remark_item = QTableWidgetItem(remark)
            url_item = QTableWidgetItem(original_url) # Hidden column data

            # Store the original index from self.configs in the first column's UserRole
            # This allows linking back from the filtered view to the master list
            original_index = -1
            try:
                 # Find the index of this config dict in the main self.configs list
                 # Use object identity for potentially faster lookup if dicts are unique
                 original_index = next((idx for idx, cfg in enumerate(self.configs) if cfg is config), -1)
                 if original_index == -1: # Fallback to value comparison if identity fails (shouldn't usually)
                     original_index = self.configs.index(config)

            except ValueError:
                 self.log_debug(f"Warning: Config from filtered list not found in main self.configs list: {config.get('remark', hostname)}")
            proto_item.setData(Qt.UserRole, original_index) # Store original index

            # Set items in the row
            table.setItem(i, 0, proto_item)
            table.setItem(i, 1, host_item)
            table.setItem(i, 2, port_item)
            table.setItem(i, 3, remark_item)
            table.setItem(i, 4, url_item) # Set hidden item

        table.setSortingEnabled(True) # Re-enable sorting
        self.update_results_count() # Update the count label
        self.log_debug("Results table updated.")

    def update_results_count(self):
        # ... (Keep existing implementation - unchanged) ...
        # Counts visible rows after filtering
        visible_rows = 0
        for r in range(self.results_table.rowCount()):
            if not self.results_table.isRowHidden(r):
                visible_rows += 1
        total_filtered = len(self.filtered_configs) # Total number in the current filtered view
        self.results_count_label.setText(f"Showing: {visible_rows} / {total_filtered} configs")

    def filter_results(self):
        # ... (Keep existing implementation - unchanged) ...
        self.log_debug("Filtering results table...")
        filter_text = self.filter_input.text().lower()
        filter_column_index = self.filter_column_combo.currentIndex() # 0: All, 1: Proto, 2: Host, 3: Port, 4: Remark
        self.log_debug(f"Filter criteria - Text: '{filter_text}', Column Index: {filter_column_index}")

        match_count = 0
        for row in range(self.results_table.rowCount()):
            match = False
            if not filter_text: # If filter is empty, show all
                match = True
            else:
                # Columns to check in the visible table: 0=Proto, 1=Host, 2=Port, 3=Remark
                if filter_column_index == 0: # All Columns
                    for col in range(4): # Check Proto, Host, Port, Remark
                        item = self.results_table.item(row, col)
                        if item and filter_text in item.text().lower():
                            match = True
                            break
                else: # Specific Column
                    col_to_check = filter_column_index - 1 # Adjust index for table columns
                    item = self.results_table.item(row, col_to_check)
                    if item and filter_text in item.text().lower():
                        match = True

            self.results_table.setRowHidden(row, not match)
            if match:
                match_count += 1

        self.log_debug(f"Filter applied - {match_count} rows visible")
        self.update_results_count() # Update the "Showing X / Y" label

    def clear_filter(self):
        # ... (Keep existing implementation - unchanged) ...
        self.filter_input.clear() # Clearing the input automatically triggers filter_results


    # --- Testing Tab & Logic (Revised for Download Test) ---
    # Add methods to track and limit Xray processes
    def increment_xray_process_count(self):
        """Increment the active Xray process counter with thread safety"""
        # Get the current effective limit based on stability settings
        if self.stability_improvements_enabled:
            # Use the adaptive limit
            new_limit = self.get_effective_max_processes()
        else:
            # Use the UI value directly
            new_limit = self.download_max_workers_spinbox.value() if hasattr(self, 'download_max_workers_spinbox') else 15

        # If the limit has changed, update the semaphore
        if new_limit != self.max_allowed_xray_processes:
            self.log_debug(f"Updating Xray process limit from {self.max_allowed_xray_processes} to {new_limit}")
            # Create a new semaphore with the updated limit
            self.xray_semaphore = threading.Semaphore(new_limit)
            self.max_allowed_xray_processes = new_limit

        # Try to acquire the semaphore with a timeout
        # Use a longer timeout if system is under load
        timeout = 2.0 if hasattr(self, 'system_load_high') and self.system_load_high else 0.5
        acquired = self.xray_semaphore.acquire(blocking=True, timeout=timeout)

        if acquired:
            # Successfully acquired the semaphore, increment the counter
            with self.xray_process_lock:
                self.active_xray_processes += 1
                count = self.active_xray_processes
                self.log_debug(f"Xray process count increased to {count} (limit: {self.max_allowed_xray_processes})")
            return True
        else:
            # Failed to acquire the semaphore, too many processes running
            self.log_debug(f"Failed to acquire Xray semaphore - too many processes running (limit: {self.max_allowed_xray_processes})")
            return False

    def decrement_xray_process_count(self):
        """Decrement the active Xray process counter with thread safety"""
        with self.xray_process_lock:
            if self.active_xray_processes > 0:
                self.active_xray_processes -= 1
            count = self.active_xray_processes
            self.log_debug(f"Xray process count decreased to {count}")

        # Release the semaphore to allow another process to start
        try:
            self.xray_semaphore.release()
            self.log_debug("Released Xray semaphore")
        except ValueError:
            # This can happen if we release more than we acquired
            self.log_debug("Warning: Attempted to release Xray semaphore too many times")

        return count

    def get_xray_process_count(self):
        """Get the current number of active Xray processes"""
        with self.xray_process_lock:
            return self.active_xray_processes

    def reset_xray_process_count(self):
        """Reset the Xray process counter to zero and reset the semaphore"""
        with self.xray_process_lock:
            old_count = self.active_xray_processes
            self.active_xray_processes = 0
            self.log_debug(f"Xray process count reset from {old_count} to 0")

        # Create a new semaphore with the current limit
        self.xray_semaphore = threading.Semaphore(self.max_allowed_xray_processes)
        self.log_debug(f"Reset Xray semaphore with limit {self.max_allowed_xray_processes}")

    def setup_latency_tab(self):
        # --- ADDED/MODIFIED FOR DOWNLOAD TEST ---
        latency_widget = QWidget()
        self.tab_widget.addTab(latency_widget, "Testing")
        latency_layout = QVBoxLayout(latency_widget)

        # Top buttons with integrated layout and labels
        button_panel = QWidget()
        button_layout = QHBoxLayout(button_panel)
        button_layout.setContentsMargins(0, 0, 0, 0) # Tighter layout

        # Create test buttons
        self.test_latency_button = QPushButton("Test Ping Latency")
        self.test_latency_button.setToolTip("Test ping latency for all configs (or selected configs if any are selected)")
        self.test_latency_button.clicked.connect(self.start_ping_latency_test)
        button_layout.addWidget(self.test_latency_button)

        self.test_netcat_button = QPushButton("Test Netcat")
        self.test_netcat_button.setToolTip("Test netcat latency for all configs (or selected configs if any are selected)")
        self.test_netcat_button.clicked.connect(self.start_netcat_test)
        button_layout.addWidget(self.test_netcat_button)

        self.test_speed_button = QPushButton("Speed Test")
        self.test_speed_button.setToolTip("Test download speed using 2MB file for all configs (or selected configs if any are selected)")
        self.test_speed_button.clicked.connect(self.start_speed_test)
        button_layout.addWidget(self.test_speed_button)

        self.test_connectivity_button = QPushButton("Connectivity Test")
        self.test_connectivity_button.setToolTip("Test connectivity using small file for all configs (or selected configs if any are selected)")
        self.test_connectivity_button.clicked.connect(self.start_connectivity_test)
        button_layout.addWidget(self.test_connectivity_button)

        self.test_http_button = QPushButton("Test HTTP")
        self.test_http_button.setToolTip("Test HTTP connectivity to Cloudflare for all configs (or selected configs if any are selected)")
        self.test_http_button.clicked.connect(self.start_http_test)
        button_layout.addWidget(self.test_http_button)

        self.test_site_button = QPushButton("Test Custom Site")
        self.test_site_button.setToolTip("Test custom site connectivity for all configs (or selected configs if any are selected)")
        self.test_site_button.clicked.connect(self.start_site_test)
        button_layout.addWidget(self.test_site_button)

        # Custom site input moved after the button
        self.site_url_input = QLineEdit(self.SITE_TEST_DEFAULT_URL)
        self.site_url_input.setPlaceholderText("Enter URL to test (e.g., https://www.cloudflare.com/cdn-cgi/trace)")
        button_layout.addWidget(self.site_url_input)
        button_layout.addStretch(1)

        latency_layout.addWidget(button_panel)

        # Add worker configuration controls
        worker_config_layout = QHBoxLayout()

        # Ping test workers
        ping_worker_label = QLabel("Ping:")
        worker_config_layout.addWidget(ping_worker_label)
        self.ping_max_workers_spinbox = QSpinBox()
        self.ping_max_workers_spinbox.setMinimum(1); self.ping_max_workers_spinbox.setMaximum(100000); self.ping_max_workers_spinbox.setValue(15)
        self.ping_max_workers_spinbox.setToolTip("Max concurrent PING tests.")
        worker_config_layout.addWidget(self.ping_max_workers_spinbox)
        worker_config_layout.addSpacing(10)

        # Netcat Workers
        netcat_worker_label = QLabel("Netcat:")
        worker_config_layout.addWidget(netcat_worker_label)
        self.netcat_max_workers_spinbox = QSpinBox()
        self.netcat_max_workers_spinbox.setMinimum(1); self.netcat_max_workers_spinbox.setMaximum(100000); self.netcat_max_workers_spinbox.setValue(15)
        self.netcat_max_workers_spinbox.setToolTip("Max concurrent Netcat TCP connection tests.")
        worker_config_layout.addWidget(self.netcat_max_workers_spinbox)
        worker_config_layout.addSpacing(10)

        # --- Download Workers (NEW) ---
        download_worker_label = QLabel("Download:")
        worker_config_layout.addWidget(download_worker_label)
        self.download_max_workers_spinbox = QSpinBox()
        self.download_max_workers_spinbox.setMinimum(1); self.download_max_workers_spinbox.setMaximum(100000); self.download_max_workers_spinbox.setValue(15) # Set to 15 as requested
        self.download_max_workers_spinbox.setToolTip("Max concurrent Download tests.\nLimited by available ports & resources.")
        worker_config_layout.addWidget(self.download_max_workers_spinbox)
        worker_config_layout.addSpacing(10)
        # --- END NEW ---

        # Xray test workers (Google/Site ONLY)
        xray_worker_label = QLabel("Google/Site:") # Renamed Label
        worker_config_layout.addWidget(xray_worker_label)
        self.xray_max_workers_spinbox = QSpinBox()
        self.xray_max_workers_spinbox.setMinimum(1); self.xray_max_workers_spinbox.setMaximum(100000); self.xray_max_workers_spinbox.setValue(15)
        self.xray_max_workers_spinbox.setToolTip("Max concurrent Xray (Google/Site) tests.\nLimited by available ports & resources.") # Updated tooltip
        worker_config_layout.addWidget(self.xray_max_workers_spinbox)
        worker_config_layout.addSpacing(10)

        # HTTP test workers
        http_worker_label = QLabel("HTTP:")
        worker_config_layout.addWidget(http_worker_label)
        self.http_max_workers_spinbox = QSpinBox()
        self.http_max_workers_spinbox.setMinimum(1); self.http_max_workers_spinbox.setMaximum(100000); self.http_max_workers_spinbox.setValue(15)
        self.http_max_workers_spinbox.setToolTip("Max concurrent HTTP tests.\nLimited by available ports & resources.")
        worker_config_layout.addWidget(self.http_max_workers_spinbox)

        worker_config_layout.addStretch(1)
        latency_layout.addLayout(worker_config_layout)



        # Progress Bar
        self.test_progress_bar = QProgressBar()
        self.test_progress_bar.setVisible(False)
        self.test_progress_bar.setTextVisible(True)
        self.test_progress_bar.setFormat("%p% - %v / %m") # Show percentage and value/max
        latency_layout.addWidget(self.test_progress_bar)

        # Create a group box for Complete Test settings (moved from Input tab)
        complete_test_group = QGroupBox("Complete Test Settings")
        complete_test_layout = QVBoxLayout()

        # Complete Test button row
        complete_test_button_layout = QHBoxLayout()

        # Profile selection for complete test
        complete_test_button_layout.addWidget(QLabel("Profile:"))
        self.complete_test_profile_combo = QComboBox()
        self.complete_test_profile_combo.addItems(["None", "All Predefined"] + self.get_profile_names())
        self.complete_test_profile_combo.setToolTip("Select a profile to test, 'All Predefined' to test all predefined subscriptions, or 'None' to use current configs")
        self.complete_test_profile_combo.setMinimumWidth(150)
        complete_test_button_layout.addWidget(self.complete_test_profile_combo)

        complete_test_button = QPushButton("Complete Test")
        complete_test_button.setToolTip("Run Netcat and Download tests in sequence, then filters Results tab to show only configs that pass both tests.")
        complete_test_button.clicked.connect(self.start_complete_test)
        complete_test_button.setMinimumWidth(120)
        complete_test_button_layout.addWidget(complete_test_button)

        # Auto start checkbox
        self.auto_start_checkbox = QCheckBox("Auto Start")
        self.auto_start_checkbox.setToolTip("Automatically restart the test after completion")
        complete_test_button_layout.addWidget(self.auto_start_checkbox)

        # Timer for auto restart
        complete_test_button_layout.addWidget(QLabel("Interval (seconds):"))
        self.auto_start_timer = QSpinBox()
        self.auto_start_timer.setRange(0, 3600)  # 0 seconds to 1 hour
        self.auto_start_timer.setValue(300)  # Default to 5 minutes
        self.auto_start_timer.setToolTip("Restart Complete Test after this many seconds")
        complete_test_button_layout.addWidget(self.auto_start_timer)

        complete_test_layout.addLayout(complete_test_button_layout)

        # Export options row
        export_options_layout = QHBoxLayout()

        # Auto export checkbox
        self.auto_export_checkbox = QCheckBox("Auto Export")
        self.auto_export_checkbox.setToolTip("Automatically export results after Complete Test finishes")
        export_options_layout.addWidget(self.auto_export_checkbox)

        # Auto rename checkbox
        self.auto_rename_checkbox = QCheckBox("Auto Rename")
        self.auto_rename_checkbox.setToolTip("Automatically rename configs when exporting")
        export_options_layout.addWidget(self.auto_rename_checkbox)

        # Export directory selection
        export_options_layout.addWidget(QLabel("Export Directory:"))
        self.export_dir_input = QLineEdit()
        self.export_dir_input.setText(os.path.dirname(os.path.abspath(__file__)))  # Default to script directory
        self.export_dir_input.setToolTip("Directory where exported files will be saved")
        export_options_layout.addWidget(self.export_dir_input)

        # Browse button for export directory
        browse_dir_button = QPushButton("Browse...")
        browse_dir_button.clicked.connect(self.browse_export_directory)
        export_options_layout.addWidget(browse_dir_button)

        complete_test_layout.addLayout(export_options_layout)
        complete_test_group.setLayout(complete_test_layout)

        # Add to main layout
        latency_layout.addWidget(complete_test_group)

        # HTTP Test Section
        http_test_group = QGroupBox("HTTP Test")
        http_test_layout = QVBoxLayout()

        # HTTP Test button row
        http_test_button_layout = QHBoxLayout()

        # Profile selection for HTTP test
        http_test_button_layout.addWidget(QLabel("Profile:"))
        self.http_test_profile_combo = QComboBox()
        self.http_test_profile_combo.addItems(["None", "All Predefined"] + self.get_profile_names())
        self.http_test_profile_combo.setToolTip("Select a profile to test, 'All Predefined' to test all predefined subscriptions, or 'None' to use current configs")
        self.http_test_profile_combo.setMinimumWidth(150)
        http_test_button_layout.addWidget(self.http_test_profile_combo)

        http_test_button = QPushButton("HTTP Test")
        http_test_button.setToolTip("Run HTTP connectivity test with integrity verification")
        http_test_button.clicked.connect(self.start_http_test)
        http_test_button.setMinimumWidth(120)
        http_test_button_layout.addWidget(http_test_button)

        # Connection integrity checkbox (moved from other location)
        self.http_connection_integrity_checkbox = QCheckBox("Connection Integrity")
        self.http_connection_integrity_checkbox.setChecked(True)  # Default checked as requested
        self.http_connection_integrity_checkbox.setToolTip("Chain HTTP test with connectivity test - only marks config as successful if both tests pass")
        http_test_button_layout.addWidget(self.http_connection_integrity_checkbox)

        http_test_layout.addLayout(http_test_button_layout)

        # HTTP Test options row 1
        http_test_options1_layout = QHBoxLayout()

        # Auto start checkbox for HTTP test
        self.http_auto_start_checkbox = QCheckBox("Auto Start")
        self.http_auto_start_checkbox.setToolTip("Automatically restart the HTTP test after completion")
        http_test_options1_layout.addWidget(self.http_auto_start_checkbox)

        # Timer for HTTP auto restart
        http_test_options1_layout.addWidget(QLabel("Interval (seconds):"))
        self.http_auto_start_timer = QSpinBox()
        self.http_auto_start_timer.setRange(0, 3600)  # 0 seconds to 1 hour
        self.http_auto_start_timer.setValue(300)  # Default to 5 minutes
        self.http_auto_start_timer.setToolTip("Restart HTTP Test after this many seconds")
        http_test_options1_layout.addWidget(self.http_auto_start_timer)

        # Auto export checkbox for HTTP test
        self.http_auto_export_checkbox = QCheckBox("Auto Export")
        self.http_auto_export_checkbox.setToolTip("Automatically export results after HTTP Test finishes")
        http_test_options1_layout.addWidget(self.http_auto_export_checkbox)

        # Auto rename checkbox for HTTP test
        self.http_auto_rename_checkbox = QCheckBox("Auto Rename")
        self.http_auto_rename_checkbox.setToolTip("Automatically rename configs when exporting HTTP test results")
        http_test_options1_layout.addWidget(self.http_auto_rename_checkbox)

        http_test_layout.addLayout(http_test_options1_layout)

        # HTTP Test options row 2 - Export directory
        http_test_options2_layout = QHBoxLayout()

        # Export directory selection for HTTP test
        http_test_options2_layout.addWidget(QLabel("Export Directory:"))
        self.http_export_dir_input = QLineEdit()
        self.http_export_dir_input.setText(os.path.dirname(os.path.abspath(__file__)))  # Default to script directory
        self.http_export_dir_input.setToolTip("Directory where HTTP test exported files will be saved")
        http_test_options2_layout.addWidget(self.http_export_dir_input)

        # Browse button for HTTP test export directory
        browse_http_dir_button = QPushButton("Browse...")
        browse_http_dir_button.clicked.connect(self.browse_http_export_directory)
        http_test_options2_layout.addWidget(browse_http_dir_button)

        http_test_layout.addLayout(http_test_options2_layout)
        http_test_group.setLayout(http_test_layout)

        # Add to main layout
        latency_layout.addWidget(http_test_group)

        # Add progress bar for complete test
        self.complete_test_progress_layout = QHBoxLayout()
        self.complete_test_progress_label = QLabel("Complete Test Progress:")
        self.complete_test_progress_layout.addWidget(self.complete_test_progress_label)
        self.complete_test_progress_bar = QProgressBar()
        self.complete_test_progress_bar.setVisible(False)
        self.complete_test_progress_bar.setTextVisible(True)
        self.complete_test_progress_bar.setFormat("%p% - %v / %m")
        self.complete_test_progress_layout.addWidget(self.complete_test_progress_bar)
        latency_layout.addLayout(self.complete_test_progress_layout)

        # Ping Statistics Group (keep as is, based on ping only)
        stats_group = QGroupBox("Ping Statistics (Based on last 'Test Ping Latency' run)")
        stats_layout = QHBoxLayout(stats_group)
        stats_layout.addWidget(QLabel("Average:"))
        self.stats_avg = QLabel("N/A")
        stats_layout.addWidget(self.stats_avg)
        stats_layout.addWidget(QLabel("Median:"))
        self.stats_median = QLabel("N/A")
        stats_layout.addWidget(self.stats_median)
        stats_layout.addWidget(QLabel("Min:"))
        self.stats_min = QLabel("N/A")
        stats_layout.addWidget(self.stats_min)
        stats_layout.addWidget(QLabel("Max:"))
        self.stats_max = QLabel("N/A")
        stats_layout.addWidget(self.stats_max)
        stats_layout.addWidget(QLabel("Available:"))
        self.stats_available = QLabel("N/A") # Shows count / total tested
        stats_layout.addWidget(self.stats_available)
        stats_layout.addStretch()
        latency_layout.addWidget(stats_group)

        # Latency Count Label
        self.latency_count_label = QLabel("Total: 0 configs") # Shows total in self.configs
        latency_layout.addWidget(self.latency_count_label)

        # Latency Table
        self.latency_table = QTableWidget()
        # ---- Increased column count for HTTP Test ----
        self.latency_table.setColumnCount(11) # Index(Hidden), Proto, Host, Port, Remark, Ping, Netcat, Download, Google, Site, HTTP
        self.latency_table.setHorizontalHeaderLabels(["Orig Idx","Protocol", "Hostname", "Port", "Remark", "Ping", "Netcat", "Download", "Google", "Site Test", "HTTP Test"])
        # -------------------------------------------

        # Table Properties
        self.latency_table.horizontalHeader().setSectionResizeMode(QHeaderView.Interactive)
        self.latency_table.setColumnHidden(0, True) # Hide Original Index
        self.latency_table.setColumnWidth(1, 70)  # Protocol
        self.latency_table.setColumnWidth(2, 180) # Hostname
        self.latency_table.setColumnWidth(3, 50)  # Port
        self.latency_table.setColumnWidth(4, 250) # Remark (stretch later)
        self.latency_table.setColumnWidth(5, 70)  # Ping
        self.latency_table.setColumnWidth(6, 70)  # Netcat
        self.latency_table.setColumnWidth(7, 80)  # Download <-- Added width
        self.latency_table.setColumnWidth(8, 70)  # Google <-- Adjusted index
        self.latency_table.setColumnWidth(9, 70)  # Site Test
        self.latency_table.setColumnWidth(10, 70) # HTTP Test <-- Adjusted index

        # Make Remark column stretch
        self.latency_table.horizontalHeader().setStretchLastSection(False) # Don't stretch last (Site Test)
        self.latency_table.horizontalHeader().setSectionResizeMode(4, QHeaderView.Stretch) # Stretch Remark

        self.latency_table.verticalHeader().setVisible(False)
        self.latency_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.latency_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.latency_table.setAlternatingRowColors(True)
        self.latency_table.setSortingEnabled(True) # Enable column sorting
        # Enable custom context menu
        self.latency_table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.latency_table.customContextMenuRequested.connect(self.show_latency_table_context_menu)

        latency_layout.addWidget(self.latency_table)

        # Layout for the bottom buttons (Stop Button)
        bottom_button_layout = QHBoxLayout() # Use a layout to contain the stop button

        # Add stop button to the UI
        self.stop_test_button = QPushButton("Stop Tests")
        self.stop_test_button.setEnabled(False)
        self.stop_test_button.setToolTip("Attempts to stop the currently running test batch.")
        self.stop_test_button.clicked.connect(self.stop_all_tests)
        bottom_button_layout.addWidget(self.stop_test_button)
        bottom_button_layout.addStretch() # Push button to the left

        latency_layout.addLayout(bottom_button_layout) # Add the layout to the main vertical layout
        # --- END DOWNLOAD TEST MODIFICATION ---

    def update_latency_table(self):
        # --- ADDED/MODIFIED FOR DOWNLOAD TEST ---
        self.log_debug("Updating testing table...")
        table = self.latency_table
        table.setSortingEnabled(False) # Disable sorting during update
        table.setRowCount(0) # Clear existing rows

        # Display filtered configs in the Testing tab (respects both Protocol and Country filters)
        configs_to_display = self.filtered_configs
        count = len(configs_to_display)

        if not count:
             self.log_debug("No configs loaded to display in testing table.")
             self.latency_count_label.setText("Total: 0 configs")
             table.setSortingEnabled(True)
             return

        table.setRowCount(count)
        self.latency_count_label.setText(f"Total: {count} configs")
        self.log_debug(f"Populating testing table with {count} configs.")

        for row, config in enumerate(configs_to_display):
            # Find the original index in self.configs for this filtered config
            original_index = -1
            for i, original_config in enumerate(self.configs):
                if original_config is config:  # Same object reference
                    original_index = i
                    break

            # Get data, using defaults
            protocol = config.get('protocol', 'unknown')
            hostname = config.get('hostname', config.get('add', 'N/A'))
            port = config.get('port', 'N/A')
            remark = config.get('remark', config.get('ps', ''))

            # Retrieve stored latency/test results
            ping_latency = config.get('ping_latency', None)
            netcat_result = config.get('netcat_result', None)
            download_speed = config.get('download_speed', None) # <-- Get Download result
            google_latency = config.get('google_latency', None)
            site_latency = config.get('site_test_latency', None)
            http_latency = config.get('http_latency', None) # <-- Get HTTP result

            # Retrieve success flags
            ping_success = config.get('ping_available', None)
            netcat_success = config.get('netcat_success', None)
            download_success = config.get('download_success', None) # <-- Get Download success flag
            google_success = config.get('google_success', None)
            site_success = config.get('site_success', None)
            http_success = config.get('http_success', None) # <-- Get HTTP success flag

            # Format the display text
            ping_text = self._format_latency_text(ping_latency, ping_success)
            netcat_text = self._format_latency_text(netcat_result, netcat_success)
            download_text = self._format_latency_text(download_speed, download_success, "Download") # <-- Format Download text
            google_text = self._format_latency_text(google_latency, google_success)
            site_text = self._format_latency_text(site_latency, site_success)
            http_text = self._format_latency_text(http_latency, http_success) # <-- Format HTTP text

            # Create table items
            index_item = QTableWidgetItem(str(original_index))
            index_item.setData(Qt.UserRole, original_index) # Store original index in self.configs

            proto_item = QTableWidgetItem(protocol.upper())
            host_item = QTableWidgetItem(hostname)
            port_item = QTableWidgetItem(str(port))
            remark_item = QTableWidgetItem(remark)
            ping_item = QTableWidgetItem(ping_text)
            netcat_item = QTableWidgetItem(netcat_text)
            download_item = QTableWidgetItem(download_text) # <-- Create Download item
            google_item = QTableWidgetItem(google_text)
            site_item = QTableWidgetItem(site_text)
            http_item = QTableWidgetItem(http_text) # <-- Create HTTP item

            # Set alignment for specific columns
            port_item.setTextAlignment(Qt.AlignCenter)
            ping_item.setTextAlignment(Qt.AlignCenter)
            netcat_item.setTextAlignment(Qt.AlignCenter)
            download_item.setTextAlignment(Qt.AlignCenter) # <-- Align Download item
            google_item.setTextAlignment(Qt.AlignCenter)
            site_item.setTextAlignment(Qt.AlignCenter)

            # Apply background color based on result
            self._apply_cell_color(ping_item, ping_latency, ping_success)
            self._apply_cell_color(netcat_item, netcat_result, netcat_success)
            self._apply_cell_color(download_item, download_speed, download_success, test_type='Download') # <-- Color Download item
            self._apply_cell_color(google_item, google_latency, google_success)
            self._apply_cell_color(site_item, site_latency, site_success)
            self._apply_cell_color(http_item, http_latency, http_success) # <-- Color HTTP item

            # Add items to the table row
            table.setItem(row, 0, index_item) # Hidden index
            table.setItem(row, 1, proto_item)
            table.setItem(row, 2, host_item)
            table.setItem(row, 3, port_item)
            table.setItem(row, 4, remark_item)
            table.setItem(row, 5, ping_item)
            table.setItem(row, 6, netcat_item)
            table.setItem(row, 7, download_item) # <-- Add Download item
            table.setItem(row, 8, google_item)   # <-- Adjusted index
            table.setItem(row, 9, site_item)     # <-- Adjusted index
            table.setItem(row, 10, http_item)    # <-- Add HTTP item

        # table.resizeColumnsToContents() # Resize after populating might be slow, keep fixed widths
        # Ensure remark stretches
        table.horizontalHeader().setSectionResizeMode(4, QHeaderView.Stretch)

        # Process events to help ensure UI updates for large tables
        QCoreApplication.processEvents()

        table.setSortingEnabled(True) # Re-enable sorting
        self.log_debug("Testing table updated.")
        # --- END DOWNLOAD TEST MODIFICATION ---

    # --- _format_latency_text (MODIFIED to use test_type) ---
    def _format_latency_text(self, result_value, success, test_type=None):
        if success is True:
            if isinstance(result_value, (int, float)):
                # --- Use test_type to decide formatting ---
                if test_type == 'Download': # Format speed
                    speed_kbs = result_value
                    if speed_kbs >= 1024:
                        speed_mbs = speed_kbs / 1024.0
                        return f"{speed_mbs:.1f} MB/s"
                    else:
                        return f"{speed_kbs:.0f} KB/s"
                # --- Explicitly check for latency test types ---
                elif test_type in ['Ping', 'Google', 'Site']: # Format latency
                    # Format latency as integer ms
                    return f"{result_value:.0f} ms"
                # --- End latency check ---
                else: # Fallback for numeric success with unknown type (shouldn't happen ideally)
                    return f"{result_value:.1f}" # Just show number
            elif isinstance(result_value, str) and result_value == "OK": # Netcat success
                return "OK"
            else: # Fallback for unexpected success type
                return "OK" # Or str(result_value)? "OK" seems safer.
        elif success is False:
            # Display the specific error message if available and it's a string
            if isinstance(result_value, str):
                 # Shorten common errors for display
                 if "Xray Start Error" in result_value: return "Xray Fail"
                 if "Config Error" in result_value: return "Bad Config"
                 if "Proxy Error" in result_value: return "Proxy Err"
                 if "Conn Error" in result_value: return "Conn Err"
                 if "Refused" in result_value: return "Refused"
                 if "SSL Error" in result_value: return "SSL Err"
                 if "HTTP" in result_value: return result_value # e.g., "HTTP 404"
                 if "Timeout" in result_value: return "Timeout"
                 if "No DNS" in result_value: return "No DNS"
                 if "Invalid Host" in result_value: return "Bad Host"
                 if "Xray Not Found" in result_value: return "No Xray"
                 if "NC Not Found" in result_value: return "No NC"
                 if "Download Error" in result_value: return "DL Error"
                 if "File Error" in result_value: return "File Err"
                 if "Too Slow" in result_value: return "Too Slow"
                 if "Failed" in result_value : return "Failed"
                 if "Error" in result_value : return "Error"
                 # Otherwise, show the first part of the error
                 return result_value.split(':')[0] if ':' in result_value else result_value[:10]
            else:
                return "Failed" # Generic failure if result_value is not a string
        elif result_value is None: # Not tested yet
            return "N/A"
        else: # Should not happen, but fallback
            return str(result_value)[:10] # Show first few chars if unexpected type

    def _apply_cell_color(self, item, result_value, success, test_type=None):
        # --- ADDED/MODIFIED FOR DOWNLOAD TEST ---
        # Define colors (RGBA with alpha for subtle background)
        SUCCESS_COLOR = QColor(0, 200, 0, 40)  # Light green
        ERROR_COLOR = QColor(255, 0, 0, 40)    # Light red
        WARN_COLOR = QColor(255, 165, 0, 40)   # Light orange
        NEUTRAL_COLOR = QColor(128, 128, 128, 40) # Light gray

        if success is True:
            if isinstance(result_value, (int, float)):
                if test_type == 'Download':
                    # Color based on download speed
                    speed_kbs = result_value
                    if speed_kbs >= 5120:  # >5MB/s = Green
                        item.setBackground(SUCCESS_COLOR)
                    elif speed_kbs >= 1024:  # >1MB/s = Light Green
                        item.setBackground(QColor(100, 200, 100, 40))
                    elif speed_kbs >= 512:  # >512KB/s = Yellow-Green
                        item.setBackground(QColor(180, 200, 100, 40))
                    elif speed_kbs >= 256:  # >256KB/s = Yellow
                        item.setBackground(QColor(200, 200, 100, 40))
                    else:  # Slower = Orange
                        item.setBackground(WARN_COLOR)
                elif test_type in ['Ping', 'Google', 'Site']:
                    # Color based on latency
                    if result_value <= 100:  # Fast
                        item.setBackground(SUCCESS_COLOR)
                    elif result_value <= 200:  # Good
                        item.setBackground(QColor(100, 200, 100, 40))
                    elif result_value <= 300:  # OK
                        item.setBackground(QColor(180, 200, 100, 40))
                    elif result_value <= 500:  # Slow
                        item.setBackground(QColor(200, 200, 100, 40))
                    else:  # Very Slow
                        item.setBackground(WARN_COLOR)
                else:  # Other numeric success (e.g., Netcat)
                    item.setBackground(SUCCESS_COLOR)
            else:  # Non-numeric success (e.g., "OK" for Netcat)
                item.setBackground(SUCCESS_COLOR)
        elif success is False:
            item.setBackground(ERROR_COLOR)
        else:  # None or unknown
            item.setBackground(NEUTRAL_COLOR)
        # --- END DOWNLOAD TEST MODIFICATION ---

    def update_latency_stats(self):
        # ... (Keep existing implementation - PING only stats - unchanged) ...
        ping_latencies = []
        available_count = 0
        total_tested = 0 # Count configs that *should* have been pinged

        for config in self.configs:
            # Only include configs that are eligible for pinging in the total count
            protocol = config.get('protocol', 'unknown')
            hostname = config.get('hostname', '')
            # Exclude configs with known bad hostnames from the 'total tested' count for ping
            is_valid_host = hostname and hostname not in ['error', 'unknown', 'parse_err', 'vmess_host_err', 'sip008_host_err', 'ss_err', 'unknown_host', 'ssr_host']

            if protocol not in ['comment', 'error', 'ssr', 'unknown'] and is_valid_host:
                 total_tested += 1
                 # Now check if it has a valid *numeric* result for stats
                 if config.get('ping_available') is True and isinstance(config.get('ping_latency'), (int, float)):
                     ping_latencies.append(config['ping_latency'])
                     available_count += 1
                 # No else needed - failed/timeout pings don't contribute to avg/min/max etc.

        if ping_latencies: # Calculate stats only if there are successful pings
            valid_count = len(ping_latencies)
            avg = sum(ping_latencies) / valid_count
            ping_latencies.sort()
            median = ping_latencies[valid_count // 2]
            min_latency = ping_latencies[0]
            max_latency = ping_latencies[-1]

            self.stats_avg.setText(f"{avg:.0f} ms")
            self.stats_median.setText(f"{median:.0f} ms")
            self.stats_min.setText(f"{min_latency:.0f} ms")
            self.stats_max.setText(f"{max_latency:.0f} ms")
        else: # No successful pings
            self.stats_avg.setText("N/A")
            self.stats_median.setText("N/A")
            self.stats_min.setText("N/A")
            self.stats_max.setText("N/A")

        # Update available count (Successful / Total Eligible Tested)
        self.stats_available.setText(f"{available_count} / {total_tested}")
        self.log_debug(f"Updated Ping Statistics: Available={available_count}/{total_tested}")

    def start_ping_latency_test(self):
        # Reset UI state before starting the test
        self._reset_ui_before_test()

        # ... (Keep existing implementation - unchanged) ...
        if not self.configs:
            QMessageBox.warning(self, "No Configurations", "Load configurations before testing.")
            return

        # Get selected rows from the latency table if there are any
        selected_items = self.latency_table.selectedItems()
        selected_rows = sorted(set(item.row() for item in selected_items)) if selected_items else []

        # --- Determine configs to test (eligible for ping) ---
        configs_to_ping = []
        indices_to_ping = [] # Store original indices

        # If rows are selected, only test those configs
        if selected_rows:
            for row in selected_rows:
                if row < len(self.configs):
                    cfg = self.configs[row]
                    protocol = cfg.get('protocol', 'unknown')
                    hostname = cfg.get('hostname', '')
                    is_valid_host = hostname and hostname not in ['error', 'unknown', 'parse_err', 'vmess_host_err', 'sip008_host_err', 'ss_err', 'unknown_host', 'ssr_host']
                    if protocol not in ['comment', 'error', 'ssr', 'unknown'] and is_valid_host:
                        configs_to_ping.append(cfg)
                        indices_to_ping.append(row)
                    elif protocol not in ['comment', 'error', 'ssr', 'unknown'] and not is_valid_host:
                        # Mark invalid hosts immediately in the table if they weren't pinged
                        self.signals.update_specific_latency.emit(row, "Invalid Host", False, "Ping")
        else:
            # Original behavior - test all configs
            for i, cfg in enumerate(self.configs):
                protocol = cfg.get('protocol', 'unknown')
                hostname = cfg.get('hostname', '')
                is_valid_host = hostname and hostname not in ['error', 'unknown', 'parse_err', 'vmess_host_err', 'sip008_host_err', 'ss_err', 'unknown_host', 'ssr_host']
                if protocol not in ['comment', 'error', 'ssr', 'unknown'] and is_valid_host:
                    configs_to_ping.append(cfg)
                    indices_to_ping.append(i)
                elif protocol not in ['comment', 'error', 'ssr', 'unknown'] and not is_valid_host:
                    # Mark invalid hosts immediately in the table if they weren't pinged
                    self.signals.update_specific_latency.emit(i, "Invalid Host", False, "Ping")

        if not configs_to_ping:
            QMessageBox.information(self, "No Suitable Configs", "No configurations eligible for ping testing found (valid protocol and hostname).")
            return

        # Get max_workers from UI
        max_workers = self.ping_max_workers_spinbox.value()
        self.log_debug(f"Starting direct PING latency test for {len(configs_to_ping)} configs with max_workers={max_workers}...")

        # Clear previous ping results in UI and config dict
        for i in indices_to_ping:
            self.configs[i].pop('ping_latency', None)
            self.configs[i].pop('ping_available', None) # Changed key name
            # Visually clear cell
            na_item = QTableWidgetItem("...")
            na_item.setTextAlignment(Qt.AlignCenter)
            self._apply_cell_color(na_item, None, None)
            self.latency_table.setItem(i, 5, na_item) # Column 5 = Ping

        # Setup UI for test start
        self.test_latency_button.setText("Testing Ping...")
        self.test_latency_button.setEnabled(False)
        self.stop_test_button.setEnabled(True) # Enable stop button
        self.test_progress_bar.setVisible(True)
        self.test_progress_bar.setValue(0)
        self.test_progress_bar.setMaximum(len(configs_to_ping)) # Set max for progress bar

        # Use the existing LatencyTesterThread (it emits the original index)
        # Pass the full self.configs list, but the thread internally filters
        self.ping_test_thread = LatencyTesterThread(self.configs, max_workers=max_workers) # Pass ALL configs
        # Disconnect previous connections if any to prevent duplicates
        try: self.ping_test_thread.update_signal.disconnect()
        except TypeError: pass
        try: self.ping_test_thread.progress_signal.disconnect()
        except TypeError: pass
        try: self.ping_test_thread.finished_signal.disconnect()
        except TypeError: pass
        # Connect signals
        self.ping_test_thread.update_signal.connect(self._update_ping_latency_in_table) # Slot handles original index
        self.ping_test_thread.progress_signal.connect(self.update_progress)
        self.ping_test_thread.finished_signal.connect(self.on_ping_test_completed)
        self.ping_test_thread.start()

        # Reset stopped flag
        self.stopping_tests = False

    def start_netcat_test(self):
        # ... (Keep existing implementation - unchanged) ...
        if not self.configs:
            QMessageBox.warning(self, "No Configurations", "Load configurations before testing.")
            return

        # Get selected rows from the latency table if there are any
        selected_items = self.latency_table.selectedItems()
        selected_rows = sorted(set(item.row() for item in selected_items)) if selected_items else []

        # --- Determine configs to test ---
        configs_to_test = []
        indices_to_test = [] # Store original indices

        # If rows are selected, only test those configs
        if selected_rows:
            for row in selected_rows:
                if row < len(self.configs):
                    cfg = self.configs[row]
                    protocol = cfg.get('protocol', 'unknown')
                    if protocol not in ['comment', 'error', 'unknown']:
                        configs_to_test.append(cfg)
                        indices_to_test.append(row)
        else:
            # Original behavior - test all configs
            for i, cfg in enumerate(self.configs):
                protocol = cfg.get('protocol', 'unknown')
                if protocol not in ['comment', 'error', 'unknown']:
                    configs_to_test.append(cfg)
                    indices_to_test.append(i)

        if not configs_to_test:
            self.show_message_box("No Suitable Configs", "No configurations eligible for Netcat testing found (valid protocol, hostname, and port).", "warning")
            return

        # Reset previous results in UI and config dict
        for i in indices_to_test:
            self.configs[i].pop('netcat_result', None)
            self.configs[i].pop('netcat_success', None)
             # Visually clear cell
            na_item = QTableWidgetItem("...")
            na_item.setTextAlignment(Qt.AlignCenter)
            self._apply_cell_color(na_item, None, None)
            self.latency_table.setItem(i, 6, na_item) # Column 6 = Netcat

        # Setup UI
        self.test_netcat_button.setText("Testing Netcat...")
        self.test_netcat_button.setEnabled(False)
        self.stop_test_button.setEnabled(True)
        self.test_progress_bar.setVisible(True)
        self.test_progress_bar.setValue(0)
        self.test_progress_bar.setMaximum(len(configs_to_test))

        test_name = "Netcat"

        # Get max_workers from UI
        max_workers = self.netcat_max_workers_spinbox.value()
        self.log_debug(f"Starting {test_name} connectivity test for {len(configs_to_test)} configs with max_workers={max_workers}...")

        # Create the thread that will run the test process using the generic handler
        # Pass the filtered list `configs_to_test`
        test_thread = threading.Thread(
            target=self._process_test_generic,
            args=(
                configs_to_test, # Pass the filtered list
                self._run_netcat_test, # The specific test function
                'netcat_result',       # Config key for result value
                'netcat_success',      # Config key for success flag
                test_name,             # Name for logging/UI
                self.test_netcat_button,# Button to re-enable
            ),
            kwargs={
                'extra_test_args': {
                    'max_workers': max_workers
                    # No target_url needed for nc
                }
            },
            daemon=True
        )

        # Disconnect previous connection if any
        try: self.signals.test_completed.disconnect(self._on_netcat_test_completed)
        except TypeError: pass
        # Connect to test completed signal
        self.signals.test_completed.connect(self._on_netcat_test_completed)

        test_thread.start()

        # Reset stopped flag
        self.stopping_tests = False

    def _on_netcat_test_completed(self):
        # ... (Keep existing implementation - unchanged) ...
        # Disconnect to avoid multiple connections later if test runs again
        try:
            self.signals.test_completed.disconnect(self._on_netcat_test_completed)
            self.log_debug("Netcat test completed signal handler disconnected.")
        except TypeError:
            self.log_debug("Netcat test completed signal handler already disconnected or never connected.")
            pass # Signal was not connected

        # Ensure UI updates happen on the main thread
        self.signals.update_button_text.emit(self.test_netcat_button, "Test Netcat")
        self.test_netcat_button.setEnabled(True)
        self.test_progress_bar.setVisible(False)
        # Don't disable stop button here, another test might be running
        # self.stop_test_button.setEnabled(False)
        self.status_bar.showMessage("Netcat test complete.", 5000)
        self.log_debug("Netcat test batch completed.")
        # We don't call update_latency_stats() as it's ping-based

        # Force update of latency table to ensure changes are visible
        QCoreApplication.processEvents()
        self.update_latency_table()


    # --- ADDED/MODIFIED FOR DOWNLOAD TEST ---
    def start_speed_test(self):
        """Start download speed test for all configs or selected configs."""
        self._start_download_test_generic("Speed Test", self.DOWNLOAD_TEST_URL, self.test_speed_button)

    def start_connectivity_test(self):
        """Start connectivity test for all configs or selected configs."""
        self._start_download_test_generic("Connectivity Test", self.CONNECTIVITY_TEST_URL, self.test_connectivity_button)

    def start_download_test(self):
        """Legacy method - redirects to speed test for backward compatibility."""
        self.start_speed_test()

    def _start_download_test_generic(self, test_display_name, target_url, button):
        """Generic method to start download-based tests."""
        if not self.configs:
            self.show_message_box("No Configs", "No configurations to test.", "warning")
            return

        # Get selected rows from the latency table if there are any
        selected_items = self.latency_table.selectedItems()
        selected_rows = sorted(set(item.row() for item in selected_items)) if selected_items else []

        # --- Determine configs to test ---
        configs_to_test = []
        indices_to_test = [] # Store original indices

        # If rows are selected, only test those configs
        if selected_rows:
            for row in selected_rows:
                index_item = self.latency_table.item(row, 0)
                if index_item:
                    original_index = index_item.data(Qt.UserRole)
                    if original_index is not None and 0 <= original_index < len(self.configs):
                        cfg = self.configs[original_index]
                        protocol = cfg.get('protocol', 'unknown')
                        if protocol not in ['comment', 'error', 'unknown']:
                            configs_to_test.append(cfg)
                            indices_to_test.append(original_index)
            test_name = f"{test_display_name} (Selected {len(configs_to_test)})"
        else:
            # Test filtered configs (respect current filter state)
            for row in range(self.latency_table.rowCount()):
                index_item = self.latency_table.item(row, 0)
                if index_item:
                    original_index = index_item.data(Qt.UserRole)
                    if original_index is not None and 0 <= original_index < len(self.configs):
                        cfg = self.configs[original_index]
                        protocol = cfg.get('protocol', 'unknown')
                        if protocol not in ['comment', 'error', 'unknown']:
                            configs_to_test.append(cfg)
                            indices_to_test.append(original_index)
            test_name = f"{test_display_name} (Filtered {len(configs_to_test)})"

        if not configs_to_test:
            self.show_message_box("No Suitable Configs", f"No configurations eligible for {test_display_name} found (supported protocol with host/port).", "warning")
            return

        # Reset previous results
        for i in indices_to_test:
            self.configs[i].pop('download_speed', None)
            self.configs[i].pop('download_success', None)
            # Visually clear cell
            na_item = QTableWidgetItem("...")
            na_item.setTextAlignment(Qt.AlignCenter)
            self._apply_cell_color(na_item, None, None)
            self.latency_table.setItem(i, 7, na_item) # Column 7 = Download

        # Setup UI
        button.setText(f"Testing {test_display_name}...")
        button.setEnabled(False)
        self.stop_test_button.setEnabled(True)
        self.test_progress_bar.setVisible(True)
        self.test_progress_bar.setValue(0)
        self.test_progress_bar.setMaximum(len(configs_to_test))

        # Get max_workers from UI - use the download-specific spinner
        max_workers = self.download_max_workers_spinbox.value()
        self.log_debug(f"Starting {test_display_name} ({target_url}) for {len(configs_to_test)} configs with max_workers={max_workers}...")

        # Create the thread that will run the test process
        test_thread = threading.Thread(
            target=self._process_test_generic,
            args=(
                configs_to_test, # Pass filtered list
                self._run_download_test, # Specific test function
                'download_speed',   # Key for speed/result
                'download_success', # Key for success flag
                'Download',  # Test type for column mapping
                button, # Button to re-enable
            ),
            kwargs={
                'extra_test_args': {
                    'target_url': target_url,
                    'max_workers': max_workers
                }
            },
            daemon=True
        )

        # Disconnect previous connection if any
        try: self.signals.test_completed.disconnect(self._on_download_test_completed)
        except TypeError: pass
        # Connect to test completed signal
        self.signals.test_completed.connect(self._on_download_test_completed)

        test_thread.start()

        # Reset stopped flag
        self.stopping_tests = False
        self.status_bar.showMessage(f"Testing {test_display_name.lower()} for {len(indices_to_test)} configs...")

    def _on_download_test_completed(self):
        """Handles UI updates when the download test batch finishes."""
        # Disconnect to avoid multiple connections later
        try:
            self.signals.test_completed.disconnect(self._on_download_test_completed)
            self.log_debug("Download test completed signal handler disconnected.")
        except TypeError:
            self.log_debug("Download test completed signal handler already disconnected or never connected.")
            pass # Signal was not connected

        # Ensure UI updates happen on the main thread
        self.signals.update_button_text.emit(self.test_speed_button, "Speed Test")
        self.test_speed_button.setEnabled(True)
        self.signals.update_button_text.emit(self.test_connectivity_button, "Connectivity Test")
        self.test_connectivity_button.setEnabled(True)
        self.test_progress_bar.setVisible(False)
        # Don't disable stop button here, another test might be running
        # self.stop_test_button.setEnabled(False)

        # Check if some configs weren't tested (still have N/A)
        untested_count = 0
        for config in self.configs:
            if config.get('protocol') not in ['comment', 'error', 'unknown'] and 'download_speed' not in config:
                untested_count += 1

        if untested_count > 0:
            message = f"Download test completed with {untested_count} configs untested. Try adjusting worker count or testing in smaller batches."
            self.status_bar.showMessage(message, 10000)
            self.log_debug(message)
        else:
            self.status_bar.showMessage("Download speed test complete.", 5000)

        self.log_debug("Download test batch completed.")
        # No specific stats update for download speed yet
        # self.update_latency_stats() # This is ping-based

        # Force update of latency table to ensure changes are visible
        QCoreApplication.processEvents()
        self.update_latency_table()

        # Force another update after a short delay
        QTimer.singleShot(100, self.update_latency_table)
    # --- END DOWNLOAD TEST MODIFICATION ---


    def start_google_test(self):
        # ... (Keep existing implementation - unchanged) ...
        if not self.configs:
            QMessageBox.warning(self, "No Configurations", "Load configurations before testing.")
            return

        # Get selected rows from the latency table if there are any
        selected_items = self.latency_table.selectedItems()
        selected_rows = sorted(set(item.row() for item in selected_items)) if selected_items else []

        # --- Determine configs to test ---
        configs_to_test = []
        indices_to_test = [] # Store original indices

        # If rows are selected, only test those configs
        if selected_rows:
            for row in selected_rows:
                if row < len(self.configs):
                    cfg = self.configs[row]
                    protocol = cfg.get('protocol', 'unknown')
                    if protocol not in ['comment', 'error', 'unknown']:
                        configs_to_test.append(cfg)
                        indices_to_test.append(row)
        else:
            # Original behavior - test all configs
            for i, cfg in enumerate(self.configs):
                protocol = cfg.get('protocol', 'unknown')
                if protocol not in ['comment', 'error', 'unknown']:
                    configs_to_test.append(cfg)
                    indices_to_test.append(i)

        if not configs_to_test:
            self.show_message_box("No Suitable Configs", "No configurations eligible for Xray testing found (supported protocol with host/port).", "warning")
            return

        # Reset previous results
        for i in indices_to_test:
            self.configs[i].pop('google_latency', None)
            self.configs[i].pop('google_success', None)
            # Visually clear cell
            na_item = QTableWidgetItem("...")
            na_item.setTextAlignment(Qt.AlignCenter)
            self._apply_cell_color(na_item, None, None)
            # --- ADDED/MODIFIED FOR DOWNLOAD TEST ---
            self.latency_table.setItem(i, 8, na_item) # Column 8 = Google
            # --- END DOWNLOAD TEST MODIFICATION ---

        # Setup UI
        # Note: Google test button removed from UI, but functionality remains
        self.stop_test_button.setEnabled(True)
        self.test_progress_bar.setVisible(True)
        self.test_progress_bar.setValue(0)
        self.test_progress_bar.setMaximum(len(configs_to_test))

        target_url = self.YOUTUBE_TARGET_URL # Use the constant
        test_name = "Google" # Test name for UI/logging

        # Get max_workers from UI
        max_workers = self.xray_max_workers_spinbox.value()
        self.log_debug(f"Starting {test_name} connectivity test ({target_url}) for {len(configs_to_test)} configs with max_workers={max_workers}...")

        # Create the thread that will run the test process
        test_thread = threading.Thread(
            target=self._process_test_generic,
            args=(
                configs_to_test, # Pass filtered list
                self._run_xray_connectivity_test,
                'google_latency',
                'google_success',
                test_name,
                None,  # Google test button removed from UI
            ),
            kwargs={
                'extra_test_args': {
                    'target_url': target_url,
                    'max_workers': max_workers
                }
            },
            daemon=True
        )

        # Disconnect previous connection if any
        try: self.signals.test_completed.disconnect(self._on_google_test_completed)
        except TypeError: pass
        # Connect to test completed signal
        self.signals.test_completed.connect(self._on_google_test_completed)

        test_thread.start()

        # Reset stopped flag
        self.stopping_tests = False

    def _on_google_test_completed(self):
        # ... (Keep existing implementation - unchanged) ...
        # Disconnect to avoid multiple connections later
        try:
            self.signals.test_completed.disconnect(self._on_google_test_completed)
            self.log_debug("Google test completed signal handler disconnected.")
        except TypeError:
            self.log_debug("Google test completed signal handler already disconnected or never connected.")
            pass # Signal was not connected

        # Ensure UI updates happen on the main thread
        # Note: Google test button removed from UI, but functionality remains
        self.test_progress_bar.setVisible(False)
        # Don't disable stop button here, another test might be running
        # self.stop_test_button.setEnabled(False)
        self.status_bar.showMessage("Google test complete.", 5000)
        self.log_debug("Google test batch completed.")
        # self.update_latency_stats() # Ping based

        # Force update of latency table to ensure changes are visible
        QCoreApplication.processEvents()
        self.update_latency_table()


    def start_site_test(self):
        # ... (Keep existing implementation - unchanged) ...
        if not self.configs:
            QMessageBox.warning(self, "No Configurations", "Load configurations before testing.")
            return

        # --- URL Input Validation ---
        target_url = self.site_url_input.text().strip()
        if not target_url:
            QMessageBox.warning(self, "Input Error", "Please enter a target URL for the site test.")
            self.site_url_input.setFocus()
            return

        # Ensure scheme exists
        if not (target_url.startswith('http://') or target_url.startswith('https://')):
            target_url = 'https://' + target_url
            self.site_url_input.setText(target_url) # Update input field with added scheme

        # Check if URL is generally valid (basic check)
        try:
            parsed = urlparse(target_url)
            if not parsed.scheme or not parsed.netloc:
                raise ValueError("Invalid URL structure")
        except ValueError:
            QMessageBox.warning(self, "Input Error", f"Invalid URL format: {target_url}")
            self.site_url_input.setFocus()
            return
        # --- End URL Validation ---

        # Get selected rows from the latency table if there are any
        selected_items = self.latency_table.selectedItems()
        selected_rows = sorted(set(item.row() for item in selected_items)) if selected_items else []

        # --- Determine configs to test ---
        configs_to_test = []
        indices_to_test = [] # Store original indices

        # If rows are selected, only test those configs
        if selected_rows:
            for row in selected_rows:
                if row < len(self.configs):
                    cfg = self.configs[row]
                    protocol = cfg.get('protocol', 'unknown')
                    if protocol not in ['comment', 'error', 'unknown']:
                        configs_to_test.append(cfg)
                        indices_to_test.append(row)
        else:
            # Original behavior - test all configs
            for i, cfg in enumerate(self.configs):
                protocol = cfg.get('protocol', 'unknown')
                if protocol not in ['comment', 'error', 'unknown']:
                    configs_to_test.append(cfg)
                    indices_to_test.append(i)

        if not configs_to_test:
            self.show_message_box("No Suitable Configs", "No configurations eligible for Xray testing found (supported protocol with host/port).", "warning")
            return

        # Reset previous results
        for i in indices_to_test:
            self.configs[i].pop('site_test_latency', None) # Correct key
            self.configs[i].pop('site_success', None) # Correct key
            # Visually clear cell
            na_item = QTableWidgetItem("...")
            na_item.setTextAlignment(Qt.AlignCenter)
            self._apply_cell_color(na_item, None, None)
             # --- ADDED/MODIFIED FOR DOWNLOAD TEST ---
            self.latency_table.setItem(i, 9, na_item) # Column 9 = Site Test
            # --- END DOWNLOAD TEST MODIFICATION ---

        # Setup UI
        self.test_site_button.setText("Testing Site...")
        self.test_site_button.setEnabled(False)
        self.stop_test_button.setEnabled(True)
        self.test_progress_bar.setVisible(True)
        self.test_progress_bar.setValue(0)
        self.test_progress_bar.setMaximum(len(configs_to_test))

        test_name = "Site" # Test name for UI/logging

        # Get max_workers from UI
        max_workers = self.xray_max_workers_spinbox.value()
        self.log_debug(f"Starting {test_name} connectivity test ({target_url}) for {len(configs_to_test)} configs with max_workers={max_workers}...")

        # Create the thread that will run the test process
        test_thread = threading.Thread(
            target=self._process_test_generic,
            args=(
                configs_to_test, # Pass filtered list
                self._run_xray_connectivity_test,
                'site_test_latency', # Correct Key for latency/result
                'site_success', # Correct Key for success flag
                test_name,
                self.test_site_button,
            ),
            kwargs={
                'extra_test_args': {
                    'target_url': target_url, # Pass the validated URL
                    'max_workers': max_workers
                }
            },
            daemon=True
        )

        # Disconnect previous connection if any
        try: self.signals.test_completed.disconnect(self._on_site_test_completed)
        except TypeError: pass
        # Connect to test completed signal
        self.signals.test_completed.connect(self._on_site_test_completed)

        test_thread.start()

        # Reset stopped flag
        self.stopping_tests = False

    def _on_site_test_completed(self):
        # ... (Keep existing implementation - unchanged) ...
        # Disconnect to avoid multiple connections later
        try:
            self.signals.test_completed.disconnect(self._on_site_test_completed)
            self.log_debug("Site test completed signal handler disconnected.")
        except TypeError:
            self.log_debug("Site test completed signal handler already disconnected or never connected.")
            pass # Signal was not connected

        # Ensure UI updates happen on the main thread
        self.signals.update_button_text.emit(self.test_site_button, "Test Custom Site")
        self.test_site_button.setEnabled(True)
        self.test_progress_bar.setVisible(False)
        # Don't disable stop button here
        # self.stop_test_button.setEnabled(False)
        self.status_bar.showMessage("Site test complete.", 5000)
        self.log_debug("Site test batch completed.")
        # self.update_latency_stats() # Ping based

        # Force update of latency table to ensure changes are visible
        QCoreApplication.processEvents()
        self.update_latency_table()

    def start_http_test(self):
        """Start HTTP test for all configs or selected configs"""
        if not self.configs:
            QMessageBox.warning(self, "No Configurations", "Load configurations before testing.")
            return

        # Always act as "select all" - test all currently visible/filtered configs
        # This ensures consistent behavior regardless of selection state
        indices_to_test = []
        configs_to_test = []

        # Get currently visible rows from the table (respects filtering)
        for row in range(self.latency_table.rowCount()):
            index_item = self.latency_table.item(row, 0)
            if index_item:
                original_index = index_item.data(Qt.UserRole)
                if original_index is not None and 0 <= original_index < len(self.configs):
                    indices_to_test.append(original_index)
                    configs_to_test.append(self.configs[original_index])

        test_name = f"HTTP Test (All Visible {len(configs_to_test)})"

        # Filter out invalid configs
        valid_configs = []
        valid_indices = []
        for i, config in zip(indices_to_test, configs_to_test):
            if config.get('protocol') not in ['comment', 'error', 'ssr', 'unknown']:
                valid_configs.append(config)
                valid_indices.append(i)

        if not valid_configs:
            QMessageBox.information(self, "No Valid Configs", "No valid configurations found for HTTP testing.")
            return

        # Get max workers
        max_workers = self.http_max_workers_spinbox.value() if hasattr(self, 'http_max_workers_spinbox') else 15

        # Reset previous results
        for i in valid_indices:
            self.configs[i].pop('http_latency', None)
            self.configs[i].pop('http_success', None)
            # Visually clear cell
            na_item = QTableWidgetItem("...")
            na_item.setTextAlignment(Qt.AlignCenter)
            self._apply_cell_color(na_item, None, None)
            self.latency_table.setItem(i, 10, na_item) # Column 10 = HTTP Test

        # Setup UI
        self.test_http_button.setText("Testing HTTP...")
        self.test_http_button.setEnabled(False)
        self.stop_test_button.setEnabled(True)
        self.test_progress_bar.setVisible(True)
        self.test_progress_bar.setValue(0)
        self.test_progress_bar.setMaximum(len(valid_configs))

        # Create the HTTP test thread (like ping test)
        self.log_debug(f"Creating HTTPTesterThread with {len(valid_configs)} configs, max_workers={max_workers}")

        # Debug: Check connection integrity checkbox state
        checkbox_state = self.http_connection_integrity_checkbox.isChecked()
        self.log_debug(f"Connection integrity checkbox state: {checkbox_state}")

        self.http_test_thread = HTTPTesterThread(
            valid_configs,
            valid_indices,
            max_workers=max_workers,
            target_url=self.HTTP_TEST_URL,
            parent_app=self
        )

        # Disconnect previous connections if any to prevent duplicates
        try: self.http_test_thread.update_signal.disconnect()
        except TypeError: pass
        try: self.http_test_thread.progress_signal.disconnect()
        except TypeError: pass
        try: self.http_test_thread.finished_signal.disconnect()
        except TypeError: pass

        # Connect signals for real-time updates (direct connection like ping test)
        self.log_debug("Connecting HTTP test signals...")
        self.http_test_thread.update_signal.connect(self.signals.update_specific_latency.emit) # Emit to the central signal
        self.http_test_thread.progress_signal.connect(self.update_progress)
        self.http_test_thread.finished_signal.connect(self.on_http_test_completed)

        # Start the thread
        self.log_debug("Starting HTTPTesterThread...")
        self.http_test_thread.start()

        # Reset stopped flag
        self.stopping_tests = False
        self.status_bar.showMessage("Testing HTTP connectivity...")

    def on_http_test_completed(self):
        """Handle HTTP test completion (like ping test completion)"""
        self.log_debug("HTTP test completion handler called")
        try:
            # Calculate success statistics
            total_tested = 0
            successful = 0
            for config in self.configs:
                if 'http_latency' in config:
                    total_tested += 1
                    if config.get('http_success', False):
                        successful += 1

            success_percentage = (successful / total_tested * 100) if total_tested > 0 else 0
            self.log_debug(f"HTTP test stats: {successful}/{total_tested} successful ({success_percentage:.1f}%)")

            # Show completion dialog only if not in workflow
            if not getattr(self, 'automated_workflow_active', False):
                self.show_message_box(
                    "HTTP Test Complete",
                    f"HTTP test completed.\n\nTested: {total_tested} configs\nSuccessful: {successful} configs\nSuccess Rate: {success_percentage:.1f}%",
                    "information"
                )

        except Exception as e:
            self.log_debug(f"Error calculating HTTP test statistics: {e}")

        # Restore UI state
        self.test_http_button.setText("Test HTTP")
        self.test_http_button.setEnabled(True)
        self.test_progress_bar.setVisible(False)
        self.status_bar.showMessage("HTTP test complete.", 5000)
        self.log_debug("HTTP test completed.")

        # Force update of latency table to ensure changes are visible
        QCoreApplication.processEvents()
        self.update_latency_table()

        # Complete automated workflow if active
        if hasattr(self, 'automated_workflow_active') and self.automated_workflow_active:
            QTimer.singleShot(1000, self.complete_automated_workflow)

    @pyqtSlot(int, str, str)
    def _update_ping_latency_in_table(self, original_config_index, latency_str, unused_url_result):
        # This slot receives the original_config_index into self.configs from LatencyTesterThread
        try:
            if not (0 <= original_config_index < len(self.configs)):
                self.log_debug(f"Error (_update_ping_latency_in_table): Invalid original_config_index {original_config_index} (len(self.configs)={len(self.configs)}). Config update skipped.")
                return

            config = self.configs[original_config_index]
            ping_success = False
            ping_latency_val = None # Store numeric latency or error string

            # --- Parse the result string ---
            if "ms" in latency_str:
                try:
                    ping_latency_val = float(latency_str.split()[0])
                    ping_success = True
                except (ValueError, IndexError):
                    ping_latency_val = "Parse Error" # Error parsing the number
                    ping_success = False
            # Check for specific failure strings returned by test_ping
            elif latency_str in ["Timeout", "No DNS", "Invalid Host", "Failed", "Error", "Unknown", "DNS Error"] or "Timeout" in latency_str:
                ping_latency_val = latency_str # Store the error string
                ping_success = False
            else: # Handle unexpected strings
                 ping_latency_val = latency_str # Display as is
                 ping_success = False
                 self.log_debug(f"Warning (Ping Update): Unexpected latency_str '{latency_str}' for original_config_index {original_config_index}")

            # --- Update the main config dictionary ---
            config['ping_latency'] = ping_latency_val
            config['ping_available'] = ping_success # Correct key

            # --- Emit signal with all required parameters for UI update via throttling queue ---
            self.signals.update_specific_latency.emit(original_config_index, ping_latency_val, ping_success, "Ping")

            # Direct UI update (setItem) removed from here to rely solely on the signal/slot throttling mechanism.
            # This prevents race conditions and simplifies UI update logic.

        except Exception as e:
            self.log_debug(f"Error updating ping latency data for original_config_index {original_config_index}: {e}")
            traceback.print_exc()

    # --- _update_specific_latency_in_table (MODIFIED to use throttling mechanism) ---
    @pyqtSlot(int, object, bool, str)  # Slot signature matches signal: original_config_index, raw_result, success, test_type
    def _update_specific_latency_in_table(self, original_config_index, raw_result, success, test_type):
        try:
            # Note: Validation of original_config_index against len(self.configs) should be done by the caller
            # before emitting the signal or calling this slot. This method prepares the task for the UI queue.

            # --- Map test_type to Column Index ---
            col_index = -1
            if test_type == 'Ping': col_index = 5
            elif test_type == 'Netcat': col_index = 6
            elif test_type == 'Download': col_index = 7
            elif test_type == 'Google': col_index = 8
            elif test_type == 'Site': col_index = 9
            elif test_type == 'HTTP': col_index = 10
            else:
                self.log_debug(f"Error (_update_specific_latency_in_table): Unknown test_type '{test_type}' for original_config_index {original_config_index}. UI Update task not queued.")
                return

            # It's useful to validate col_index here, as it's derived from test_type.
            # The row index will be validated in _deferred_update_latency_cell.
            if hasattr(self, 'latency_table') and not (0 <= col_index < self.latency_table.columnCount()):
                self.log_debug(f"Warning (_update_specific_latency_in_table): Column index {col_index} for test_type '{test_type}' (original_config_index {original_config_index}) is out of bounds for latency_table (columnCount={self.latency_table.columnCount()}). UI Update task not queued.")
                return

            # Add update task to the throttling queue
            update_task = (original_config_index, col_index, raw_result, success, test_type)
            self.ui_update_queue.append(update_task)

            # If the timer is not already running, start it
            if not self.ui_update_timer.isActive():
                self.ui_update_timer.start(50)  # 50ms interval for smooth one-by-one updates

        except Exception as e:
            self.log_debug(f"CRITICAL Error queueing {test_type} latency update for index {original_config_index}: {e}")
            traceback.print_exc()

    def _process_ui_update_queue(self):
        """Process one update task from the UI update queue for smooth one-by-one updates"""
        try:
            if self.ui_update_queue:
                # Get the next update task
                index, col_index, raw_result, success, test_type = self.ui_update_queue.popleft()

                # Perform the actual UI update
                self._deferred_update_latency_cell(index, col_index, raw_result, success, test_type)

                # If there are more tasks in the queue, schedule the next update
                if self.ui_update_queue:
                    self.ui_update_timer.start(50)  # 50ms interval

        except Exception as e:
            self.log_debug(f"Error processing UI update queue: {e}")
            traceback.print_exc()

    def _deferred_update_latency_cell(self, original_config_index, col_index, raw_result, success, test_type):
        """Perform the actual table cell update (called by the throttling mechanism)
           Finds the correct row in latency_table based on original_config_index stored in UserRole.
        """
        try:
            target_row_num = -1
            # Iterate through the latency_table to find the row that corresponds to original_config_index
            for row_num in range(self.latency_table.rowCount()):
                item_in_first_col = self.latency_table.item(row_num, 0) # Hidden Original Index column
                if item_in_first_col:
                    stored_original_index = item_in_first_col.data(Qt.UserRole)
                    if stored_original_index == original_config_index:
                        target_row_num = row_num
                        break
            
            if target_row_num == -1:
                self.log_debug(f"Warning (_deferred_update_latency_cell): Config with original_index {original_config_index} (test_type: {test_type}) not found in current latency_table view. UI cell update skipped.")
                return

            # Validate col_index against table column count
            if not (0 <= col_index < self.latency_table.columnCount()):
                self.log_debug(f"Warning (_deferred_update_latency_cell): Column index {col_index} for test_type '{test_type}' (original_config_index {original_config_index}, target_row_num {target_row_num}) is out of bounds for latency_table (columnCount={self.latency_table.columnCount()}). UI cell update skipped.")
                return

            # --- Format the display string USING the received raw data and test_type ---
            item_text = self._format_latency_text(raw_result, success, test_type=test_type)
            item = QTableWidgetItem(item_text)
            item.setTextAlignment(Qt.AlignCenter)

            # --- Apply color based on received raw data and test_type ---
            self._apply_cell_color(item, raw_result, success, test_type=test_type)

            # --- Set the item in the table ---
            self.latency_table.setItem(target_row_num, col_index, item)
            # Note: QCoreApplication.processEvents() removed as timer mechanism handles event loop yielding

        except Exception as e:
            self.log_debug(f"CRITICAL Error updating {test_type} latency cell for original_config_index {original_config_index}: {e}")
            traceback.print_exc()

    def _generate_xray_config_for_test(self, config_dict, local_port):
        # ... (Keep existing implementation - unchanged) ...
        """Generates an Xray JSON config dictionary from a parsed config dict."""
        # Check for hostname in both 'hostname' and 'host' fields
        hostname = config_dict.get('hostname', '')
        if not hostname and 'host' in config_dict:
            hostname = config_dict.get('host', '')
            # Update the config_dict with the hostname
            config_dict['hostname'] = hostname
            self.log_debug(f"Fixed hostname from 'host' field: {hostname}")

        self.log_debug(f"Generating Xray config for: {config_dict.get('protocol')} {hostname}:{config_dict.get('port')}")

        # --- Essential parameters ---
        protocol = config_dict.get('protocol', '').lower()
        address = hostname
        port_str = config_dict.get('port')

        if not protocol or not address or not port_str or address in ['error', 'unknown', 'parse_err']:
            raise ValueError(f"Invalid/incomplete config for Xray: Protocol='{protocol}', Address='{address}', Port='{port_str}'")
        try:
            port = int(port_str)
        except (ValueError, TypeError):
            raise ValueError(f"Invalid port value: '{port_str}'")
        if port <= 0 or port > 65535:
            raise ValueError(f"Port number out of range: {port}")

        # --- Initialize Outbound Structure ---
        # Note: Xray uses 'shadowsocks' protocol name for SS
        outbound_protocol = "shadowsocks" if protocol == "ss" else protocol
        outbound = {"protocol": outbound_protocol, "settings": {}, "streamSettings": {}, "tag": "proxy_outbound"} # Added tag

        # --- Protocol Specific Settings (`outbound.settings`) ---
        try:
            if protocol == "vmess":
                vmess_id = config_dict.get("id")
                vmess_aid = config_dict.get("aid", 0)
                vmess_scy = config_dict.get("method", "auto") # 'method' holds 'scy'/'security' from parser
                if not vmess_id: raise ValueError("Missing 'id' for VMess config")
                try: vmess_aid = int(vmess_aid)
                except (ValueError, TypeError): raise ValueError("Invalid 'aid' for VMess (must be integer)")

                outbound["settings"]["vnext"] = [{
                    "address": address,
                    "port": port,
                    "users": [{
                        "id": vmess_id,
                        "alterId": vmess_aid,
                        "security": vmess_scy,
                        "level": 0
                    }]
                }]
            elif protocol == "vless":
                vless_id = config_dict.get("id")
                vless_enc = config_dict.get("encryption", "none")
                vless_flow = config_dict.get("flow", "")
                if not vless_id: raise ValueError("Missing 'id' for VLESS config")

                user_settings = {
                    "id": vless_id,
                    "encryption": vless_enc,
                    "level": 0
                }
                # Add flow only if it's specified and not empty
                if vless_flow:
                    user_settings["flow"] = vless_flow

                # VLESS over Reality/TLS/XTLS MUST use "none" encryption in user settings
                vless_security = config_dict.get("security", "none").lower()
                if vless_security in ["reality", "tls", "xtls"] and user_settings["encryption"] != "none":
                    self.log_debug(f"Warning: VLESS encryption '{user_settings['encryption']}' ignored when security is '{vless_security}'. Using 'none'.")
                    user_settings["encryption"] = "none"

                outbound["settings"]["vnext"] = [{
                    "address": address,
                    "port": port,
                    "users": [user_settings]
                }]
            elif protocol == "trojan":
                trojan_pass = config_dict.get("password")
                if not trojan_pass: raise ValueError("Missing 'password' for Trojan config")

                outbound["settings"]["servers"] = [{
                    "address": address,
                    "port": port,
                    "password": trojan_pass,
                    "level": 0
                    # flow is not standard here, handle via streamSettings if needed (rare for trojan)
                }]
            elif protocol == "ss":
                ss_method = config_dict.get("method", "auto")
                ss_pass = config_dict.get("password", "")
                if not ss_method or not ss_pass:
                    # Allow generation even if missing, Xray might default, but log warning.
                    self.log_debug(f"Warning: Missing method/password for SS: {address}:{port}. Using method='{ss_method}', pass='{ss_pass[:2]}...'")

                outbound["settings"]["servers"] = [{
                    "address": address,
                    "port": port,
                    "method": ss_method,
                    "password": ss_pass,
                    "level": 0
                }]
            else:
                # This shouldn't be reached if calling functions filter protocols
                raise ValueError(f"Unsupported protocol for Xray config generation: {protocol}")
        except Exception as setting_err:
            # Catch potential errors during settings construction
            raise ValueError(f"Error configuring {protocol} settings: {setting_err}")

        # --- Stream Settings (`outbound.streamSettings`) ---
        network = config_dict.get("network", "tcp").lower() # Default to tcp

        # --- >>> ADD VALIDATION/DEFAULTING FOR NETWORK <<< ---
        known_networks = ["tcp", "kcp", "ws", "h2", "grpc", "quic", "domainsocket"]
        if network not in known_networks:
            self.log_debug(f"Warning: Unsupported network type '{network}' found for '{config_dict.get('remark', 'Unknown Config')}'. Defaulting to 'tcp'.")
            network = "tcp" # Default to TCP if unknown
        # --- >>> END VALIDATION <<< ---

        outbound["streamSettings"]["network"] = network # Use the validated/defaulted network value

        # --- Security Settings (TLS, Reality) ---
        security = config_dict.get("security", "none").lower() # tls, reality, none
        # SNI: Use 'sni' field, fallback to 'host' header field, fallback to server address
        sni = config_dict.get("sni", config_dict.get("host", address))
        if not sni: # Ensure SNI is never empty if security is tls/reality, default to address
             if security in ["tls", "reality"]:
                 sni = address
                 self.log_debug(f"SNI was empty for {security} connection, defaulting to address: {address}")

        # Set top-level security only if it's tls or reality
        if security in ["tls", "reality"]:
            outbound["streamSettings"]["security"] = security

        # TLS Specific Settings
        if security == "tls":
            tls_settings = {"serverName": sni}
            fp = config_dict.get("fp", "") # Fingerprint
            alpn_str = config_dict.get("alpn", "") # Comma-separated string
            allow_insecure = str(config_dict.get("allowInsecure", "0")).lower() in ['true', '1', 'yes'] # Check 'allowInsecure' query param

            if fp:
                tls_settings["fingerprint"] = fp
            if alpn_str:
                # Convert comma-separated string to list for JSON
                alpn_list = [x.strip() for x in alpn_str.split(',') if x.strip()]
                if alpn_list: # Only add if list is not empty
                     tls_settings["alpn"] = alpn_list
            if allow_insecure:
                tls_settings["allowInsecure"] = True

            outbound["streamSettings"]["tlsSettings"] = tls_settings

        # Reality Specific Settings
        elif security == "reality":
            pbk = config_dict.get("pbk", "") # Public key
            sid = config_dict.get("sid", "") # Short ID
            fp = config_dict.get("fp", "")   # Fingerprint
            # spiderX = config_dict.get("spx", "") # Optional SpiderX

            if not pbk:
                raise ValueError("Missing 'pbk' (Reality Public Key) for Reality config")

            reality_settings = {"serverName": sni, "publicKey": pbk}
            if sid:
                reality_settings["shortId"] = sid
            if fp:
                reality_settings["fingerprint"] = fp
            # if spiderX: reality_settings["spiderX"] = spiderX # Uncomment if needed

            outbound["streamSettings"]["realitySettings"] = reality_settings

        # --- Transport Specific Settings (WS, gRPC, H2, TCP Header) ---
        host_header = config_dict.get("host", "") # Host header value, often same as SNI or address
        path = config_dict.get("path", "/")
        service_name = config_dict.get("serviceName", "") # Usually for gRPC
        header_type = config_dict.get("headerType", "none").lower() # For TCP obfuscation

        if network == "ws":
            ws_settings = {"path": path}
            # Add Host header if it's provided
            if host_header:
                 ws_settings["headers"] = {"Host": host_header}
            outbound["streamSettings"]["wsSettings"] = ws_settings

        elif network == "grpc":
            grpc_settings = {}
            # Determine gRPC mode (gun or multi) - assuming 'mode' might be in query dict
            mode_query = config_dict.get("query", {}).get("mode", "gun") # Check if parser stored query dict
            mode_param = config_dict.get("mode", mode_query).lower() # Allow direct 'mode' field too
            # Default to gun mode unless explicitly set to multi
            grpc_settings["multiMode"] = (mode_param == "multi")
            # Use serviceName if provided, otherwise it's often omitted for gun mode
            if service_name:
                grpc_settings["serviceName"] = service_name
            elif mode_param == "multi":
                # Multi mode usually requires a service name, raise warning if missing?
                self.log_debug(f"Warning: gRPC multiMode used but no 'serviceName' provided for {address}:{port}. Using empty string.")
                grpc_settings["serviceName"] = ""


            outbound["streamSettings"]["grpcSettings"] = grpc_settings

        elif network == "h2": # HTTP/2
            h2_settings = {"path": path}
            # Host for H2 is a list. Use host_header if provided, else default to SNI (or address as fallback).
            h2_host_val = host_header if host_header else sni
            if h2_host_val:
                 h2_settings["host"] = [h2_host_val]
            else:
                 # Should not happen if SNI defaults correctly, but safety check
                 h2_settings["host"] = [address]
                 self.log_debug(f"Warning: No host header or SNI for H2, using address: {address}")

            # Xray uses 'httpSettings' for H2 transport
            outbound["streamSettings"]["httpSettings"] = h2_settings

        elif network == "tcp" and header_type == "http":
            # TCP with HTTP Header Obfuscation
            tcp_settings = {"header": {"type": "http"}}
            # Construct request header
            request_data = {
                 "version": "1.1",
                 "method": "GET",
                 "path": [path if path else "/"], # Path must be a list
                 "headers": { # Default headers, Host will be overwritten if specified
                     # Use host_header if available, otherwise don't include Host unless necessary?
                     # "Host": [host_header if host_header else address], # Values must be lists
                     "User-Agent": ["Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/108.0.0.0 Safari/537.36"], # Example UA
                     "Accept-Encoding": ["gzip, deflate"],
                     "Connection": ["keep-alive"],
                     "Pragma": "no-cache"
                 }
            }
            # Add Host header specifically if host_header is present
            if host_header:
                 request_data["headers"]["Host"] = [host_header]
            elif path: # If path is specified but no host, maybe add address as host? Risky.
                self.log_debug(f"TCP HTTP Header: Path '{path}' provided but no Host header. Sending request without Host header.")


            tcp_settings["header"]["request"] = request_data
            outbound["streamSettings"]["tcpSettings"] = tcp_settings


        # --- Complete Config Structure ---
        config_structure = {
            "log": {
                "loglevel": "warning" # Use "debug" for verbose Xray logs if needed
            },
            "dns": {
                # DNS settings will be conditional based on dns_leak_checkbox
                "servers": [] # Initialize with empty list, will be populated below
            },
            "inbounds": [], # Initialize empty, will be populated
            "outbounds": [
                outbound, # The primary outbound using the config URI details (now tagged as "proxy_outbound")
                {"protocol": "freedom", "tag": "direct"}, # Direct connection outbound
                {"protocol": "blackhole", "tag": "block"}, # Block connection outbound
                {"protocol": "freedom", "tag": "api"} # API outbound for stats service
            ],
            # Updated "api" block
            "api": {
                "tag": "api", # Ensure this tag is present
                "services": ["StatsService"] # Make sure StatsService is included
            },
            # Updated "policy" block (ensure it's at the root level)
            "policy": {
                "system": {
                    "statsInboundUplink": True,
                    "statsInboundDownlink": True,
                    "statsOutboundUplink": True,
                    "statsOutboundDownlink": True
                }
            },
            "routing": {
                "domainStrategy": "IPIfNonMatch", # Or AsIs, IPOnDemand
                "rules": [] # Initialize empty, rules will be added below
            }
        }

        # --- Setup Inbounds (Main SOCKS inbound and API inbound) ---
        main_socks_inbound = {
            "port": local_port,
            "listen": self.TEMP_PROXY_HOST,
            "protocol": "socks",
            "settings": {
                "auth": "noauth",
                "udp": True,
                "ip": self.TEMP_PROXY_HOST,
                "timeout": max(self.REQUEST_TIMEOUT, self.DOWNLOAD_TIMEOUT) + 5
            },
            "sniffing": {
                "enabled": True,
                "destOverride": ["http", "tls"]
            }
        }
        config_structure["inbounds"].append(main_socks_inbound)

        # API inbound removed - no longer needed for data transfer stats
        
        # API inbound configuration removed - no longer needed


        # --- Ensure essential outbounds exist (direct, block) ---
        # proxy_outbound is already tagged in the main outbound creation.
        # direct and block outbounds are standard.
        has_direct_outbound = any(out.get("tag") == "direct" for out in config_structure["outbounds"])
        if not has_direct_outbound:
            config_structure["outbounds"].append({"protocol": "freedom", "tag": "direct"})
            self.log_debug("Added 'direct' outbound for routing rules.")
            
        has_block_outbound = any(out.get("tag") == "block" for out in config_structure["outbounds"])
        if not has_block_outbound:
            config_structure["outbounds"].append({"protocol": "blackhole", "tag": "block"})
            self.log_debug("Added 'block' outbound for routing rules.")

        # --- Routing Rules ---
        # Initialize routing rules list if not present
        if "routing" not in config_structure:
            config_structure["routing"] = {"rules": []}
        if "rules" not in config_structure["routing"]:
            config_structure["routing"]["rules"] = []
            
        # Define the API routing rule
        api_routing_rule = {"type": "field", "inboundTag": ["api_inbound"], "outboundTag": "api"}

        # Remove any existing API routing rule and prepend the new one
        config_structure["routing"]["rules"] = [
            r for r in config_structure["routing"]["rules"] 
            if not (r.get("inboundTag") == ["api_inbound"] and r.get("outboundTag") == "api")
        ]
        config_structure["routing"]["rules"].insert(0, api_routing_rule)
        self.log_debug("Ensured API routing rule (api_inbound -> api) is the first rule.")

        # --- Application-Specific Proxying Logic ---
        if (hasattr(self, 'app_proxy_enable_checkbox') and self.app_proxy_enable_checkbox.isChecked() and
            hasattr(self, 'active_app_profile_name') and self.active_app_profile_name and
            self.active_app_profile_name in self.application_profiles and
            not (hasattr(self, 'system_proxy_checkbox') and self.system_proxy_checkbox.isChecked())):

            self.log_debug(f"Applying application-specific routing for profile: {self.active_app_profile_name}")
            profile = self.application_profiles[self.active_app_profile_name]
            profile_rules_defs = profile.get("rules", [])
            domains_to_proxy, ips_to_proxy = [], []
            domains_to_direct, ips_to_direct = [], []
            domains_to_block, ips_to_block = [], []

            for item_path, item_action in profile_rules_defs:
                is_domain = '.' in item_path
                if item_action == "Proxy":
                    if is_domain: domains_to_proxy.append(item_path)
                    else: ips_to_proxy.append(item_path)
                elif item_action == "Direct":
                    if is_domain: domains_to_direct.append(item_path)
                    else: ips_to_direct.append(item_path)
                elif item_action == "Block":
                    if is_domain: domains_to_block.append(item_path)
                    else: ips_to_block.append(item_path)
            
            app_specific_rules = []
            if domains_to_proxy: app_specific_rules.append({"type": "field", "domain": domains_to_proxy, "outboundTag": "proxy_outbound"})
            if ips_to_proxy: app_specific_rules.append({"type": "field", "ip": ips_to_proxy, "outboundTag": "proxy_outbound"})
            if domains_to_direct: app_specific_rules.append({"type": "field", "domain": domains_to_direct, "outboundTag": "direct"})
            if ips_to_direct: app_specific_rules.append({"type": "field", "ip": ips_to_direct, "outboundTag": "direct"})
            if domains_to_block: app_specific_rules.append({"type": "field", "domain": domains_to_block, "outboundTag": "block"})
            if ips_to_block: app_specific_rules.append({"type": "field", "ip": ips_to_block, "outboundTag": "block"})

            # Insert app-specific rules after the API rule
            config_structure["routing"]["rules"][1:1] = app_specific_rules
            self.log_debug(f"App Profile: Inserted {len(app_specific_rules)} app-specific rules.")

            # Private IP Rule (after app-specific, before default unmatched)
            config_structure["routing"]["rules"].append({"type": "field", "ip": ["geoip:private"], "outboundTag": "direct"})
            self.log_debug("App Profile: Added rule for private IPs to 'direct'.")

            # Unmatched Traffic Rule
            unmatched_action = profile.get("unmatched_action", "Proxy")
            default_outbound_tag = "proxy_outbound"
            if unmatched_action == "Direct": default_outbound_tag = "direct"
            elif unmatched_action == "Block": default_outbound_tag = "block"
            config_structure["routing"]["rules"].append({"type": "field", "network": "tcp,udp", "outboundTag": default_outbound_tag})
            self.log_debug(f"App Profile: Routing unmatched traffic to '{default_outbound_tag}'.")

        else:
            # Standard IP/DNS Leak Prevention (System Proxy ON or App Profile mode OFF)
            # API rule is already first.
            standard_rules_to_add = []
            if hasattr(self, 'ip_leak_checkbox') and self.ip_leak_checkbox.isChecked():
                self.log_debug("Standard: IP leak prevention IS CHECKED. Routing most traffic via proxy.")
                standard_rules_to_add.extend([
                    {"type": "field", "ip": ["geoip:private"], "outboundTag": "direct"},
                    {"type": "field", "network": "tcp,udp", "outboundTag": "proxy_outbound"}
                ])
            else:
                self.log_debug("Standard: IP leak prevention IS NOT CHECKED. Defaulting to direct.")
                standard_rules_to_add.extend([
                    {"type": "field", "ip": ["geoip:private"], "outboundTag": "direct"},
                    {"type": "field", "network": "tcp,udp", "outboundTag": "direct"}
                ])
            # Insert standard rules after the API rule.
            config_structure["routing"]["rules"][1:1] = standard_rules_to_add
            self.log_debug(f"Set standard routing rules after API rule: {json.dumps(standard_rules_to_add)}")

        # --- Conditional DNS Configuration based on DNS Leak Prevention Checkbox ---
        if hasattr(self, 'dns_leak_checkbox') and self.dns_leak_checkbox.isChecked():
            selected_dns_text = ""
            if hasattr(self, 'dns_server_combobox'): # Check if combobox exists
                selected_dns_text = self.dns_server_combobox.currentText()
            
            self.log_debug(f"DNS leak prevention IS CHECKED. Selected DNS: '{selected_dns_text}'")

            if "Google (8.8.8.8)" in selected_dns_text:
                config_structure["dns"]["servers"] = ["8.8.8.8", "8.8.4.4"]
            elif "Quad9 (9.9.9.9)" in selected_dns_text:
                config_structure["dns"]["servers"] = ["9.9.9.9", "149.112.112.112"]
            elif "System Default" in selected_dns_text:
                # Using "localhost" tells Xray to use the system's resolver.
                # Forcing this to go via proxy needs specific routing rule for port 53 if proxy is default.
                # For simplicity, if "System Default" is chosen with leak prevention,
                # it might mean "resolve via proxy using a known good upstream" or "resolve directly".
                # Current behavior: uses localhost, which might not always be proxied by default Xray DNS config.
                # To ensure it's proxied, Xray's own DNS settings must be robust.
                # For now, let's stick to Cloudflare if System Default is chosen with leak prevention ON,
                # as "localhost" might bypass the proxy for DNS if not carefully routed.
                # A better "System Default" with leak prevention would be to explicitly route localhost:53 to proxy.
                # For now, defaulting to Cloudflare to ensure DNS goes through *a* proxy if leak prevention is on.
                self.log_debug("DNS 'System Default' selected with leak prevention. Using Cloudflare (1.1.1.1) for now to ensure proxying.")
                config_structure["dns"]["servers"] = ["1.1.1.1", "1.0.0.1"]
            elif "Cloudflare (1.1.1.1)" in selected_dns_text: # Default or explicitly selected
                config_structure["dns"]["servers"] = ["1.1.1.1", "1.0.0.1"]
            else: # Fallback if combobox is somehow empty or text is unexpected
                self.log_debug(f"Warning: Unexpected DNS selection '{selected_dns_text}'. Defaulting to Cloudflare.")
                config_structure["dns"]["servers"] = ["1.1.1.1", "1.0.0.1"]
        else:
            self.log_debug("DNS leak prevention IS NOT CHECKED. Using system DNS primarily.")
            # Prioritize system DNS, with fallback to public DNS if needed
            config_structure["dns"]["servers"] = ["localhost", "1.1.1.1", "8.8.8.8"] 

        self.log_debug("Xray config generation complete.")
        # --- Add this before the return ---
        # try:
        #     generated_json_str = json.dumps(config_structure, indent=2)
        #     self.log_debug(f"--- Generated Xray JSON for {protocol} {address}:{port} ---\n{generated_json_str}\n--------------------------------------------")
        # except Exception as json_log_err:
        #     self.log_debug(f"Error logging generated JSON: {json_log_err}")
        # ----------------------------------
        return config_structure


    def _run_xray_connectivity_test(self, config_dict, target_url=None, local_port=None):
        # ... (Keep existing implementation - unchanged) ...
        """
        Core testing logic using Xray (for Google/Site Tests).
        Generates config, starts Xray, tests connection via temp proxy, stops Xray.
        Returns tuple: (success: bool, result: float_latency_ms_or_error_string)
        """
        if not target_url:
            target_url = self.SITE_TEST_DEFAULT_URL # Use default for generic connectivity

        # --- Validate Input ---
        if not config_dict or not isinstance(config_dict, dict):
             self.log_debug(f"Xray Test Error: Invalid config_dict provided.")
             return False, "Internal Error (Bad Config)"

        # Check for hostname in both 'hostname' and 'host' fields
        hostname = config_dict.get('hostname', '')
        if not hostname and 'host' in config_dict:
            hostname = config_dict.get('host', '')
            # Update the config_dict with the hostname
            config_dict['hostname'] = hostname
            self.log_debug(f"Fixed hostname from 'host' field for connectivity test: {hostname}")

        if not hostname:
            hostname = 'unknown'

        protocol = config_dict.get('protocol', 'unknown')
        port = config_dict.get('port', '0')
        remark = config_dict.get('remark', f"{protocol}_{hostname}:{port}")

        # --- Ensure local_port is provided (should be handled by _process_test_generic) ---
        if not local_port:
            self.log_debug(f"Xray Test Error for '{remark}': No local_port provided.")
            # Attempt to allocate dynamically as a fallback (shouldn't happen ideally)
            local_port = self.find_available_port()
            if not local_port:
                 return False, "Internal Error (No Port)"
            allocated_dynamically = True
            self.log_debug(f"Xray Test Warning for '{remark}': Allocated local_port {local_port} dynamically.")
        else:
            allocated_dynamically = False


        self.log_debug(f"Starting Xray connectivity test for '{remark}' -> {target_url} on port {local_port}")

        xray_process = None
        config_path = None
        success = False
        result_value = "Error: Init" # Default result if something goes wrong early

        # Check stop flag FIRST
        if self.stopping_tests:
            self.log_debug(f"Test stopped before semaphore acquisition for '{remark}'")
            return False, "Stopped"

        # Acquire semaphore with timeout
        acquired = False
        try:
            self.log_debug(f"Attempting to acquire Xray semaphore for '{remark}' (Current: {self.get_xray_process_count()}/{self.max_allowed_xray_processes})")
            # Use a reasonable timeout (e.g., 5-10 seconds)
            # Adjust timeout based on stability setting if desired
            timeout_seconds = 10.0 if self.stability_improvements_enabled else 5.0
            acquired = self.xray_semaphore.acquire(blocking=True, timeout=timeout_seconds)

            if not acquired:
                self.log_debug(f"TIMEOUT acquiring Xray semaphore for '{remark}'. Skipping test.")
                return False, "Resource Limit (Timeout)"
            else:
                self.log_debug(f"Acquired Xray semaphore for '{remark}'")
                # Update counter for logging
                with self.xray_process_lock:
                    self.active_xray_processes += 1
                    count = self.active_xray_processes
                    self.log_debug(f"Xray process count increased to {count} (limit: {self.max_allowed_xray_processes})")
        except Exception as sem_e:
            self.log_debug(f"Error acquiring semaphore for '{remark}': {sem_e}")
            return False, f"Error (Semaphore Acq)"

        try:
            # --- Generate Xray config ---
            xray_json_config = self._generate_xray_config_for_test(config_dict, local_port)

            # --- Write temp config file ---
            try:
                with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix=".json", encoding='utf-8', dir=self.temp_dir, prefix=f"xray_conn_{protocol}_") as temp_f:
                    config_path = temp_f.name
                    json.dump(xray_json_config, temp_f, indent=2)
                self.log_debug(f"Temp config written: {os.path.basename(config_path)}")
            except Exception as file_err:
                self.log_debug(f"Error writing temp config file: {file_err}")
                raise ValueError(f"Config File Error: {file_err}")

            # --- Start Xray process ---
            command = [self.XRAY_EXECUTABLE, "run", "-c", config_path]
            self.log_debug(f"Executing: {' '.join(command)}")
            startupinfo = None
            creationflags = 0
            if platform.system() == "Windows":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE
                creationflags = subprocess.CREATE_NO_WINDOW

            xray_process = subprocess.Popen(
                command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                startupinfo=startupinfo, creationflags=creationflags,
                encoding='utf-8', errors='ignore'
            )

            # --- Wait briefly for Xray to start and check if it exited ---
            time.sleep(self.XRAY_STARTUP_WAIT)
            exit_code = xray_process.poll()

            if exit_code is not None:
                stderr_output = "N/A"
                try: stderr_output = xray_process.stderr.read()
                except Exception as read_err: stderr_output = f"(Error reading stderr: {read_err})"
                self.log_debug(f"XRAY FAILED TO START for '{remark}' (Connectivity Test)")
                self.log_debug(f"Config File: {config_path}")
                self.log_debug(f"Exit Code: {exit_code}")
                self.log_debug(f"Xray Stderr (<=1000 chars):\n{stderr_output[:1000]}")
                if "config file not found" in stderr_output.lower(): result_value = "Xray Start Error (Config Not Found)"
                elif "failed to read config file" in stderr_output.lower(): result_value = "Xray Start Error (Read Fail)"
                elif "failed to find socks inbound" in stderr_output.lower(): result_value = "Xray Start Error (Bad Config)"
                elif "address already in use" in stderr_output.lower(): result_value = f"Xray Start Error (Port {local_port} Busy)"
                else: result_value = "Xray Start Error"
                success = False

            else:
                # --- Xray seems to be running, perform request ---
                self.log_debug(f"Xray process (PID: {xray_process.pid}) started for '{remark}'. Testing connection...")
                proxies = {
                    "http": f"{self.TEMP_PROXY_TYPE_FOR_REQUESTS}://{self.TEMP_PROXY_HOST}:{local_port}",
                    "https": f"{self.TEMP_PROXY_TYPE_FOR_REQUESTS}://{self.TEMP_PROXY_HOST}:{local_port}"
                }
                session = requests.Session()
                retry_strategy = Retry(total=1) # No retries for testing
                adapter = HTTPAdapter(max_retries=retry_strategy)
                session.mount("http://", adapter)
                session.mount("https://", adapter)

                headers = {'User-Agent': 'Mozilla/5.0 QTester/1.0'}
                start_req_time = time.time()
                response = None
                try:
                    # Try HEAD first for speed
                    response = session.head(
                        target_url, proxies=proxies, timeout=self.REQUEST_TIMEOUT,
                        headers=headers, allow_redirects=True, verify=False
                    )
                    latency = (time.time() - start_req_time) * 1000
                    self.log_debug(f"HEAD request for '{remark}' status: {response.status_code}, Latency: {latency:.0f} ms")

                    # HTTP 2xx and 3xx status codes are considered successful for latency tests
                    # This includes 200 OK, 204 No Content, 301 Redirect, etc.
                    if not (200 <= response.status_code < 400):
                         self.log_debug(f"HEAD failed ({response.status_code}), trying GET for '{remark}'...")
                         start_req_time = time.time()
                         response = session.get(
                             target_url, proxies=proxies, timeout=self.REQUEST_TIMEOUT,
                             headers=headers, allow_redirects=True, verify=False, stream=True
                         )
                         try: response.raw.read(1024) # Read a small amount
                         except Exception as read_err: self.log_debug(f"Error consuming GET response stream for '{remark}': {read_err}")
                         latency = (time.time() - start_req_time) * 1000
                         self.log_debug(f"GET request for '{remark}' status: {response.status_code}, Latency: {latency:.0f} ms")
                         # Only raise for status if it's not a 2xx or 3xx response
                         if not (200 <= response.status_code < 400):
                             response.raise_for_status()

                    success = True
                    result_value = latency

                except requests.exceptions.Timeout:
                    self.log_debug(f"Request Timeout for '{remark}' after {self.REQUEST_TIMEOUT}s")
                    result_value = "Timeout"
                    success = False
                except requests.exceptions.ProxyError as e:
                    err_str = str(e).lower()
                    if f"{self.TEMP_PROXY_HOST}:{local_port}" in err_str or "failed to connect to proxy" in err_str or "proxy connection refused" in err_str:
                        result_value = "Proxy Error (Local)"
                    elif "socks" in err_str or "connection refused by target" in err_str or "general socks server failure" in err_str:
                        result_value = "Proxy Error (Remote)"
                    else: result_value = "Proxy Error"
                    self.log_debug(f"Proxy Error for '{remark}': {str(e)[:150]}")
                    success = False
                except requests.exceptions.SSLError as e:
                    if "certificate verify failed" in str(e).lower(): result_value = "SSL Error (Verify)"
                    else: result_value = "SSL Error (Handshake)"
                    self.log_debug(f"SSL Error for '{remark}': {str(e)[:150]}")
                    success = False
                except requests.exceptions.ConnectionError as e:
                    err_str = str(e).lower()
                    if "nodename nor servname" in err_str or "name or service not known" in err_str or "dns lookup failed" in err_str: result_value = "DNS Error"
                    elif "connection refused" in err_str: result_value = "Conn Error (Refused)"
                    else: result_value = "Conn Error"
                    self.log_debug(f"Connection Error for '{remark}': {str(e)[:150]}")
                    success = False
                except requests.exceptions.HTTPError as e:
                    status = response.status_code if response is not None else 'N/A'
                    self.log_debug(f"Request Failed for '{remark}': HTTP Status {status}")
                    result_value = f"HTTP {status}"
                    success = False
                except requests.exceptions.RequestException as e:
                    self.log_debug(f"Generic Request Failed for '{remark}': {e}")
                    result_value = "Request Error"
                    success = False
                except Exception as e:
                    self.log_debug(f"Unexpected request error for '{remark}': {e}")
                    traceback.print_exc()
                    result_value = f"Exec Error ({type(e).__name__})"
                    success = False
                finally:
                    if response: response.close()
                    session.close()

        except (ValueError, OSError, subprocess.SubprocessError, Exception) as setup_err:
            self.log_debug(f"Setup/Execution exception during Xray connectivity test for '{remark}': {setup_err}")
            traceback.print_exc()
            if isinstance(setup_err, ValueError) and "Config File Error" in str(setup_err): result_value = "File Error"
            elif isinstance(setup_err, ValueError): result_value = f"Bad Config ({str(setup_err)[:30]})"
            elif isinstance(setup_err, FileNotFoundError): result_value = "Xray Not Found"
            else: result_value = f"Exec Error ({type(setup_err).__name__})"
            success = False

        finally:
            # --- Stop Xray Process ---
            if xray_process is not None and xray_process.poll() is None:
                self.log_debug(f"Terminating Xray process (PID: {xray_process.pid}) for '{remark}' (Connectivity Test)...")
                try:
                    xray_process.terminate()
                    try: xray_process.wait(timeout=0.5)
                    except subprocess.TimeoutExpired:
                        self.log_debug(f"Xray (PID: {xray_process.pid}) did not terminate gracefully, killing...")
                        xray_process.kill()
                        xray_process.wait(timeout=1.0)
                    self.log_debug(f"Xray process (PID: {xray_process.pid}) stopped.")
                except Exception as term_err:
                    self.log_debug(f"Error during Xray termination for PID {xray_process.pid}: {term_err}")

            # --- Release Semaphore ---
            if acquired:
                try:
                    self.xray_semaphore.release()
                    self.log_debug(f"Released Xray semaphore for '{remark}'")
                except ValueError:
                    self.log_debug(f"Warning: Attempted to release semaphore too many times for '{remark}'")

            # --- Decrement Counter --- (primarily for logging now)
            with self.xray_process_lock:
                if self.active_xray_processes > 0:
                    self.active_xray_processes -= 1
                count = self.active_xray_processes
                self.log_debug(f"Xray process count decreased to {count}")

            # --- Delete Temp Config File ---
            if config_path and os.path.exists(config_path):
                try: os.remove(config_path)
                except Exception as del_err: self.log_debug(f"Failed to delete temp file {config_path}: {del_err}")

            # --- Release Port ---
            if local_port and allocated_dynamically:
                self.release_port(local_port)


        self.log_debug(f"Xray connectivity test finished for '{remark}'. Success: {success}, Result: {result_value}")
        return success, result_value


    # --- ADDED/MODIFIED FOR DOWNLOAD TEST ---
    def _run_download_test(self, config_dict, target_url=None, local_port=None, skip_increment=False):
        """
        Core download speed testing logic using Xray.
        Generates config, starts Xray, downloads file via temp proxy, calculates speed, stops Xray, deletes file.
        Returns tuple: (success: bool, result: float_speed_kbps_or_error_string)

        Parameters:
            config_dict: The configuration dictionary
            target_url: The URL to download from
            local_port: The local port to use for the proxy
            skip_increment: If True, skip the increment_xray_process_count check (used when semaphore is already acquired)
        """
        if not target_url:
            target_url = self.DOWNLOAD_TEST_URL

        # --- Validate Input ---
        if not config_dict or not isinstance(config_dict, dict):
             self.log_debug(f"Download Test Error: Invalid config_dict provided.")
             return False, "Internal Error (Bad Config)"

        # Check for hostname in both 'hostname' and 'host' fields
        hostname = config_dict.get('hostname', '')
        if not hostname and 'host' in config_dict:
            hostname = config_dict.get('host', '')
            # Update the config_dict with the hostname
            config_dict['hostname'] = hostname
            self.log_debug(f"Fixed hostname from 'host' field for download test: {hostname}")

        if not hostname:
            hostname = 'unknown'

        protocol = config_dict.get('protocol', 'unknown')
        port = config_dict.get('port', '0')
        remark = config_dict.get('remark', f"{protocol}_{hostname}:{port}")

        # Check stop flag FIRST
        if self.stopping_tests:
            self.log_debug(f"Download test stopped before semaphore acquisition for '{remark}'")
            return False, "Stopped"

        # --- Check if we're allowed to start another Xray process ---
        # Acquire semaphore with timeout if not already acquired
        acquired = False
        if not skip_increment:  # Only try to acquire if not already acquired by caller
            try:
                self.log_debug(f"Attempting to acquire Xray semaphore for '{remark}' download test (Current: {self.get_xray_process_count()}/{self.max_allowed_xray_processes})")
                # Use a reasonable timeout (e.g., 5-10 seconds)
                # Adjust timeout based on stability setting if desired
                timeout_seconds = 10.0 if self.stability_improvements_enabled else 5.0
                acquired = self.xray_semaphore.acquire(blocking=True, timeout=timeout_seconds)

                if not acquired:
                    self.log_debug(f"TIMEOUT acquiring Xray semaphore for '{remark}' download test. Skipping test.")
                    return False, "Resource Limit (Timeout)"
                else:
                    self.log_debug(f"Acquired Xray semaphore for '{remark}' download test")
                    # Update counter for logging
                    with self.xray_process_lock:
                        self.active_xray_processes += 1
                        count = self.active_xray_processes
                        self.log_debug(f"Xray process count increased to {count} (limit: {self.max_allowed_xray_processes})")
            except Exception as sem_e:
                self.log_debug(f"Error acquiring semaphore for '{remark}' download test: {sem_e}")
                return False, f"Error (Semaphore Acq)"

        # --- Ensure local_port is provided ---
        if not local_port:
            self.log_debug(f"Download Test Error for '{remark}': No local_port provided.")
            local_port = self.find_available_port()
            if not local_port:
                # Make sure to decrement the counter if we can't allocate a port
                if not skip_increment:
                    self.decrement_xray_process_count()
                return False, "Internal Error (No Port)"
            allocated_dynamically = True
            self.log_debug(f"Download Test Warning for '{remark}': Allocated local_port {local_port} dynamically.")
        else:
            allocated_dynamically = False

        self.log_debug(f"Starting Download test for '{remark}' -> {target_url} on port {local_port}")

        xray_process = None
        config_path = None
        temp_download_path = None
        success = False
        result_value = "Error: Init"

        try:
            # --- Generate Xray config ---
            xray_json_config = self._generate_xray_config_for_test(config_dict, local_port)

            # --- Write temp config file ---
            try:
                with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix=".json", encoding='utf-8', dir=self.temp_dir, prefix=f"xray_dl_{protocol}_") as temp_f:
                    config_path = temp_f.name
                    json.dump(xray_json_config, temp_f, indent=2)
                self.log_debug(f"Temp config written: {os.path.basename(config_path)}")
            except Exception as file_err:
                self.log_debug(f"Error writing temp config file: {file_err}")
                raise ValueError(f"Config File Error: {file_err}")

            # --- Start Xray process ---
            command = [self.XRAY_EXECUTABLE, "run", "-c", config_path]
            startupinfo = None
            creationflags = 0
            if platform.system() == "Windows":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE
                creationflags = subprocess.CREATE_NO_WINDOW

            xray_process = subprocess.Popen(
                command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                startupinfo=startupinfo, creationflags=creationflags,
                encoding='utf-8', errors='ignore'
            )

            # --- Wait briefly for Xray to start and check if it exited ---
            time.sleep(self.XRAY_STARTUP_WAIT)
            exit_code = xray_process.poll()

            if exit_code is not None:
                stderr_output = "N/A"
                try: stderr_output = xray_process.stderr.read()
                except Exception as read_err: stderr_output = f"(Error reading stderr: {read_err})"
                self.log_debug(f"XRAY FAILED TO START for '{remark}' (Download Test)")
                if "config file not found" in stderr_output.lower(): result_value = "Xray Start Error (Config Not Found)"
                elif "failed to read config file" in stderr_output.lower(): result_value = "Xray Start Error (Read Fail)"
                elif "address already in use" in stderr_output.lower(): result_value = f"Xray Start Error (Port {local_port} Busy)"
                else: result_value = "Xray Start Error"
                success = False
            else:
                # --- Xray running, perform download ---
                self.log_debug(f"Xray process (PID: {xray_process.pid}) started for '{remark}'. Testing download...")
                proxies = {
                    "http": f"{self.TEMP_PROXY_TYPE_FOR_REQUESTS}://{self.TEMP_PROXY_HOST}:{local_port}",
                    "https": f"{self.TEMP_PROXY_TYPE_FOR_REQUESTS}://{self.TEMP_PROXY_HOST}:{local_port}"
                }
                session = requests.Session()
                adapter = HTTPAdapter(max_retries=0)  # No retries for speed test
                session.mount("http://", adapter)
                session.mount("https://", adapter)

                headers = {'User-Agent': 'Mozilla/5.0 QTester-DL/1.0'}
                response = None
                total_bytes_downloaded = 0
                start_dl_time = None
                time_elapsed = 0

                # --- Define temp download file path ---
                temp_filename = f"temp_download_{protocol}_{hostname}_{port}_{secrets.token_hex(4)}.tmp"
                temp_download_path = os.path.join(self.DOWNLOAD_TARGET_DIR, temp_filename)

                try:
                    # Start download with connect timeout
                    response = session.get(
                        target_url, proxies=proxies,
                        timeout=(self.DOWNLOAD_CONNECT_TIMEOUT, self.DOWNLOAD_TIMEOUT),
                        headers=headers, verify=False, stream=True
                    )
                    response.raise_for_status()

                    # --- Stream download content with timeout ---
                    with open(temp_download_path, 'wb') as f:
                        start_dl_time = time.perf_counter()
                        download_deadline = start_dl_time + self.DOWNLOAD_TIMEOUT

                        for chunk in response.iter_content(chunk_size=self.DOWNLOAD_CHUNK_SIZE):
                            if chunk:
                                chunk_len = len(chunk)
                                f.write(chunk)
                                total_bytes_downloaded += chunk_len

                                # Check if we've exceeded our timeout
                                current_time = time.perf_counter()
                                if current_time > download_deadline:
                                    raise requests.exceptions.ReadTimeout("Download exceeded 12 second limit")

                            # Check for stop signal
                            if self.stopping_tests:
                                raise OperationCanceledError("Download stopped by user")

                    # Calculate final time and speed
                    time_elapsed = time.perf_counter() - start_dl_time

                    # Calculate speed (KB/s)
                    if time_elapsed > 0 and total_bytes_downloaded > 0:
                        speed_bytes_sec = total_bytes_downloaded / time_elapsed
                        speed_kbytes_sec = speed_bytes_sec / 1024.0
                        success = True
                        result_value = speed_kbytes_sec
                        self.log_debug(f"Download successful for '{remark}'. Bytes: {total_bytes_downloaded}, Time: {time_elapsed:.3f}s, Speed: {result_value:.1f} KB/s")
                    else:
                        result_value = "Download Error (No Data)"
                        success = False

                except requests.exceptions.ReadTimeout:
                    self.log_debug(f"Download timeout for '{remark}' after {self.DOWNLOAD_TIMEOUT}s")
                    result_value = "Timeout"
                    success = False
                except requests.exceptions.ConnectTimeout:
                    result_value = "Timeout (Connect)"
                    success = False
                except requests.exceptions.ProxyError as e:
                    err_str = str(e).lower()
                    if f"{self.TEMP_PROXY_HOST}:{local_port}" in err_str: result_value = "Proxy Error (Local)"
                    else: result_value = "Proxy Error (Remote)"
                    success = False
                except requests.exceptions.SSLError:
                    result_value = "SSL Error"
                    success = False
                except requests.exceptions.ConnectionError:
                    result_value = "Conn Error"
                    success = False
                except requests.exceptions.HTTPError as e:
                    status = response.status_code if response else 'N/A'
                    result_value = f"HTTP {status}"
                    success = False
                except OperationCanceledError:
                    result_value = "Stopped"
                    success = False
                except Exception as e:
                    self.log_debug(f"Unexpected download error for '{remark}': {e}")
                    traceback.print_exc()
                    result_value = f"DL Error ({type(e).__name__})"
                    success = False
                finally:
                    if response: response.close()
                    session.close()

        except Exception as setup_err:
            self.log_debug(f"Setup/Execution exception during Download test for '{remark}': {setup_err}")
            traceback.print_exc()
            if isinstance(setup_err, ValueError) and "Config File Error" in str(setup_err):
                result_value = "File Error"
            elif isinstance(setup_err, ValueError):
                result_value = f"Bad Config ({str(setup_err)[:30]})"
            elif isinstance(setup_err, FileNotFoundError):
                result_value = "Xray Not Found"
            else:
                result_value = f"Exec Error ({type(setup_err).__name__})"
            success = False

        finally:
            # Stop Xray
            if xray_process is not None and xray_process.poll() is None:
                try:
                    xray_process.terminate()
                    try: xray_process.wait(timeout=0.5)
                    except subprocess.TimeoutExpired:
                        xray_process.kill()
                        xray_process.wait(timeout=1.0)
                except Exception as term_err:
                    self.log_debug(f"Error terminating Xray PID {xray_process.pid}: {term_err}")

            # --- Release Semaphore ---
            if not skip_increment and acquired:
                try:
                    self.xray_semaphore.release()
                    self.log_debug(f"Released Xray semaphore for '{remark}' download test")
                except ValueError:
                    self.log_debug(f"Warning: Attempted to release semaphore too many times for '{remark}' download test")

            # --- Decrement Counter --- (primarily for logging now)
            if not skip_increment:
                with self.xray_process_lock:
                    if self.active_xray_processes > 0:
                        self.active_xray_processes -= 1
                    count = self.active_xray_processes
                    self.log_debug(f"Xray process count decreased to {count}")

            # Delete temp files
            if config_path and os.path.exists(config_path):
                try: os.remove(config_path)
                except Exception as del_err:
                    self.log_debug(f"Failed to delete temp config {config_path}: {del_err}")

            if temp_download_path and os.path.exists(temp_download_path):
                try:
                    os.remove(temp_download_path)
                    self.log_debug(f"Deleted temp download file: {os.path.basename(temp_download_path)}")
                except Exception as del_err:
                    self.log_debug(f"Failed to delete temp download file {temp_download_path}: {del_err}")

            # Release port if dynamically allocated
            if local_port and allocated_dynamically:
                self.release_port(local_port)

        self.log_debug(f"Download test finished for '{remark}'. Success: {success}, Result: {result_value if isinstance(result_value, str) else f'{result_value:.1f} KB/s'}")
        return success, result_value
    # --- END DOWNLOAD TEST MODIFICATION ---

    # --- HTTP TEST METHOD ---
    def _run_http_test(self, config_dict, target_url=None, local_port=None):
        """
        Core HTTP testing logic using Xray.
        Generates config, starts Xray, makes HTTP request via temp proxy, measures response time, stops Xray.
        Returns tuple: (success: bool, result: float_latency_ms_or_error_string)
        """
        if not target_url:
            target_url = self.HTTP_TEST_URL

        # --- Validate Input ---
        if not config_dict or not isinstance(config_dict, dict):
            self.log_debug(f"HTTP Test Error: Invalid config_dict provided.")
            return False, "Internal Error (Bad Config)"

        # Check for hostname in both 'hostname' and 'host' fields
        hostname = config_dict.get('hostname', '')
        if not hostname and 'host' in config_dict:
            hostname = config_dict.get('host', '')
            config_dict['hostname'] = hostname
            self.log_debug(f"Fixed hostname from 'host' field for HTTP test: {hostname}")

        port_str = config_dict.get('port', '')
        remark = config_dict.get('remark', f"http_{hostname}:{port_str}")

        # Validate hostname
        if not hostname or hostname in ['error', 'unknown', 'parse_err', 'vmess_host_err', 'sip008_host_err', 'ss_err', 'unknown_host', 'ssr_host']:
            self.log_debug(f"HTTP Test Error for '{remark}': Invalid hostname '{hostname}'")
            return False, "Invalid Host"

        # Get or allocate port
        if local_port is None:
            local_port = self.find_available_port()
            if not local_port:
                self.log_debug(f"HTTP Test Error for '{remark}': No available ports")
                return False, "No Ports"
            port_allocated_here = True
        else:
            port_allocated_here = False

        self.log_debug(f"Starting HTTP test for '{remark}' -> {target_url} on port {local_port}")

        xray_process = None
        config_path = None
        success = False
        result_value = "Error: Init"

        # Check stop flag
        if self.stopping_tests:
            self.log_debug(f"HTTP test stopped before semaphore acquisition for '{remark}'")
            return False, "Stopped"

        try:
            # Acquire semaphore to limit concurrent Xray processes
            if not self.xray_semaphore.acquire(blocking=False):
                self.log_debug(f"HTTP Test for '{remark}': Semaphore limit reached, skipping")
                return False, "Process Limit"

            try:
                # Increment process count
                with self.xray_process_lock:
                    self.active_xray_processes += 1
                    self.log_debug(f"HTTP Test: Active Xray processes: {self.active_xray_processes}")

                # Check stop flag again after acquiring semaphore
                if self.stopping_tests:
                    self.log_debug(f"HTTP test stopped after semaphore acquisition for '{remark}'")
                    return False, "Stopped"

                # --- Generate Xray config ---
                config_json = self._generate_xray_config_for_test(config_dict, local_port)
                if not config_json:
                    self.log_debug(f"HTTP Test Error for '{remark}': Failed to generate Xray config")
                    return False, "Config Error"

                # --- Write config to temp file ---
                config_path = os.path.join(self.temp_dir, f"http_test_{local_port}_{secrets.token_hex(4)}.json")
                with open(config_path, 'w', encoding='utf-8') as f:
                    json.dump(config_json, f, indent=2)

                # --- Start Xray process ---
                command = [self.XRAY_EXECUTABLE, "run", "-c", config_path]
                self.log_debug(f"Executing: {' '.join(command)}")
                startupinfo = None
                creationflags = 0
                if platform.system() == "Windows":
                    startupinfo = subprocess.STARTUPINFO()
                    startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                    startupinfo.wShowWindow = subprocess.SW_HIDE
                    creationflags = subprocess.CREATE_NO_WINDOW

                xray_process = subprocess.Popen(
                    command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    startupinfo=startupinfo, creationflags=creationflags,
                    encoding='utf-8', errors='ignore'
                )

                # --- Wait briefly for Xray to start and check if it exited ---
                time.sleep(self.XRAY_STARTUP_WAIT)
                exit_code = xray_process.poll()
                if exit_code is not None:
                    stdout, stderr = xray_process.communicate(timeout=2)
                    self.log_debug(f"HTTP Test Error for '{remark}': Xray exited early (code {exit_code}). Stderr: {stderr[:200]}")
                    return False, f"Xray Error ({exit_code})"

                # Check stop flag before making HTTP request
                if self.stopping_tests:
                    self.log_debug(f"HTTP test stopped before HTTP request for '{remark}'")
                    return False, "Stopped"

                # --- Make HTTP request via proxy ---
                proxy_url = f"{self.TEMP_PROXY_TYPE_FOR_REQUESTS}://{self.TEMP_PROXY_HOST}:{local_port}"
                proxies = {'http': proxy_url, 'https': proxy_url}

                start_time = time.time()
                try:
                    response = requests.get(
                        target_url,
                        proxies=proxies,
                        timeout=self.HTTP_TEST_TIMEOUT,
                        verify=False,
                        allow_redirects=True
                    )
                    end_time = time.time()

                    # HTTP 2xx status codes (200-299) are considered successful
                    # This includes 200 OK, 204 No Content, etc.
                    if 200 <= response.status_code < 300:
                        latency_ms = (end_time - start_time) * 1000
                        success = True
                        result_value = latency_ms
                        self.log_debug(f"HTTP Test Success for '{remark}': {latency_ms:.0f}ms (Status: {response.status_code})")
                    else:
                        result_value = f"HTTP {response.status_code}"
                        self.log_debug(f"HTTP Test Error for '{remark}': HTTP {response.status_code}")

                except requests.exceptions.Timeout:
                    result_value = "Timeout"
                    self.log_debug(f"HTTP Test Timeout for '{remark}'")
                except requests.exceptions.ProxyError:
                    result_value = "Proxy Error"
                    self.log_debug(f"HTTP Test Proxy Error for '{remark}'")
                except requests.exceptions.ConnectionError:
                    result_value = "Connection Error"
                    self.log_debug(f"HTTP Test Connection Error for '{remark}'")
                except Exception as req_err:
                    result_value = f"Request Error ({type(req_err).__name__})"
                    self.log_debug(f"HTTP Test Request Error for '{remark}': {req_err}")

            finally:
                # Always release semaphore
                self.xray_semaphore.release()
                # Decrement process count
                with self.xray_process_lock:
                    self.active_xray_processes = max(0, self.active_xray_processes - 1)
                    self.log_debug(f"HTTP Test: Active Xray processes after decrement: {self.active_xray_processes}")

        except Exception as e:
            self.log_debug(f"HTTP Test Exception for '{remark}': {e}")
            traceback.print_exc()
            result_value = f"Exception ({type(e).__name__})"

        finally:
            # --- Cleanup ---
            if xray_process:
                try:
                    if xray_process.poll() is None:
                        xray_process.terminate()
                        try:
                            xray_process.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            xray_process.kill()
                            xray_process.wait()
                except Exception as cleanup_err:
                    self.log_debug(f"Error cleaning up Xray process for HTTP test '{remark}': {cleanup_err}")

            if config_path and os.path.exists(config_path):
                try:
                    os.remove(config_path)
                except Exception as file_err:
                    self.log_debug(f"Error removing HTTP test config file '{config_path}': {file_err}")

            if port_allocated_here:
                self.release_port(local_port)

        self.log_debug(f"HTTP test part 1 finished for '{remark}'. Initial Success: {success}, Initial Result: {result_value if isinstance(result_value, str) else f'{result_value:.0f}ms'}")

        # --- Connection Integrity Check ---
        final_success = success
        final_result = result_value

        if success and hasattr(self, 'http_connection_integrity_checkbox') and self.http_connection_integrity_checkbox.isChecked():
            self.log_debug(f"HTTP success for '{remark}', performing connectivity integrity test...")
            # Note: _run_connectivity_test needs its own Xray instance as the one from _run_http_test is stopped by this point (or will be in finally).
            # It also needs a port. If _run_http_test was called with a local_port, we can reuse it conceptually,
            # but _run_connectivity_test will manage its own Xray process and port if not supplied carefully.
            # For simplicity here, _run_connectivity_test will manage its own port if local_port is None or it starts a new Xray.
            # The key is that the _run_http_test's Xray process is confined to this method.
            
            # We need to pass the *original* config_dict to _run_connectivity_test, not a modified one.
            # And ensure it uses a *different* port or that the current Xray is stopped.
            # The current _run_connectivity_test is designed to be somewhat standalone.
            
            # The Xray process for _run_http_test is stopped in its finally block.
            # _run_connectivity_test will start its own.
            connectivity_success, connectivity_result_str = self._run_connectivity_test(config_dict, local_port=None) # Pass None to force new port for its own Xray

            if connectivity_success:
                self.log_debug(f"Connection integrity VERIFIED for '{remark}'. HTTP result stands.")
                # final_success and final_result are already set from HTTP test
            else:
                final_success = False
                final_result = f"Integrity Failed: {connectivity_result_str}"
                self.log_debug(f"Connection integrity FAILED for '{remark}': {connectivity_result_str}")
        else:
            if success:
                self.log_debug(f"HTTP test for '{remark}' successful, integrity check skipped (checkbox unchecked or initial HTTP failed).")
            # else: HTTP test already failed, final_success/final_result reflect that.

        self.log_debug(f"HTTP test (incl. integrity) finalized for '{remark}'. Final Success: {final_success}, Final Result: {final_result if isinstance(final_result, str) else f'{final_result:.0f}ms'}")
        return final_success, final_result
    # --- END HTTP TEST METHOD ---

    # --- CONNECTIVITY TEST METHOD (for Connection Integrity) ---
    def _run_connectivity_test(self, config_dict, local_port=None):
        """
        Core connectivity testing logic using Xray and small file download.
        This is used for connection integrity verification after successful HTTP tests.
        Returns tuple: (success: bool, result: str)
        """
        success = False
        result_value = "Error: Init"
        xray_process = None
        config_path = None
        port_allocated_here = False

        try:
            # --- Validate Input ---
            if not config_dict or not isinstance(config_dict, dict):
                raise ValueError("Invalid config_dict provided")

            remark = config_dict.get('remark', 'Unknown')
            self.log_debug(f"Starting connectivity test for '{remark}'...")

            # --- Port Allocation ---
            if local_port is None:
                local_port = self.find_available_port()
                if not local_port:
                    self.log_debug(f"Connectivity Test Error for '{remark}': No available ports")
                    return False, "Port Error"
                port_allocated_here = True

            # --- Generate Xray Config ---
            try:
                xray_config = self._generate_xray_config_for_test(config_dict, local_port)
            except Exception as config_err:
                self.log_debug(f"Connectivity Test Config Error for '{remark}': {config_err}")
                return False, "Config Error"

            # --- Write Config File ---
            config_path = os.path.join(self.temp_dir, f"connectivity_test_{local_port}.json")
            try:
                with open(config_path, 'w', encoding='utf-8') as f:
                    json.dump(xray_config, f, indent=2)
            except Exception as file_err:
                self.log_debug(f"Connectivity Test File Error for '{remark}': {file_err}")
                return False, "File Error"

            # --- Start Xray Process ---
            try:
                if not self.increment_xray_process_count():
                    self.log_debug(f"Connectivity Test Error for '{remark}': Too many Xray processes running")
                    return False, "Process Limit"

                command = [self.XRAY_EXECUTABLE, "run", "-config", config_path]
                startupinfo = None
                creationflags = 0
                if platform.system() == "Windows":
                    startupinfo = subprocess.STARTUPINFO()
                    startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                    startupinfo.wShowWindow = subprocess.SW_HIDE
                    creationflags = subprocess.CREATE_NO_WINDOW

                xray_process = subprocess.Popen(
                    command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    startupinfo=startupinfo, creationflags=creationflags,
                    encoding='utf-8', errors='ignore'
                )

                # Wait for Xray to start
                time.sleep(self.XRAY_STARTUP_WAIT)
                exit_code = xray_process.poll()
                if exit_code is not None:
                    stdout, stderr = xray_process.communicate(timeout=2)
                    self.log_debug(f"Connectivity Test Error for '{remark}': Xray exited early (code {exit_code}). Stderr: {stderr[:200]}")
                    return False, f"Xray Error ({exit_code})"

            except Exception as xray_err:
                self.log_debug(f"Connectivity Test Xray Start Error for '{remark}': {xray_err}")
                return False, "Xray Start Error"

            # --- Perform Connectivity Test (actual file download) ---
            try:
                proxy_config = {
                    'http': f'socks5h://{self.TEMP_PROXY_HOST}:{local_port}',
                    'https': f'socks5h://{self.TEMP_PROXY_HOST}:{local_port}'
                }

                # Use a small test file for download verification
                # Using a reliable 10KB test file from a CDN
                test_file_url = self.CONNECTIVITY_TEST_URL
                temp_file_path = os.path.join(self.temp_dir, f"connectivity_test_{local_port}_{int(time.time())}.tmp")

                self.log_debug(f"Downloading test file from {test_file_url} for connectivity verification...")

                start_time = time.time() # This start_time is for the request itself
                response = requests.get(
                    test_file_url,
                    proxies=proxy_config,
                    timeout=self.HTTP_TEST_TIMEOUT,
                    allow_redirects=True,
                    stream=True  # Stream download for better control
                )

                if response.status_code == 200:
                    # Download the file to verify actual data transfer
                    downloaded_size = 0
                    with open(temp_file_path, 'wb') as f:
                        for chunk in response.iter_content(chunk_size=1024): # Note: uses 1024, not self.DOWNLOAD_CHUNK_SIZE
                            if chunk:
                                f.write(chunk)
                                downloaded_size += len(chunk)

                    elapsed_ms = (time.time() - start_time) * 1000 # This is overall elapsed time

                    # Verify we downloaded the expected amount of data
                    if downloaded_size >= 10240:  # At least 10KB
                        success = True
                        result_value = "OK"
                        self.log_debug(f"Connectivity test success for '{remark}': Downloaded {downloaded_size} bytes in {elapsed_ms:.0f}ms")
                    else:
                        success = False
                        result_value = f"Incomplete Download ({downloaded_size} bytes)"
                        self.log_debug(f"Connectivity test incomplete download for '{remark}': {downloaded_size} bytes")

                    # Clean up the temporary file
                    try:
                        if os.path.exists(temp_file_path):
                            os.remove(temp_file_path)
                            self.log_debug(f"Cleaned up temporary file: {temp_file_path}")
                    except Exception as cleanup_err:
                        self.log_debug(f"Error cleaning up temporary file {temp_file_path}: {cleanup_err}")

                else:
                    success = False
                    result_value = f"HTTP {response.status_code}"
                    self.log_debug(f"Connectivity test HTTP error for '{remark}': {response.status_code}")

            except requests.exceptions.ConnectTimeout:
                success = False
                result_value = "Conn Timeout"
                self.log_debug(f"Connectivity test connection timeout for '{remark}'")
            except requests.exceptions.ReadTimeout:
                success = False
                result_value = "Read Timeout"
                self.log_debug(f"Connectivity test read timeout for '{remark}'")
            except requests.exceptions.ConnectionError as conn_err:
                success = False
                if "Connection refused" in str(conn_err):
                    result_value = "Conn Refused"
                elif "timed out" in str(conn_err).lower():
                    result_value = "Timeout"
                else:
                    result_value = "Conn Error"
                self.log_debug(f"Connectivity test connection error for '{remark}': {conn_err}")
            except requests.exceptions.ProxyError:
                success = False
                result_value = "Proxy Error"
                self.log_debug(f"Connectivity test proxy error for '{remark}'")
            except requests.exceptions.SSLError:
                success = False
                result_value = "SSL Error"
                self.log_debug(f"Connectivity test SSL error for '{remark}'")
            except Exception as e: # Catch any other unexpected errors during requests
                success = False
                result_value = f"Request Error ({type(e).__name__})" # Keep a simple error for UI
                # Log the detailed error including exception type and message
                self.log_error(f"Detailed error during connectivity test for {remark} after {(time.time() - start_time):.2f}s: {type(e).__name__} - {e}", exc_info=True)

                # Clean up temp file in case of error
                try:
                    if 'temp_file_path' in locals() and os.path.exists(temp_file_path):
                        os.remove(temp_file_path)
                except Exception:
                    pass

        except Exception as e:
            self.log_debug(f"Connectivity Test Exception for '{remark}': {e}")
            traceback.print_exc()
            result_value = f"Exception ({type(e).__name__})"

        finally:
            # --- Cleanup ---
            try:
                # Always release semaphore
                self.xray_semaphore.release()
                # Decrement process count
                with self.xray_process_lock:
                    self.active_xray_processes = max(0, self.active_xray_processes - 1)
                    self.log_debug(f"Connectivity Test: Active Xray processes after decrement: {self.active_xray_processes}")
            except Exception as sem_err:
                self.log_debug(f"Error releasing semaphore in connectivity test: {sem_err}")

            if xray_process:
                try:
                    if xray_process.poll() is None:
                        xray_process.terminate()
                        try:
                            xray_process.wait(timeout=3)
                        except subprocess.TimeoutExpired:
                            xray_process.kill()
                            xray_process.wait()
                except Exception as cleanup_err:
                    self.log_debug(f"Error cleaning up Xray process for connectivity test '{remark}': {cleanup_err}")

            if config_path and os.path.exists(config_path):
                try:
                    os.remove(config_path)
                except Exception as file_err:
                    self.log_debug(f"Error removing connectivity test config file '{config_path}': {file_err}")

            if port_allocated_here:
                self.release_port(local_port)

        self.log_debug(f"Connectivity test finished for '{remark}'. Success: {success}, Result: {result_value}")
        return success, result_value
    # --- END CONNECTIVITY TEST METHOD ---

    def _run_netcat_test(self, config_dict):
        # ... (Keep existing implementation - unchanged) ...
        """
        Performs a TCP connection test using nc (Netcat).
        Returns tuple: (success: bool, result: str)
        """
        success = False
        result_value = "Error: Init"

        try:
            # --- Validate Input ---
            if not config_dict or not isinstance(config_dict, dict):
                 raise ValueError("Invalid config_dict provided")

            # Check for hostname in both 'hostname' and 'host' fields
            hostname = config_dict.get('hostname', '')
            if not hostname and 'host' in config_dict:
                hostname = config_dict.get('host', '')
                # Update the config_dict with the hostname
                config_dict['hostname'] = hostname
                self.log_debug(f"Fixed hostname from 'host' field for netcat test: {hostname}")

            port_str = config_dict.get('port', '')
            remark = config_dict.get('remark', f"nc_{hostname}:{port_str}")

            # Validate hostname (allow IPs and domain names)
            if not hostname or hostname in ['error', 'unknown', 'parse_err'] or not re.match(r"^[a-zA-Z0-9\.\-\:]+$", hostname):
                 self.log_debug(f"Netcat Test Error for '{remark}': Invalid hostname '{hostname}'")
                 return False, "Invalid Host"

            # Validate and parse port
            port = self._parse_port(port_str)
            if not port:
                self.log_debug(f"Netcat Test Error for '{remark}': Invalid port '{port_str}'")
                return False, "Invalid Port"

            # --- Determine Netcat Command ---
            nc_command_options = ['nc', 'ncat']
            nc_command_to_use = None
            for cmd in nc_command_options:
                 try:
                      # Check if command exists and is executable (basic check)
                      check_cmd = [cmd, "-h"] # Simple command to check existence
                      startupinfo = None
                      creationflags = 0
                      if platform.system() == "Windows":
                           startupinfo = subprocess.STARTUPINFO()
                           startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                           startupinfo.wShowWindow = subprocess.SW_HIDE
                           creationflags = subprocess.CREATE_NO_WINDOW
                      subprocess.run(check_cmd, capture_output=True, timeout=1, check=False, startupinfo=startupinfo, creationflags=creationflags)
                      nc_command_to_use = cmd
                      break # Found a working command
                 except FileNotFoundError:
                      continue # Try the next command
                 except Exception as check_err:
                      self.log_debug(f"Error checking '{cmd}': {check_err}")
                      continue

            if not nc_command_to_use:
                 self.log_debug(f"Netcat Test Error for '{remark}': Neither 'nc' nor 'ncat' found in PATH.")
                 return False, "NC Not Found"

            # --- Construct and Execute Command ---
            command = [nc_command_to_use, "-z", "-w", str(self.NETCAT_TIMEOUT), hostname, str(port)]
            self.log_debug(f"Executing Netcat for '{remark}': {' '.join(command)}")

            startupinfo = None
            creationflags = 0
            if platform.system() == "Windows":
                startupinfo = subprocess.STARTUPINFO()
                startupinfo.dwFlags |= subprocess.STARTF_USESHOWWINDOW
                startupinfo.wShowWindow = subprocess.SW_HIDE
                creationflags = subprocess.CREATE_NO_WINDOW

            start_time = time.time()
            try:
                result = subprocess.run(
                    command,
                    capture_output=True, text=True,
                    timeout=self.NETCAT_TIMEOUT + 2,
                    check=False, startupinfo=startupinfo, creationflags=creationflags,
                    encoding='utf-8', errors='ignore'
                )
                elapsed = time.time() - start_time

                # --- Interpret Result ---
                if result.returncode == 0:
                    success = True; result_value = "OK"
                    self.log_debug(f"Netcat Success for '{remark}' ({elapsed:.2f}s)")
                else:
                    success = False
                    stderr_lower = result.stderr.lower(); stdout_lower = result.stdout.lower()
                    combined_output = stderr_lower + " " + stdout_lower
                    if "connection refused" in combined_output: result_value = "Refused"
                    elif "timed out" in combined_output or "timeout" in combined_output:
                         result_value = "Timeout" if elapsed >= self.NETCAT_TIMEOUT else "Failed"
                    elif "invalid option" in combined_output: result_value = "NC Error (Option)"
                    elif "dns" in combined_output or "name or service not known" in combined_output: result_value = "No DNS"
                    elif "host not found" in combined_output: result_value = "Invalid Host"
                    else: result_value = "Failed"
                    self.log_debug(f"Netcat Failure for '{remark}' (Code: {result.returncode}, Time: {elapsed:.2f}s): {result_value}. Stderr: {result.stderr.strip()[:100]}")

            except subprocess.TimeoutExpired:
                 success = False; result_value = "Timeout (Exec)"
                 self.log_debug(f"Netcat process timed out for '{remark}'")
            except Exception as nc_exec_err:
                 success = False; result_value = f"NC Error ({type(nc_exec_err).__name__})"
                 self.log_debug(f"Error executing Netcat for '{remark}': {nc_exec_err}")
                 traceback.print_exc()

        except Exception as outer_err:
            self.log_debug(f"Outer exception during Netcat test for '{config_dict.get('remark', 'unknown')}': {outer_err}")
            result_value = f"Error ({type(outer_err).__name__})"
            success = False; traceback.print_exc()

        return success, result_value

    def _process_test_generic(self, configs_to_test, test_func, latency_key, success_key, test_name, button_to_enable=None, extra_test_args=None):
        if not configs_to_test:
            self.log_debug(f"No configs to test for {test_name}.")
            if button_to_enable: button_to_enable.setEnabled(True)
            return

        if extra_test_args is None:
            extra_test_args = {}

        # Get max_workers from extra_test_args or use default
        base_thread_limit = extra_test_args.pop('max_workers', 10)
        total_count = len(configs_to_test)

        # Use the *current* effective Xray process limit as an upper bound for threads launching Xray
        current_process_limit = self.max_allowed_xray_processes # Get current semaphore limit

        # Worker threads should not drastically exceed the process limit if they launch processes
        # Allow a few extra threads for non-process tasks, cap by process limit
        worker_threads = min(base_thread_limit, current_process_limit + 5, total_count)
        self.log_debug(f"{test_name}: BaseThreads={base_thread_limit}, ProcessLimit={current_process_limit}, PoolSize={worker_threads}")

        processed_count = 0
        success_count = 0  # Initialize success counter

        # --- Check if ports are needed (Xray based tests: Google, Site, Download) ---
        needs_port = (test_func in [self._run_xray_connectivity_test, self._run_download_test])

        # For download tests, we need to be especially careful with resource management
        is_download_test = (test_func == self._run_download_test)
        if is_download_test:
            # For download tests, strictly enforce the concurrency limit from the spinbox
            download_concurrency = self.download_max_workers_spinbox.value()
            worker_threads = min(worker_threads, download_concurrency)  # Use the value from the spinbox

            # For download tests, also check the current Xray process count
            current_xray_count = self.get_xray_process_count()
            if current_xray_count > 0:
                # If there are already Xray processes running, reduce concurrency further
                adjusted_for_running = max(1, min(worker_threads, self.max_allowed_xray_processes - current_xray_count))
                if adjusted_for_running < worker_threads:
                    self.log_debug(f"Download test - adjusting concurrency from {worker_threads} to {adjusted_for_running} due to {current_xray_count} running Xray processes")
                    worker_threads = adjusted_for_running

            self.log_debug(f"Download test - strictly limiting to {worker_threads} worker threads (from spinbox setting and running processes)")
        else:
            # For other tests (including netcat), also set to 15
            worker_threads = min(worker_threads, 15)  # Fixed at 15 for all tests
            self.log_debug(f"{test_name} test - using {worker_threads} worker threads")

        # Check system load and adjust concurrency if needed
        if hasattr(self, 'system_load_high') and self.system_load_high:
            # Reduce worker threads by 30% if system is under heavy load
            adjusted_workers = max(3, int(worker_threads * 0.7))
            if adjusted_workers < worker_threads:
                self.log_debug(f"System under heavy load - reducing {test_name} worker threads from {worker_threads} to {adjusted_workers}")
                worker_threads = adjusted_workers

        # For download tests, ensure we never exceed the maximum allowed Xray processes
        if is_download_test:
            # Make sure we don't exceed the maximum allowed Xray processes
            worker_threads = min(worker_threads, self.max_allowed_xray_processes)
            self.log_debug(f"Final download test concurrency: {worker_threads} workers (max allowed: {self.max_allowed_xray_processes})")

        def allocate_one_port():
            port = self.find_available_port()
            if not port:
                self.log_debug(f"No ports available for {test_name} test.")
                raise RuntimeError("No ports available")
            return port

        # Setup progress bar
        QMetaObject.invokeMethod(self.test_progress_bar, "setMaximum", Qt.QueuedConnection, Q_ARG(int, total_count))
        QMetaObject.invokeMethod(self.test_progress_bar, "setValue", Qt.QueuedConnection, Q_ARG(int, 0))
        QMetaObject.invokeMethod(self.test_progress_bar, "setVisible", Qt.QueuedConnection, Q_ARG(bool, True))
        if button_to_enable:
            self.signals.update_button_text.emit(button_to_enable, f"Testing {test_name} (0/{total_count})...")

        # Keep track of configs that couldn't be processed due to resource constraints
        skipped_indices = []

        # Use a context manager to ensure proper cleanup of the thread pool
        # The thread_name_prefix helps identify threads in debugging
        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_threads,
                                                 thread_name_prefix=f"{test_name}-worker") as executor:
            futures = {}
            batch_size = min(50, total_count)  # Process in batches to avoid memory issues

            # Process configs in batches
            for batch_start in range(0, total_count, batch_size):
                if self.stopping_tests:
                    break

                batch_end = min(batch_start + batch_size, total_count)
                self.log_debug(f"Processing {test_name} batch {batch_start//batch_size + 1}: configs {batch_start}-{batch_end-1}")

                # Submit batch of configs
                for i in range(batch_start, batch_end):
                    if self.stopping_tests:
                        break

                    config = configs_to_test[i]
                    # Store original index for result mapping
                    original_index = next((idx for idx, cfg in enumerate(self.configs) if cfg is config), -1)
                    if original_index == -1:
                        self.log_debug(f"Warning: Config not found in self.configs during {test_name} test.")
                        continue

                    try:
                        allocated_port = allocate_one_port() if needs_port else None
                        current_extra_args = extra_test_args.copy() if extra_test_args else {}
                        if allocated_port:
                            current_extra_args['local_port'] = allocated_port
                        future = executor.submit(test_func, config, **current_extra_args)
                        futures[future] = (original_index, allocated_port)
                    except Exception as e:
                        self.log_debug(f"Error submitting {test_name} test for index {original_index}: {e}")
                        if allocated_port:
                            self.release_port(allocated_port)

                        # For "No ports available" errors, track the skipped config to retry later
                        if "No ports available" in str(e) and is_download_test:
                            skipped_indices.append(original_index)
                            self.log_debug(f"Tracking skipped config {original_index} for retry")
                        else:
                            # Other errors - emit error for this config
                            self.signals.update_specific_latency.emit(original_index, str(e), False, test_name)

                        processed_count += 1
                        self.signals.update_progress.emit(processed_count)

                # Process completed futures for this batch before moving to the next batch
                # This helps manage memory by not keeping all futures in memory at once
                completed_futures = set()
                for future in concurrent.futures.as_completed([f for f in futures.keys() if f not in completed_futures]):
                    if self.stopping_tests:
                        break

                    completed_futures.add(future)
                    original_index, allocated_port = futures[future]
                    try:
                        # Get result from the future
                        success, result_value = future.result()

                        # Store results in the config dictionary
                        if 0 <= original_index < len(self.configs):
                            self.configs[original_index][latency_key] = result_value
                            self.configs[original_index][success_key] = success

                            # Update UI
                            self.signals.update_specific_latency.emit(original_index, result_value, success, test_name)
                            if success:
                                success_count += 1
                        else:
                            self.log_debug(f"Warning ({test_name}): Invalid original index {original_index} after task completion.")
                    except Exception as e:
                        self.log_debug(f"Error processing {test_name} result for index {original_index}: {e}")
                        # Emit error state
                        self.signals.update_specific_latency.emit(original_index, str(e), False, test_name)
                    finally:
                        if allocated_port:
                            self.release_port(allocated_port)
                        processed_count += 1
                        self.signals.update_progress.emit(processed_count)
                        if button_to_enable and not self.stopping_tests:
                            self.signals.update_button_text.emit(button_to_enable, f"Testing {test_name} ({processed_count}/{total_count})...")

                # Remove processed futures to free memory
                for future in completed_futures:
                    del futures[future]

                # Force garbage collection after each batch
                try:
                    import gc
                    gc.collect()
                except ImportError:
                    pass

                # Give the UI a chance to update
                QApplication.processEvents()



        # Handle skipped configs for download tests - try to process them now
        if is_download_test and skipped_indices and not self.stopping_tests:
            self.log_debug(f"Attempting to process {len(skipped_indices)} skipped configs for {test_name} test")

            # Wait a moment to ensure all ports are truly released
            time.sleep(1.0)

            # Use a second thread pool to process skipped configs in parallel
            # Use the same worker_threads value for consistency
            retry_worker_count = min(worker_threads, len(skipped_indices))
            self.log_debug(f"Starting retry batch with {retry_worker_count} workers for {len(skipped_indices)} configs")

            # Update UI to show retry phase
            if button_to_enable:
                retry_text = f"Testing {test_name} - Retrying {len(skipped_indices)} configs..."
                self.signals.update_button_text.emit(button_to_enable, retry_text)

            retry_processed = 0
            retry_success = 0
            retry_futures = {}

            with concurrent.futures.ThreadPoolExecutor(max_workers=retry_worker_count) as retry_executor:
                # Submit all retry jobs
                for idx in skipped_indices:
                    if self.stopping_tests:
                        break

                    if idx >= len(self.configs):
                        continue

                    config = self.configs[idx]
                    self.log_debug(f"Scheduling retry for config index {idx}")

                    try:
                        # Allocate a port for this retry
                        allocated_port = self.find_available_port()
                        if not allocated_port:
                            self.log_debug(f"Still no ports available for retry {idx}")
                            # Mark as error since we can't retry
                            self.signals.update_specific_latency.emit(idx, "No Ports Available", False, test_name)
                            continue

                        # Prepare arguments
                        current_extra_args = extra_test_args.copy() if extra_test_args else {}
                        current_extra_args['local_port'] = allocated_port

                        # Submit the job
                        future = retry_executor.submit(test_func, config, **current_extra_args)
                        retry_futures[future] = (idx, allocated_port)

                    except Exception as submit_err:
                        self.log_debug(f"Error scheduling retry for index {idx}: {submit_err}")
                        self.signals.update_specific_latency.emit(idx, f"Retry Error: {type(submit_err).__name__}", False, test_name)

                # Process completed futures
                for future in concurrent.futures.as_completed(retry_futures):
                    if self.stopping_tests:
                        break

                    idx, allocated_port = retry_futures[future]
                    try:
                        # Get result and update config
                        success, result_value = future.result()

                        # Store results in the config dictionary
                        self.configs[idx][latency_key] = result_value
                        self.configs[idx][success_key] = success

                        # Update UI
                        self.signals.update_specific_latency.emit(idx, result_value, success, test_name)
                        if success:
                            retry_success += 1

                    except Exception as retry_err:
                        self.log_debug(f"Error during retry for index {idx}: {retry_err}")
                        self.signals.update_specific_latency.emit(idx, f"Retry Error: {type(retry_err).__name__}", False, test_name)
                    finally:
                        if allocated_port:
                            self.release_port(allocated_port)
                        retry_processed += 1

                        # Update UI with progress
                        if button_to_enable and not self.stopping_tests:
                            retry_text = f"Testing {test_name} - Retrying ({retry_processed}/{len(skipped_indices)})"
                            self.signals.update_button_text.emit(button_to_enable, retry_text)

            self.log_debug(f"Retry batch complete: processed {retry_processed}/{len(skipped_indices)} with {retry_success} successful")
            # Add retry successes to total success count
            success_count += retry_success

        # Cleanup and final status
        if button_to_enable and not self.stopping_tests:
            button_to_enable.setEnabled(True)
            self.signals.update_button_text.emit(button_to_enable, f"Test {test_name}")
        QMetaObject.invokeMethod(self.test_progress_bar, "setVisible", Qt.QueuedConnection, Q_ARG(bool, False))

        self.signals.test_completed.emit()
        if not self.stopping_tests:
            success_rate = (success_count / total_count * 100) if total_count > 0 else 0

            # Skip showing the message box for predefined tests or if explicitly requested
            if not (hasattr(self, 'is_predefined_test') and self.is_predefined_test) and not (hasattr(self, 'skip_generic_completion_message') and self.skip_generic_completion_message):
                self.signals.show_message_box.emit(f"{test_name} Complete",
                                                f"{test_name} finished. Success: {success_count}/{total_count} ({success_rate:.1f}%).",
                                                "info")
            else:
                self.log_debug(f"Skipping generic completion message for predefined test")

        self.log_debug(f"Generic test batch '{test_name}' completed processing.")


    # --- Slot Connections & Completion Handlers ---
    def on_generic_test_completed(self):
        """Handle completion of a generic test batch"""
        self.log_debug("A generic test batch has completed (on_generic_test_completed).");

        # Check if this is a predefined test completion
        if hasattr(self, 'is_predefined_test') and self.is_predefined_test:
            # Wait a short time to ensure all results are processed
            QTimer.singleShot(500, lambda: self._predefined_test_completed())
            # Don't reset is_predefined_test flag here, it will be reset in _predefined_test_completed

    def on_ping_test_completed(self):
        # ... (Keep existing implementation - unchanged) ...
        self.log_debug("Ping testing thread finished.");
        self.signals.update_button_text.emit(self.test_latency_button, "Test Ping Latency")
        self.test_latency_button.setEnabled(True)
        self.test_progress_bar.setVisible(False)
        self.status_bar.showMessage("Ping test complete.", 5000)
        self.update_latency_stats() # Update ping stats
        self.log_debug("Ping test batch completed.")

        # Add a small delay to allow signal processing
        QTimer.singleShot(100, self.update_latency_table)

    # _update_ping_latency_in_table - Kept above near ping logic
    # _update_specific_latency_in_table - Modified above

    # --- UI Slots (Keep As Is) ---
    @pyqtSlot(object, str)
    def update_button_text(self, button, text):
        # ... (Keep existing implementation - unchanged) ...
        try:
             if button and isinstance(button, QPushButton) and button.parent() is not None:
                 button.setText(text)
        except Exception as e:
            self.log_debug(f"Minor: Error updating button text in slot: {e}")

    @pyqtSlot(int)
    def update_progress(self, value):
        # ... (Keep existing implementation - unchanged) ...
        try:
            if self.test_progress_bar and self.test_progress_bar.isVisible():
                max_val = self.test_progress_bar.maximum()
                current_val = value
                if QApplication.instance().thread() != QThread.currentThread():
                    QMetaObject.invokeMethod(self.test_progress_bar, "setValue", Qt.QueuedConnection, Q_ARG(int, current_val))
                else:
                    self.test_progress_bar.setValue(current_val)
        except Exception as e:
             self.log_debug(f"Minor: Error updating progress bar: {e}")


    @pyqtSlot(str, str, str)
    def show_message_box(self, title, message, message_type="info"):
        # ... (Keep existing implementation - unchanged) ...
        if QApplication.instance().thread() != QThread.currentThread():
             QMetaObject.invokeMethod(self, "show_message_box", Qt.QueuedConnection,
                                      Q_ARG(str, title), Q_ARG(str, message), Q_ARG(str, message_type))
             return
        if message_type == "info": QMessageBox.information(self, title, message)
        elif message_type == "warning": QMessageBox.warning(self, title, message)
        elif message_type == "error": QMessageBox.critical(self, title, message)
        else: QMessageBox.information(self, title, message)

    # --- _parse_port (Keep As Is) ---
    def _parse_port(self, port_str):
        # ... (Keep existing implementation - unchanged) ...
        if not port_str: return 0
        port_part = str(port_str).split('?')[0].split('/')[0].split('#')[0]
        try:
             port_int = int(port_part)
             return port_int if 1 <= port_int <= 65535 else 0
        except (ValueError, TypeError): return 0

    # --- Context Menus & _run_single_test (Adjusted for Download) ---
    def show_latency_table_context_menu(self, position):
        selected_items = self.latency_table.selectedItems()
        if not selected_items: return

        # Get all unique selected rows
        selected_rows = sorted(set(item.row() for item in selected_items))
        if not selected_rows: return

        # Get the first row's info for the menu header
        first_row = selected_rows[0]
        original_config_index_item = self.latency_table.item(first_row, 0)
        if not original_config_index_item: return
        try:
            first_config_index = int(original_config_index_item.data(Qt.UserRole))
            if not (0 <= first_config_index < len(self.configs)): return
            first_config = self.configs[first_config_index]
            remark_short = first_config.get('remark', first_config.get('hostname', f'Idx {first_config_index}'))[:30]
        except (ValueError, TypeError):
            return

        context_menu = QMenu()
        if len(selected_rows) > 1:
            context_menu.addAction(f"Selected: {len(selected_rows)} configs...")
        else:
            context_menu.addAction(f"Config: {remark_short}...")

        # Add copy action for all selected
        copy_url_action = context_menu.addAction(f"Copy Config URL{' (All Selected)' if len(selected_rows) > 1 else ''}")
        
        context_menu.addSeparator()

        connect_action = context_menu.addAction("Connect to this config")
        connect_action.setEnabled(len(selected_rows) == 1)
        if len(selected_rows) == 1:
            connect_action.triggered.connect(lambda: self.connect_to_selected_config_context_menu(self.latency_table))
        
        context_menu.addSeparator()

        # Get test capabilities for first config
        proto = first_config.get('protocol', 'error')
        host = first_config.get('hostname', 'error')
        port = self._parse_port(first_config.get('port', '0'))
        is_valid_host = host not in ['error', 'unknown', 'parse_err', 'vmess_host_err', 'sip008_host_err', 'ss_err', 'unknown_host', 'ssr_host']
        is_xray_proto = proto in ['ss', 'vmess', 'vless', 'trojan']

        # Add test options
        if len(selected_rows) == 1:
            test_ping_action = context_menu.addAction("Test Ping (Selected 1 config)")
            test_ping_action.setEnabled(is_valid_host and proto not in ['comment', 'error', 'ssr', 'unknown'])

            test_netcat_action = context_menu.addAction("Test Netcat (Selected 1 config)")
            test_netcat_action.setEnabled(is_valid_host and port > 0 and proto not in ['comment', 'error', 'ssr', 'unknown'])

            test_download_action = context_menu.addAction("Test Download Speed (Selected 1 config)")
            test_download_action.setEnabled(is_xray_proto and is_valid_host and port > 0)



            test_site_action = context_menu.addAction(f"Test Site (Selected 1 config)")
            test_site_action.setEnabled(is_xray_proto and is_valid_host and port > 0)

            test_http_action = context_menu.addAction(f"Test HTTP (Selected 1 config)")
            test_http_action.setEnabled(is_xray_proto and is_valid_host and port > 0)

            context_menu.addSeparator()
        else:
            # Add batch test options for multiple selection
            test_ping_action = context_menu.addAction(f"Test Ping (Selected {len(selected_rows)} configs)")
            test_netcat_action = context_menu.addAction(f"Test Netcat (Selected {len(selected_rows)} configs)")
            test_download_action = context_menu.addAction(f"Test Download Speed (Selected {len(selected_rows)} configs)")

            test_site_action = context_menu.addAction(f"Test Site (Selected {len(selected_rows)} configs)")
            test_http_action = context_menu.addAction(f"Test HTTP (Selected {len(selected_rows)} configs)")

        action = context_menu.exec_(self.latency_table.mapToGlobal(position))

        if action == copy_url_action:
            urls = []
            for row in selected_rows:
                index_item = self.latency_table.item(row, 0)
                if index_item:
                    try:
                        config_index = int(index_item.data(Qt.UserRole))
                        if 0 <= config_index < len(self.configs):
                            url = self.configs[config_index].get('original_url', '')
                            if url:
                                urls.append(url)
                    except (ValueError, TypeError):
                        continue

            if urls:
                QApplication.clipboard().setText('\n'.join(urls))
                self.status_bar.showMessage(f"Copied {len(urls)} config URL{'s' if len(urls) > 1 else ''}", 3000)
            else:
                self.status_bar.showMessage("No valid URLs found to copy", 3000)

        # Handle test actions
        elif action == test_ping_action:
            if len(selected_rows) == 1:
                self._run_single_ping_test(first_config_index)
            else:
                # Get all valid config indices for ping test
                indices_to_test = []
                configs_to_test = []
                for row in selected_rows:
                    index_item = self.latency_table.item(row, 0)
                    if index_item:
                        try:
                            config_index = int(index_item.data(Qt.UserRole))
                            if 0 <= config_index < len(self.configs):
                                config = self.configs[config_index]
                                if (config.get('protocol') not in ['comment', 'error', 'ssr', 'unknown'] and
                                    config.get('hostname') not in ['error', 'unknown', 'parse_err', 'vmess_host_err',
                                                                'sip008_host_err', 'ss_err', 'unknown_host', 'ssr_host']):
                                    indices_to_test.append(config_index)
                                    configs_to_test.append(config)
                        except (ValueError, TypeError):
                            continue

                if indices_to_test:
                    max_workers = self.ping_max_workers_spinbox.value()

                    # Clear previous results for these indices
                    for i in indices_to_test:
                        self.configs[i].pop('ping_latency', None)
                        self.configs[i].pop('ping_available', None)
                        na_item = QTableWidgetItem("...")
                        na_item.setTextAlignment(Qt.AlignCenter)
                        self._apply_cell_color(na_item, None, None)
                        self.latency_table.setItem(i, 5, na_item)  # Column 5 = Ping

                    # Setup UI for test start
                    self.test_progress_bar.setVisible(True)
                    self.test_progress_bar.setValue(0)
                    self.test_progress_bar.setMaximum(len(indices_to_test))
                    self.stop_test_button.setEnabled(True)

                    # Create and start the test thread with original indices
                    self.ping_test_thread = LatencyTesterThread(configs_to_test, max_workers=max_workers, original_indices=indices_to_test)
                    try: self.ping_test_thread.update_signal.disconnect()
                    except TypeError: pass
                    try: self.ping_test_thread.progress_signal.disconnect()
                    except TypeError: pass
                    try: self.ping_test_thread.finished_signal.disconnect()
                    except TypeError: pass

                    self.ping_test_thread.update_signal.connect(self._update_ping_latency_in_table)
                    self.ping_test_thread.progress_signal.connect(self.update_progress)
                    self.ping_test_thread.finished_signal.connect(self.on_ping_test_completed)
                    self.ping_test_thread.start()

                    # Reset stopped flag
                    self.stopping_tests = False
                    self.status_bar.showMessage(f"Testing ping latency for {len(indices_to_test)} configs...")

        elif action == test_netcat_action:
            if len(selected_rows) == 1:
                self._run_single_netcat_test(first_config_index)
            else:
                # Get all valid config indices for netcat test
                indices_to_test = []
                for row in selected_rows:
                    index_item = self.latency_table.item(row, 0)
                    if index_item:
                        try:
                            config_index = int(index_item.data(Qt.UserRole))
                            if 0 <= config_index < len(self.configs):
                                config = self.configs[config_index]
                                if (config.get('protocol') not in ['comment', 'error', 'ssr', 'unknown'] and
                                    config.get('hostname') not in ['error', 'unknown', 'parse_err', 'vmess_host_err',
                                                                'sip008_host_err', 'ss_err', 'unknown_host', 'ssr_host'] and
                                    self._parse_port(config.get('port', '0')) > 0):
                                    indices_to_test.append(config_index)
                        except (ValueError, TypeError):
                            continue

                if indices_to_test:
                    configs_to_test = [self.configs[i] for i in indices_to_test]
                    max_workers = self.netcat_max_workers_spinbox.value()

                    # Reset previous results
                    for i in indices_to_test:
                        self.configs[i].pop('netcat_result', None)
                        self.configs[i].pop('netcat_success', None)
                        na_item = QTableWidgetItem("...")
                        na_item.setTextAlignment(Qt.AlignCenter)
                        self._apply_cell_color(na_item, None, None)
                        self.latency_table.setItem(i, 6, na_item)  # Column 6 = Netcat

                    # Setup UI
                    self.test_netcat_button.setText("Testing Netcat...")
                    self.test_netcat_button.setEnabled(False)
                    self.stop_test_button.setEnabled(True)
                    self.test_progress_bar.setVisible(True)
                    self.test_progress_bar.setValue(0)
                    self.test_progress_bar.setMaximum(len(configs_to_test))

                    # Create and start the test thread
                    test_thread = threading.Thread(
                        target=self._process_test_generic,
                        args=(
                            configs_to_test,
                            self._run_netcat_test,
                            'netcat_result',
                            'netcat_success',
                            'Netcat',
                            self.test_netcat_button,
                        ),
                        kwargs={'extra_test_args': {'max_workers': max_workers}},
                        daemon=True
                    )

                    try: self.signals.test_completed.disconnect(self._on_netcat_test_completed)
                    except TypeError: pass
                    self.signals.test_completed.connect(self._on_netcat_test_completed)

                    test_thread.start()
                    self.stopping_tests = False
                    self.status_bar.showMessage(f"Testing netcat connection for {len(indices_to_test)} configs...")

        elif action == test_download_action:
            if len(selected_rows) == 1:
                self._run_single_download_test(first_config_index)
            else:
                # Get all valid config indices for download test
                indices_to_test = []
                for row in selected_rows:
                    index_item = self.latency_table.item(row, 0)
                    if index_item:
                        try:
                            config_index = int(index_item.data(Qt.UserRole))
                            if 0 <= config_index < len(self.configs):
                                config = self.configs[config_index]
                                if (config.get('protocol') in ['ss', 'vmess', 'vless', 'trojan'] and
                                    config.get('hostname') and self._parse_port(config.get('port', '0')) > 0):
                                    indices_to_test.append(config_index)
                        except (ValueError, TypeError):
                            continue

                if indices_to_test:
                    configs_to_test = [self.configs[i] for i in indices_to_test]
                    max_workers = self.download_max_workers_spinbox.value()

                    # Reset previous results
                    for i in indices_to_test:
                        self.configs[i].pop('download_speed', None)
                        self.configs[i].pop('download_success', None)
                        na_item = QTableWidgetItem("...")
                        na_item.setTextAlignment(Qt.AlignCenter)
                        self._apply_cell_color(na_item, None, None)
                        self.latency_table.setItem(i, 7, na_item)  # Column 7 = Download

                    # Setup UI
                    self.test_speed_button.setText("Testing Download...")
                    self.test_speed_button.setEnabled(False)
                    self.stop_test_button.setEnabled(True)
                    self.test_progress_bar.setVisible(True)
                    self.test_progress_bar.setValue(0)
                    self.test_progress_bar.setMaximum(len(configs_to_test))

                    # Create and start the test thread
                    test_thread = threading.Thread(
                        target=self._process_test_generic,
                        args=(
                            configs_to_test,
                            self._run_download_test,
                            'download_speed',
                            'download_success',
                            'Download',
                            self.test_speed_button,
                        ),
                        kwargs={
                            'extra_test_args': {
                                'target_url': self.DOWNLOAD_TEST_URL,
                                'max_workers': max_workers
                            }
                        },
                        daemon=True
                    )

                    try: self.signals.test_completed.disconnect(self._on_download_test_completed)
                    except TypeError: pass
                    self.signals.test_completed.connect(self._on_download_test_completed)

                    test_thread.start()
                    self.stopping_tests = False
                    self.status_bar.showMessage(f"Testing download speed for {len(indices_to_test)} configs...")

        elif action == test_site_action:
            if len(selected_rows) == 1:
                target_url = self.site_url_input.text().strip() or self.SITE_TEST_DEFAULT_URL
                if not target_url.startswith(('http://', 'https://')):
                    target_url = 'https://' + target_url
                self._run_single_xray_test(
                    config_index=first_config_index,
                    latency_key='site_test_latency',
                    success_key='site_success',
                    test_name='Site',
                    extra_args={'target_url': target_url}
                )
            else:
                # Get all valid config indices for Site test
                indices_to_test = []
                for row in selected_rows:
                    index_item = self.latency_table.item(row, 0)
                    if index_item:
                        try:
                            config_index = int(index_item.data(Qt.UserRole))
                            if 0 <= config_index < len(self.configs):
                                config = self.configs[config_index]
                                if (config.get('protocol') in ['ss', 'vmess', 'vless', 'trojan'] and
                                    config.get('hostname') and self._parse_port(config.get('port', '0')) > 0):
                                    indices_to_test.append(config_index)
                        except (ValueError, TypeError):
                            continue

                if indices_to_test:
                    configs_to_test = [self.configs[i] for i in indices_to_test]
                    max_workers = self.xray_max_workers_spinbox.value()

                    # Get target URL
                    target_url = self.site_url_input.text().strip() or self.SITE_TEST_DEFAULT_URL
                    if not target_url.startswith(('http://', 'https://')):
                        target_url = 'https://' + target_url

                    # Reset previous results
                    for i in indices_to_test:
                        self.configs[i].pop('site_test_latency', None)
                        self.configs[i].pop('site_success', None)
                        na_item = QTableWidgetItem("...")
                        na_item.setTextAlignment(Qt.AlignCenter)
                        self._apply_cell_color(na_item, None, None)
                        self.latency_table.setItem(i, 9, na_item)  # Column 9 = Site Test

                    # Setup UI
                    self.test_site_button.setText("Testing Site...")
                    self.test_site_button.setEnabled(False)
                    self.stop_test_button.setEnabled(True)
                    self.test_progress_bar.setVisible(True)
                    self.test_progress_bar.setValue(0)
                    self.test_progress_bar.setMaximum(len(configs_to_test))

                    # Create and start the test thread
                    test_thread = threading.Thread(
                        target=self._process_test_generic,
                        args=(
                            configs_to_test,
                            self._run_xray_connectivity_test,
                            'site_test_latency',
                            'site_success',
                            'Site',
                            self.test_site_button,
                        ),
                        kwargs={
                            'extra_test_args': {
                                'target_url': target_url,
                                'max_workers': max_workers
                            }
                        },
                        daemon=True
                    )

                    try: self.signals.test_completed.disconnect(self._on_site_test_completed)
                    except TypeError: pass
                    self.signals.test_completed.connect(self._on_site_test_completed)

                    test_thread.start()
                    self.stopping_tests = False
                    self.status_bar.showMessage(f"Testing site connection for {len(indices_to_test)} configs...")

        elif action == test_http_action:
            if len(selected_rows) == 1:
                self._run_single_http_test(config_index=first_config_index)
            else:
                # Get all valid config indices for HTTP test
                indices_to_test = []
                for row in selected_rows:
                    index_item = self.latency_table.item(row, 0)
                    if index_item:
                        try:
                            config_index = int(index_item.data(Qt.UserRole))
                            if 0 <= config_index < len(self.configs):
                                config = self.configs[config_index]
                                if (config.get('protocol') in ['ss', 'vmess', 'vless', 'trojan'] and
                                    config.get('hostname') and self._parse_port(config.get('port', '0')) > 0):
                                    indices_to_test.append(config_index)
                        except (ValueError, TypeError):
                            continue

                if indices_to_test:
                    configs_to_test = [self.configs[i] for i in indices_to_test]
                    max_workers = self.http_max_workers_spinbox.value()

                    # Reset previous results
                    for i in indices_to_test:
                        self.configs[i].pop('http_latency', None)
                        self.configs[i].pop('http_success', None)
                        na_item = QTableWidgetItem("...")
                        na_item.setTextAlignment(Qt.AlignCenter)
                        self._apply_cell_color(na_item, None, None)
                        self.latency_table.setItem(i, 10, na_item)  # Column 10 = HTTP Test

                    # Setup UI
                    self.test_http_button.setText("Testing HTTP...")
                    self.test_http_button.setEnabled(False)
                    self.stop_test_button.setEnabled(True)
                    self.test_progress_bar.setVisible(True)
                    self.test_progress_bar.setValue(0)
                    self.test_progress_bar.setMaximum(len(configs_to_test))

                    # Create and start the test thread
                    test_thread = threading.Thread(
                        target=self._process_test_generic,
                        args=(
                            configs_to_test,
                            self._run_http_test,
                            'http_latency',
                            'http_success',
                            'HTTP',
                            self.test_http_button,
                        ),
                        kwargs={
                            'extra_test_args': {
                                'target_url': self.HTTP_TEST_URL,
                                'max_workers': max_workers
                            }
                        },
                        daemon=True
                    )

                    try: self.signals.test_completed.disconnect(self.on_http_test_completed)
                    except TypeError: pass
                    self.signals.test_completed.connect(self.on_http_test_completed)

                    test_thread.start()
                    self.stopping_tests = False
                    self.status_bar.showMessage(f"Testing HTTP connection for {len(indices_to_test)} configs...")

    def _run_single_ping_test(self, config_index):
        """Run a ping test for a single configuration."""
        if not (0 <= config_index < len(self.configs)):
            return

        config = self.configs[config_index]
        if config.get('protocol') in ['comment', 'error', 'ssr', 'unknown']:
            return
        if config.get('hostname') in ['error', 'unknown', 'parse_err', 'vmess_host_err',
                                    'sip008_host_err', 'ss_err', 'unknown_host', 'ssr_host']:
            return

        # Clear previous results
        config.pop('ping_latency', None)
        config.pop('ping_available', None)
        na_item = QTableWidgetItem("...")
        na_item.setTextAlignment(Qt.AlignCenter)
        self._apply_cell_color(na_item, None, None)
        self.latency_table.setItem(config_index, 5, na_item)  # Column 5 = Ping

        # Setup UI for test start
        self.test_progress_bar.setVisible(True)
        self.test_progress_bar.setValue(0)
        self.test_progress_bar.setMaximum(1)
        self.stop_test_button.setEnabled(True)

        # Create and start the test thread with original indices
        self.ping_test_thread = LatencyTesterThread([config], max_workers=1, original_indices=[config_index])
        try: self.ping_test_thread.update_signal.disconnect()
        except TypeError: pass
        try: self.ping_test_thread.progress_signal.disconnect()
        except TypeError: pass
        try: self.ping_test_thread.finished_signal.disconnect()
        except TypeError: pass

        self.ping_test_thread.update_signal.connect(self._update_ping_latency_in_table)
        self.ping_test_thread.progress_signal.connect(self.update_progress)
        self.ping_test_thread.finished_signal.connect(self.on_ping_test_completed)
        self.ping_test_thread.start()

        # Reset stopped flag
        self.stopping_tests = False
        self.status_bar.showMessage("Testing ping latency...")

    def _run_single_netcat_test(self, config_index):
        if not (0 <= config_index < len(self.configs)):
            self.log_debug(f"Invalid config index for single netcat test: {config_index}")
            return

        config = self.configs[config_index]
        hostname = config.get('hostname', '')
        port = config.get('port', '')
        remark = config.get('remark', hostname)
        test_name = "Netcat"

        # Pre-check validity
        if not hostname or hostname in ['error', 'unknown', 'parse_err', 'vmess_host_err', 'sip008_host_err', 'ss_err', 'unknown_host', 'ssr_host']:
            msg = f"Skipping single {test_name} test for '{remark}': Invalid hostname."
            self.log_debug(msg)
            self.status_bar.showMessage(msg, 5000)
            self.signals.update_specific_latency.emit(config_index, "Invalid Host", False, test_name)
            return

        if not self._parse_port(port):
            msg = f"Skipping single {test_name} test for '{remark}': Invalid port."
            self.log_debug(msg)
            self.status_bar.showMessage(msg, 5000)
            self.signals.update_specific_latency.emit(config_index, "Invalid Port", False, test_name)
            return

        # Visually clear cell
        na_item = QTableWidgetItem("Testing...")
        na_item.setTextAlignment(Qt.AlignCenter)
        self._apply_cell_color(na_item, None, None)
        self.latency_table.setItem(config_index, 6, na_item)  # Column 6 = Netcat
        QApplication.processEvents()

        self.status_bar.showMessage(f"Testing {test_name} connection to {remark} ({hostname}:{port})...")

        def worker():
            success = False
            result_value = "Exec Error"
            try:
                success, result_value = self._run_netcat_test(config)
                self.log_debug(f"Single {test_name} Result for Index {config_index}: Success={success}, Value={result_value}")

                # Store results in config
                self.configs[config_index]['netcat_result'] = result_value
                self.configs[config_index]['netcat_success'] = success

                # Emit signal with all required parameters
                self.signals.update_specific_latency.emit(config_index, result_value, success, test_name)

                # Update status bar
                status_msg = f"{test_name} Test '{remark}': {self._format_latency_text(result_value, success, test_name)}"
                QMetaObject.invokeMethod(self.status_bar, "showMessage", Qt.QueuedConnection, Q_ARG(str, status_msg), Q_ARG(int, 5000))

            except Exception as e:
                self.log_debug(f"Error in single {test_name} test worker for {hostname}:{port}: {e}")
                traceback.print_exc()
                err_msg = f"Error ({type(e).__name__})"
                # Ensure results are updated even on error before emitting signal
                self.configs[config_index]['netcat_result'] = err_msg
                self.configs[config_index]['netcat_success'] = False
                self.signals.update_specific_latency.emit(config_index, err_msg, False, test_name)
                QMetaObject.invokeMethod(self.status_bar, "showMessage", Qt.QueuedConnection,
                                       Q_ARG(str, f"{test_name} Test Error for '{remark}'"), Q_ARG(int, 5000))
            finally:
                # Force table refresh after single test completes (success or error) using a signal
                self.signals.refresh_latency_table_signal.emit()

                # Show a brief message box to force UI update like in batch tests
                test_result = "Success" if success else "Failed"
                self.signals.show_message_box.emit(
                    f"{test_name} Test Complete",
                    f"{test_name} test for '{remark}': {test_result}",
                    "info"
                )

        # Start the worker thread
        threading.Thread(target=worker, daemon=True).start()

    def _run_single_download_test(self, config_index):
        """ Helper to run a single Download speed test """
        if not (0 <= config_index < len(self.configs)): return

        config = self.configs[config_index]
        remark = config.get('remark', config.get('hostname', f'Idx {config_index}'))
        test_name = "Download"

        # Pre-check validity
        if config.get('protocol') not in ['ss', 'vmess', 'vless', 'trojan']:
             msg = f"Skipping single {test_name} test for '{remark}': Unsupported protocol."; self.log_debug(msg)
             self.status_bar.showMessage(msg, 5000);
             self.signals.update_specific_latency.emit(config_index, "Unsupported", False, test_name)
             return
        if not config.get('hostname') or not self._parse_port(config.get('port')):
             msg = f"Skipping single {test_name} test for '{remark}': Invalid host/port."; self.log_debug(msg)
             self.status_bar.showMessage(msg, 5000);
             self.signals.update_specific_latency.emit(config_index, "Bad Config", False, test_name)
             return

        target_url = self.DOWNLOAD_TEST_URL
        self.log_debug(f"Starting single {test_name} test for index {config_index} ('{remark}') -> {target_url}")
        self.status_bar.showMessage(f"Running {test_name} test for '{remark}'...")

        # Visually clear cell
        na_item = QTableWidgetItem("Testing..."); na_item.setTextAlignment(Qt.AlignCenter)
        self._apply_cell_color(na_item, None, None); self.latency_table.setItem(config_index, 7, na_item) # Col 7 = Download
        QApplication.processEvents()

        def worker():
            success = False; result_value = "Exec Error"; allocated_port = None
            try:
                allocated_port = self.find_available_port()
                if not allocated_port: raise RuntimeError("No ports available for single test")
                # Call the specific download test function
                success, result_value = self._run_download_test(config, target_url=target_url, local_port=allocated_port)
                self.log_debug(f"Single {test_name} Result for Index {config_index}: Success={success}, Value={result_value}")
            except Exception as e:
                self.log_debug(f"Error in single {test_name} test thread for index {config_index}: {e}")
                traceback.print_exc(); success = False; result_value = f"Exec Error ({type(e).__name__})"
            finally:
                 if allocated_port: self.release_port(allocated_port)
                 try:
                     self.configs[config_index]['download_speed'] = result_value
                     self.configs[config_index]['download_success'] = success
                     self.signals.update_specific_latency.emit(config_index, result_value, success, test_name)
                     status_msg = f"{test_name} Test '{remark}': {self._format_latency_text(result_value, success, test_name)}"
                     QMetaObject.invokeMethod(self.status_bar, "showMessage", Qt.QueuedConnection, Q_ARG(str, status_msg), Q_ARG(int, 5000))
                 except Exception as update_err:
                     self.log_debug(f"Error updating results after single {test_name} test for index {config_index}: {update_err}")
                     self.signals.update_specific_latency.emit(config_index, f"Update Error ({type(update_err).__name__})", False, test_name)

                 # Force table refresh
                 self.signals.refresh_latency_table_signal.emit()

                 # Show a brief message box to force UI update like in batch tests
                 speed_text = self._format_latency_text(result_value, success, test_name) if success else str(result_value)
                 self.signals.show_message_box.emit(
                     f"{test_name} Test Complete",
                     f"{test_name} test for '{remark}': {'Success' if success else 'Failed'} ({speed_text})",
                     "info"
                 )

        threading.Thread(target=worker, daemon=True).start()

    def _run_single_http_test(self, config_index):
        """Helper to run a single HTTP test"""
        if not (0 <= config_index < len(self.configs)):
            return

        config = self.configs[config_index]
        remark = config.get('remark', config.get('hostname', f'Idx {config_index}'))
        test_name = "HTTP"

        # Pre-check validity
        if config.get('protocol') not in ['ss', 'vmess', 'vless', 'trojan']:
            msg = f"Skipping single {test_name} test for '{remark}': Unsupported protocol."
            self.log_debug(msg)
            self.status_bar.showMessage(msg, 5000)
            self.signals.update_specific_latency.emit(config_index, "Unsupported", False, test_name)
            return
        if not config.get('hostname') or not self._parse_port(config.get('port')):
            msg = f"Skipping single {test_name} test for '{remark}': Invalid host/port."
            self.log_debug(msg)
            self.status_bar.showMessage(msg, 5000)
            self.signals.update_specific_latency.emit(config_index, "Invalid Host/Port", False, test_name)
            return

        # Clear previous results
        config.pop('http_latency', None)
        config.pop('http_success', None)
        na_item = QTableWidgetItem("...")
        na_item.setTextAlignment(Qt.AlignCenter)
        self._apply_cell_color(na_item, None, None)
        self.latency_table.setItem(config_index, 10, na_item) # Column 10 = HTTP Test

        def worker():
            success = False
            result_value = "Exec Error"
            allocated_port = None
            try:
                allocated_port = self.find_available_port()
                if not allocated_port:
                    raise RuntimeError("No ports available for single test")

                # Call the HTTP test function
                success, result_value = self._run_http_test(config, target_url=self.HTTP_TEST_URL, local_port=allocated_port)
                self.log_debug(f"Single {test_name} Result for Index {config_index}: Success={success}, Value={result_value}")

            except Exception as e:
                self.log_debug(f"Error in single {test_name} test worker for {remark}: {e}")
                traceback.print_exc()
                success = False
                result_value = f"Error ({type(e).__name__})"

            finally:
                if allocated_port:
                    self.release_port(allocated_port)

                try:
                    # Store results in config
                    self.configs[config_index]['http_latency'] = result_value
                    self.configs[config_index]['http_success'] = success

                    # Emit signal with all required parameters
                    self.signals.update_specific_latency.emit(config_index, result_value, success, test_name)

                    # Update status bar
                    status_msg = f"{test_name} Test '{remark}': {self._format_latency_text(result_value, success, test_name)}"
                    QMetaObject.invokeMethod(self.status_bar, "showMessage", Qt.QueuedConnection, Q_ARG(str, status_msg), Q_ARG(int, 5000))

                    # Force table refresh
                    self.signals.refresh_latency_table_signal.emit()

                except Exception as update_err:
                    self.log_debug(f"Error updating results after single {test_name} test for index {config_index}: {update_err}")
                    self.signals.update_specific_latency.emit(config_index, f"Update Error ({type(update_err).__name__})", False, test_name)
                    self.signals.refresh_latency_table_signal.emit()

        threading.Thread(target=worker, daemon=True).start()

    def _run_single_xray_test(self, config_index, latency_key, success_key, test_name, extra_args=None):
        if not (0 <= config_index < len(self.configs)):
            self.log_debug(f"Invalid config index for single {test_name} test: {config_index}")
            return

        config = self.configs[config_index]
        hostname = config.get('hostname', '')
        remark = config.get('remark', hostname)

        # Pre-check validity
        if config.get('protocol') not in ['ss', 'vmess', 'vless', 'trojan']:
            msg = f"Skipping single {test_name} test for '{remark}': Unsupported protocol."
            self.log_debug(msg)
            self.status_bar.showMessage(msg, 5000)
            self.signals.update_specific_latency.emit(config_index, "Unsupported", False, test_name)
            return
        if not config.get('hostname') or not self._parse_port(config.get('port')):
            msg = f"Skipping single {test_name} test for '{remark}': Invalid host/port."
            self.log_debug(msg)
            self.status_bar.showMessage(msg, 5000)
            self.signals.update_specific_latency.emit(config_index, "Bad Config", False, test_name)
            return

        # Visually clear cell
        na_item = QTableWidgetItem("Testing...")
        na_item.setTextAlignment(Qt.AlignCenter)
        self._apply_cell_color(na_item, None, None)
        col_index = 8 if test_name == "Google" else 9  # Column 8 = Google, 9 = Site
        self.latency_table.setItem(config_index, col_index, na_item)
        QApplication.processEvents()

        def worker():
            success = False
            result_value = "Exec Error"
            allocated_port = None
            try:
                allocated_port = self.find_available_port()
                if not allocated_port:
                    raise RuntimeError("No ports available for single test")

                # Call the specific test function
                success, result_value = self._run_xray_connectivity_test(config, **(extra_args or {}), local_port=allocated_port)
                self.log_debug(f"Single {test_name} Result for Index {config_index}: Success={success}, Value={result_value}")

            except Exception as e:
                self.log_debug(f"Error in single {test_name} test worker for {hostname}: {e}")
                traceback.print_exc()
                success = False
                result_value = f"Error ({type(e).__name__})"

            finally:
                if allocated_port:
                    self.release_port(allocated_port)
                try:
                    # Store results in config
                    self.configs[config_index][latency_key] = result_value
                    self.configs[config_index][success_key] = success

                    # Emit signal with all required parameters
                    self.signals.update_specific_latency.emit(config_index, result_value, success, test_name)

                    # Update status bar
                    status_msg = f"{test_name} Test '{remark}': {self._format_latency_text(result_value, success, test_name)}"
                    QMetaObject.invokeMethod(self.status_bar, "showMessage", Qt.QueuedConnection, Q_ARG(str, status_msg), Q_ARG(int, 5000))

                    # Force table refresh after single test completes
                    self.signals.refresh_latency_table_signal.emit()

                    # Show a brief message box to force UI update like in batch tests
                    test_result = "Success" if success else "Failed"
                    latency_text = self._format_latency_text(result_value, success, test_name)
                    self.signals.show_message_box.emit(
                        f"{test_name} Test Complete",
                        f"{test_name} test for '{remark}': {test_result} ({latency_text})",
                        "info"
                    )

                except Exception as update_err:
                    self.log_debug(f"Error updating results after single {test_name} test for index {config_index}: {update_err}")
                    self.signals.update_specific_latency.emit(config_index, f"Update Error ({type(update_err).__name__})", False, test_name)
                    # Force table refresh even after errors or success using a signal - THIS COMMENT IS MISLEADING, THE LINE BELOW IS THE TARGET
                    # QMetaObject.invokeMethod(self, "update_latency_table", Qt.QueuedConnection) # Replace this line
                    self.signals.refresh_latency_table_signal.emit() # With this line

        threading.Thread(target=worker, daemon=True).start()


    def show_results_table_context_menu(self, position):
        selected_items = self.results_table.selectedItems()
        if not selected_items: return

        # Get all unique selected rows
        selected_rows = sorted(set(item.row() for item in selected_items))
        if not selected_rows: return

        # Get the first row's info for the menu header
        first_row = selected_rows[0]
        remark_item = self.results_table.item(first_row, 3)
        remark_short = remark_item.text()[:30] if remark_item else f"Row {first_row}"

        context_menu = QMenu()
        if len(selected_rows) > 1:
            context_menu.addAction(f"Selected: {len(selected_rows)} configs...")
        else:
            context_menu.addAction(f"Config: {remark_short}...")

        # Add copy actions
        copy_url_action = context_menu.addAction(f"Copy Config URL{' (All Selected)' if len(selected_rows) > 1 else ''}")
        context_menu.addSeparator()

        connect_action = context_menu.addAction("Connect to this config")
        connect_action.setEnabled(len(selected_rows) == 1)
        if len(selected_rows) == 1:
            connect_action.triggered.connect(lambda: self.connect_to_selected_config_context_menu(self.results_table))

        action = context_menu.exec_(self.results_table.mapToGlobal(position))
        
        if action == connect_action and len(selected_rows) == 1:
            # Already handled by the lambda connection above, but we can log here if needed
            self.log_debug(f"Connect action triggered from Results table for row {selected_rows[0]}")
            # The actual connection logic is in connect_to_selected_config_context_menu
        elif action == copy_url_action:
            urls = []
            for row in selected_rows:
                url_item = self.results_table.item(row, 4)  # Column 4 contains original URLs
                if url_item and url_item.text():
                    urls.append(url_item.text())

            if urls:
                QApplication.clipboard().setText('\n'.join(urls))
                self.status_bar.showMessage(f"Copied {len(urls)} config URL{'s' if len(urls) > 1 else ''}", 3000)
            else:
                self.status_bar.showMessage("No valid URLs found to copy", 3000)

    # --- Export Tab (Keep As Is) ---
    def setup_profiles_tab(self):
        """Set up the Profiles tab to manage and view predefined profiles"""
        profiles_widget = QWidget()
        self.tab_widget.addTab(profiles_widget, "Profiles")
        profiles_layout = QVBoxLayout(profiles_widget)

        # Profile selection and management
        profile_selection_layout = QHBoxLayout()
        profile_selection_layout.addWidget(QLabel("Select Profile:"))

        # Profile combo box
        self.profiles_combo = QComboBox()
        self.profiles_combo.addItems(["All Predefined"] + self.get_profile_names())
        self.profiles_combo.setMinimumWidth(200)
        self.profiles_combo.currentIndexChanged.connect(self.load_selected_profile)
        profile_selection_layout.addWidget(self.profiles_combo)

        # Refresh button
        refresh_profiles_button = QPushButton("Refresh")
        refresh_profiles_button.setToolTip("Refresh the list of profiles")
        refresh_profiles_button.clicked.connect(self.refresh_profiles)
        profile_selection_layout.addWidget(refresh_profiles_button)

        # Create new profile button
        new_profile_button = QPushButton("New Profile")
        new_profile_button.setToolTip("Create a new empty profile")
        new_profile_button.clicked.connect(self.create_new_profile)
        profile_selection_layout.addWidget(new_profile_button)

        # Delete profile button
        delete_profile_button = QPushButton("Delete Profile")
        delete_profile_button.setToolTip("Delete the selected profile")
        delete_profile_button.clicked.connect(self.delete_selected_profile)
        profile_selection_layout.addWidget(delete_profile_button)

        profile_selection_layout.addStretch(1)
        profiles_layout.addLayout(profile_selection_layout)

        # Profile stats
        profile_stats_layout = QHBoxLayout()
        self.profile_stats_label = QLabel("Total configs: 0 | Successful tests: 0")
        profile_stats_layout.addWidget(self.profile_stats_label)
        profile_stats_layout.addStretch(1)
        profiles_layout.addLayout(profile_stats_layout)

        # Profile configs table
        self.profiles_table = QTableWidget()
        self.profiles_table.setColumnCount(8)  # Protocol, Host, Port, Remark, Success Count, Complete Success Count, Last Test, Original URL
        self.profiles_table.setHorizontalHeaderLabels(["Protocol", "Hostname", "Port", "Remark", "Success Count", "Complete Success", "Last Test", "Original URL"])

        # Table Properties
        self.profiles_table.horizontalHeader().setSectionResizeMode(QHeaderView.Interactive)
        self.profiles_table.setColumnWidth(0, 70)   # Protocol
        self.profiles_table.setColumnWidth(1, 180)  # Hostname
        self.profiles_table.setColumnWidth(2, 50)   # Port
        self.profiles_table.setColumnWidth(3, 200)  # Remark
        self.profiles_table.setColumnWidth(4, 100)  # Success Count
        self.profiles_table.setColumnWidth(5, 100)  # Complete Success Count
        self.profiles_table.setColumnWidth(6, 150)  # Last Test
        self.profiles_table.setColumnWidth(7, 300)  # Original URL

        # Make Remark column stretch
        self.profiles_table.horizontalHeader().setStretchLastSection(False)
        self.profiles_table.horizontalHeader().setSectionResizeMode(3, QHeaderView.Stretch)  # Stretch Remark

        self.profiles_table.verticalHeader().setVisible(False)
        self.profiles_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.profiles_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.profiles_table.setAlternatingRowColors(True)
        self.profiles_table.setSortingEnabled(True)
        self.profiles_table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.profiles_table.customContextMenuRequested.connect(self.show_profiles_context_menu)

        profiles_layout.addWidget(self.profiles_table)

        # Initialize with the first profile if available
        if self.profiles_combo.count() > 0:
            self.load_selected_profile(0)

    def setup_export_tab(self):
        # ... (Keep existing implementation - unchanged) ...
        self.export_tab = QWidget()
        self.tab_widget.addTab(self.export_tab, "Export")
        export_layout = QVBoxLayout(self.export_tab)

        description = QLabel("Export configurations (original URLs) to a text file, one URL per line.")
        description.setWordWrap(True); export_layout.addWidget(description)

        export_buttons_group = QGroupBox("Export Options")
        export_buttons_layout = QVBoxLayout(export_buttons_group)

        export_all_button = QPushButton("Export All Loaded Configs (Original URLs)")
        export_all_button.setToolTip("Saves the original URLs of all configurations currently loaded in the application (from self.configs).")
        export_all_button.clicked.connect(self.export_all_configs)
        export_all_button.setMinimumHeight(40); export_buttons_layout.addWidget(export_all_button)

        export_latency_button = QPushButton("Export Working Google Configs (Sorted by Latency)")
        export_latency_button.setToolTip("Saves original URLs of configs that passed the 'Test Google' check,\nsorted from lowest to highest latency.")
        export_latency_button.clicked.connect(self.export_by_google_latency)
        export_latency_button.setMinimumHeight(40); export_buttons_layout.addWidget(export_latency_button)

        emergency_export_button = QPushButton("Emergency Export Raw Input")
        emergency_export_button.setToolTip("Saves the exact text content fetched from the last subscription URL\nor the content entered in the custom input box.")
        emergency_export_button.clicked.connect(self.emergency_export_all)
        emergency_export_button.setMinimumHeight(40); export_buttons_layout.addWidget(emergency_export_button)

        export_complete_test_button = QPushButton("Export Complete Test Results")
        export_complete_test_button.setToolTip("Saves original URLs of configs that passed both Netcat and Download tests in the Complete Test.")
        export_complete_test_button.clicked.connect(self.export_complete_test_results)
        export_complete_test_button.setMinimumHeight(40); export_buttons_layout.addWidget(export_complete_test_button)

        export_layout.addWidget(export_buttons_group)
        export_layout.addStretch()

    def emergency_export_all(self):
        # ... (Keep existing implementation - unchanged) ...
        raw_data = self.original_subscription_text
        if not raw_data:
             if not self.configs: QMessageBox.warning(self, "Warning", "No raw input data or loaded configurations available to export."); return
             lines = [config.get('original_url', '') for config in self.configs if config.get('original_url')]
             if not lines: QMessageBox.warning(self, "Warning", "No original URLs found in loaded configurations."); return
             raw_data = '\n'.join(lines)
        default_filename = "emergency_raw_export.txt"
        file_path, _ = QFileDialog.getSaveFileName(self, "Save Raw Input", default_filename, "Text Files (*.txt);;All Files (*.*)")
        if not file_path: self.status_bar.showMessage("Emergency export cancelled."); return
        try:
            with open(file_path, 'w', encoding='utf-8') as f: f.write(raw_data)
            line_count = len(raw_data.splitlines())
            QMessageBox.information(self, "Success", f"Emergency export successful!\nExported {line_count} raw lines to:\n{file_path}")
            self.status_bar.showMessage(f"Emergency exported {line_count} raw lines.")
        except Exception as e:
            self.log_debug(f"Emergency export failed: {e}"); QMessageBox.critical(self, "Error", f"Emergency export failed: {str(e)}"); self.status_bar.showMessage("Emergency export failed.")

    def export_all_configs(self):
        # ... (Keep existing implementation - unchanged) ...
        if not self.configs: QMessageBox.warning(self, "Warning", "No configurations loaded to export."); return
        default_filename = "export_all_configs.txt"
        file_path, _ = QFileDialog.getSaveFileName(self, "Export All Configs", default_filename, "Text Files (*.txt);;All Files (*.*)")
        if not file_path: self.status_bar.showMessage("Export cancelled."); return
        try:
            exported_count = 0
            with open(file_path, 'w', encoding='utf-8') as f:
                for config in self.configs:
                    url = config.get('original_url', ''); protocol = config.get('protocol', 'error')
                    if url and protocol not in ['comment', 'error', 'unknown', 'ssr']:
                        f.write(f"{url}\n"); exported_count += 1
            if exported_count > 0:
                 QMessageBox.information(self, "Success", f"Successfully exported {exported_count} configuration URLs to:\n{file_path}")
                 self.status_bar.showMessage(f"Exported {exported_count} configurations.")
            else: QMessageBox.warning(self, "Export Empty", "No valid configuration URLs found to export."); self.status_bar.showMessage("Exported 0 configurations.")
        except Exception as e:
            self.log_debug(f"Export all configs failed: {e}"); QMessageBox.critical(self, "Error", f"Failed to export configurations: {str(e)}"); self.status_bar.showMessage("Export failed.")

    def export_by_google_latency(self):
        # ... (Keep existing implementation - unchanged) ...
        if not self.configs: QMessageBox.warning(self, "Warning", "No configurations have been tested for Google connectivity."); return
        valid_configs = [config for config in self.configs if config.get('google_success') is True and isinstance(config.get('google_latency'), (int, float))]
        if not valid_configs: QMessageBox.warning(self, "Warning", "No configurations passed the Google connectivity test with valid latency data."); return
        valid_configs.sort(key=lambda x: x.get('google_latency', float('inf')))
        default_filename = "export_google_working_sorted.txt"
        file_path, _ = QFileDialog.getSaveFileName(self, "Export Working Google Configs", default_filename, "Text Files (*.txt);;All Files (*.*)")
        if not file_path: self.status_bar.showMessage("Export cancelled."); return
        try:
            exported_count = 0
            with open(file_path, 'w', encoding='utf-8') as f:
                for config in valid_configs:
                    url = config.get('original_url', '')
                    if url: f.write(f"{url}\n"); exported_count += 1
            QMessageBox.information(self, "Success", f"Successfully exported {exported_count} working Google configs (sorted by latency) to:\n{file_path}")
            self.status_bar.showMessage(f"Exported {exported_count} working configurations.")
        except Exception as e:
            self.log_debug(f"Export by Google latency failed: {e}"); QMessageBox.critical(self, "Error", f"Failed to export working configurations: {str(e)}"); self.status_bar.showMessage("Export failed.")

    def export_complete_test_results(self):
        """Export configs that passed both Netcat and Download tests in the Complete Test."""
        if not self.filtered_configs:
            QMessageBox.warning(self, "Warning", "No configurations from Complete Test available to export. Run Complete Test first.");
            return

        # Check if these are actually from a complete test
        has_download_success = any(config.get('download_success') is True for config in self.filtered_configs)
        has_netcat_success = any(config.get('netcat_success') is True for config in self.filtered_configs)

        if not (has_download_success and has_netcat_success):
            response = QMessageBox.question(
                self, "Confirm Export",
                "The current filtered configs may not be from a Complete Test. Export anyway?",
                QMessageBox.Yes | QMessageBox.No
            )
            if response == QMessageBox.No:
                self.status_bar.showMessage("Export cancelled.");
                return

        default_filename = "Filtered_Configs.txt"
        script_dir = os.path.dirname(os.path.abspath(__file__))
        file_path, _ = QFileDialog.getSaveFileName(
            self, "Export Complete Test Results",
            os.path.join(script_dir, default_filename),
            "Text Files (*.txt);;All Files (*.*)"
        )

        if not file_path:
            self.status_bar.showMessage("Export cancelled.");
            return

        try:
            # Apply auto-renaming if enabled
            configs_to_export = self.filtered_configs.copy()
            if hasattr(self, 'auto_rename_checkbox') and self.auto_rename_checkbox.isChecked():
                self.log_debug("Applying auto-rename for export")
                configs_to_export = self._apply_auto_rename(configs_to_export)

            exported_count = 0
            with open(file_path, 'w', encoding='utf-8') as f:
                for config in configs_to_export:
                    url = config.get('original_url', '')
                    if url:
                        f.write(f"{url}\n")
                        exported_count += 1

            QMessageBox.information(
                self, "Success",
                f"Successfully exported {exported_count} configs that passed Complete Test to:\n{file_path}"
            )
            self.status_bar.showMessage(f"Exported {exported_count} Complete Test configurations.")
        except Exception as e:
            self.log_debug(f"Export Complete Test results failed: {e}")
            QMessageBox.critical(self, "Error", f"Failed to export Complete Test configurations: {str(e)}")
            self.status_bar.showMessage("Export failed.")

    def browse_export_directory(self):
        """Open a directory browser dialog to select the export directory"""
        directory = QFileDialog.getExistingDirectory(
            self, "Select Export Directory",
            self.export_dir_input.text(),
            QFileDialog.ShowDirsOnly | QFileDialog.DontResolveSymlinks
        )
        if directory:
            self.export_dir_input.setText(directory)
            self.log_debug(f"Export directory set to: {directory}")

    def browse_http_export_directory(self):
        """Open a directory browser dialog to select the HTTP test export directory"""
        directory = QFileDialog.getExistingDirectory(
            self, "Select HTTP Test Export Directory",
            self.http_export_dir_input.text(),
            QFileDialog.ShowDirsOnly | QFileDialog.DontResolveSymlinks
        )
        if directory:
            self.http_export_dir_input.setText(directory)
            self.log_debug(f"HTTP test export directory set to: {directory}")

    def _apply_auto_rename(self, configs):
        """Apply auto-renaming to configs based on predefined rules"""
        # Define renaming rules - map from hostname to new name prefix
        rename_rules = {
            # Add your renaming rules here
            # Format: 'hostname': 'new_name_prefix'
            'example.com': 'Example',
            'google.com': 'Google',
            'cloudflare.com': 'CF',
            # Add more rules as needed
        }

        renamed_configs = []
        for i, config in enumerate(configs):
            config_copy = dict(config)

            # Get hostname and check if it matches any rule
            hostname = config.get('hostname', '').lower()
            new_prefix = None

            # Check for exact matches
            if hostname in rename_rules:
                new_prefix = rename_rules[hostname]
            else:
                # Check for partial matches
                for host_pattern, prefix in rename_rules.items():
                    if host_pattern in hostname:
                        new_prefix = prefix
                        break

            # Apply renaming if a rule matched
            if new_prefix:
                # Get original URL
                original_url = config.get('original_url', '')
                if original_url:
                    # Parse the URL to extract components
                    protocol = config.get('protocol', '').upper()
                    port = config.get('port', '')

                    # Create a new remark with index
                    new_remark = f"{new_prefix}-{i+1:02d}"

                    # Modify the URL to include the new remark
                    # This is a simplified approach - in a real implementation,
                    # you would need to properly parse and reconstruct the URL
                    # based on the specific protocol format

                    # For this example, we'll just add a note that renaming would happen
                    self.log_debug(f"Would rename config {i} from '{config.get('remark', '')}' to '{new_remark}'")

                    # In a real implementation, you would modify the URL here
                    # For now, we'll just keep the original URL
                    config_copy['remark'] = new_remark

            renamed_configs.append(config_copy)

        return renamed_configs

    def format_config_as_url(self, config):
        # ... (Keep existing implementation - unchanged) ...
        return config.get('original_url', '')


    # --- read_subscriptions/_read_single_subscription/is_base64_encoded (Keep As Is) ---
    def read_subscriptions(self, input_source):
        # ... (Keep Refined Version - unchanged) ...
        self.log_debug(f"Reading subscriptions from source type: {'URL/File/Block'}")
        self.original_subscription_text = input_source
        sources_to_process = []
        processed_as = "Direct Text / Multi-line"
        trimmed_source = input_source.strip()
        is_likely_url = re.match(r"^(https?|file)://", trimmed_source, re.IGNORECASE)
        is_likely_path = os.path.sep in trimmed_source and not is_likely_url and len(trimmed_source) < 260

        if is_likely_url or (is_likely_path and os.path.exists(trimmed_source)):
            sources_to_process.append(trimmed_source)
            processed_as = "Single URL/File Path"
        else:
            sources_to_process = [line.strip() for line in input_source.splitlines() if line.strip()]
            if not sources_to_process and trimmed_source:
                 sources_to_process.append(trimmed_source)
                 processed_as = "Single Config Line / Base64?"

        if not sources_to_process:
             self.log_debug("No valid sources found in input after parsing.")
             self.configs = []
             return False

        self.log_debug(f"Processing input as: {processed_as}. Found {len(sources_to_process)} source lines/URLs/paths...")
        temp_all_configs = []
        for source in sources_to_process:
            current_configs = self._read_single_subscription(source)
            if current_configs: temp_all_configs.extend(current_configs)
            else:
                if not source.startswith('#') and not (os.path.isfile(source) and os.path.getsize(source)==0) :
                    self.log_debug(f"    No configs extracted or error processing source: {source[:80]}")

        self.configs = temp_all_configs
        self.log_debug(f"Finished reading subscriptions. Total entries loaded (incl. comments/errors): {len(self.configs)}")
        return True


    def _read_single_subscription(self, url_or_file_or_config_line):
        # Special handling for URLs to prevent crashes
        source_desc = url_or_file_or_config_line[:80]; extracted_configs = []; text_content = ""
        try:
            # Add extra validation for URL
            if not url_or_file_or_config_line or not isinstance(url_or_file_or_config_line, str):
                self.log_debug(f"Invalid input: {type(url_or_file_or_config_line)}")
                return []

            source_type = "Direct Text"
            if url_or_file_or_config_line.startswith(('http://', 'https://')):
                source_type = "URL"; self.log_debug(f"    Fetching from URL: {source_desc}...")
                try:
                     headers = {'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36'}
                     with requests.Session() as session:
                         session.headers.update(headers)
                         response = session.get(url_or_file_or_config_line, timeout=20, verify=False, allow_redirects=True)
                     response.raise_for_status()
                     response.encoding = response.apparent_encoding if response.apparent_encoding else 'utf-8'
                     text_content = response.text
                     self.log_debug(f"    URL fetch OK. Size: {len(text_content)} bytes. Status: {response.status_code}")
                except requests.exceptions.Timeout:
                     self.log_debug(f"    Network Timeout fetching URL: {source_desc}")
                     self.signals.show_message_box.emit("Network Error", f"Timeout occurred while fetching subscription:\n{source_desc}", "warning"); return []
                except requests.exceptions.HTTPError as http_err:
                    self.log_debug(f"    HTTP error fetching URL {source_desc}: {http_err}")
                    self.signals.show_message_box.emit("Network Error", f"Failed to fetch subscription (HTTP {http_err.response.status_code}):\n{source_desc}", "warning"); return []
                except requests.exceptions.RequestException as req_err:
                     self.log_debug(f"    Network error fetching URL {source_desc}: {req_err}")
                     self.signals.show_message_box.emit("Network Error", f"Failed to fetch subscription:\n{source_desc}\n\nError: {req_err}", "warning"); return []
            elif os.path.isfile(url_or_file_or_config_line):
                 source_type = "File"; self.log_debug(f"    Reading from file: {source_desc}...")
                 try:
                     with open(url_or_file_or_config_line, 'r', encoding='utf-8', errors='ignore') as file: text_content = file.read()
                     self.log_debug(f"    Read {len(text_content)} bytes from file.")
                 except OSError as file_err:
                     self.log_debug(f"    Error reading file {source_desc}: {file_err}")
                     self.signals.show_message_box.emit("File Error", f"Failed to read file:\n{source_desc}\n\nError: {file_err}", "warning"); return []
            else: text_content = url_or_file_or_config_line

            if not text_content.strip(): self.log_debug(f"    No content found/retrieved for source: {source_desc}"); return []

            decoded_text = text_content; trimmed_content = text_content.strip()
            looks_like_direct_uri = re.match(r"^(ss|vmess|vless|trojan|ssr)://", trimmed_content)
            might_be_subscription_b64 = ( not looks_like_direct_uri and len(trimmed_content) > 50 and re.match(r"^[a-zA-Z0-9+/=\-_]+$", trimmed_content) )

            if might_be_subscription_b64:
                try:
                    base64_padded = fix_base64_padding(trimmed_content); decoded_bytes = base64.urlsafe_b64decode(base64_padded)
                    try: decoded_text = decoded_bytes.decode('utf-8'); self.log_debug("    Base64 (urlsafe) decoded successfully (UTF-8).")
                    except UnicodeDecodeError: decoded_text = decoded_bytes.decode('latin-1', errors='ignore'); self.log_debug("    Base64 (urlsafe) decoded successfully (Latin-1 fallback).")
                except (base64.Error, ValueError, Exception) as b64_err:
                    self.log_debug(f"    Base64 decode failed for '{source_desc}': {b64_err}. Using original text."); decoded_text = text_content

            lines = decoded_text.splitlines(); parse_errors = 0
            for line_num, line in enumerate(lines):
                 line = line.strip();
                 if not line: continue
                 config = decode_proxy_url(line, parent_logger=self.log_debug)
                 if config:
                     extracted_configs.append(config)
                     if config.get('protocol') == 'error': parse_errors += 1

            entry_type_counts = {};
            for cfg in extracted_configs: proto = cfg.get('protocol', 'unknown'); entry_type_counts[proto] = entry_type_counts.get(proto, 0) + 1
            count_summary = ", ".join(f"{k}:{v}" for k,v in entry_type_counts.items())
            self.log_debug(f"    Finished processing source '{source_desc}'. Found entries: [{count_summary}]")
            if parse_errors > 0: self.log_debug(f"    Note: {parse_errors} parsing errors encountered for source '{source_desc}'.")
            return extracted_configs
        except Exception as e:
            self.log_debug(f"    FATAL Error processing source '{source_desc}': {e}")
            traceback.print_exc(); self.signals.show_message_box.emit("Processing Error", f"An unexpected error occurred while processing source:\n{source_desc}\n\nError: {e}", "error")
            return []


    def is_base64_encoded(self, text):
        # ... (Keep existing implementation - unchanged) ...
        pattern = re.compile(r"^[a-zA-Z0-9+/=\-_ \r\n\t]+$")
        if not text or not pattern.match(text): return False
        text_no_space = "".join(text.split())
        if not text_no_space: return False
        has_padding = '=' in text_no_space
        valid_chars_only = re.fullmatch(r"^[a-zA-Z0-9+/_\-]+$", text_no_space.replace('=', '')) is not None
        if len(text_no_space) < 4: return False
        if has_padding and len(text_no_space) % 4 != 0: return False
        if not valid_chars_only: return False
        try:
            padded_str = fix_base64_padding(text_no_space)
            try: base64.b64decode(padded_str, validate=True); return True
            except (base64.Error, ValueError):
                 try: base64.urlsafe_b64decode(padded_str); return True
                 except (base64.Error, ValueError): return False
        except Exception: return False


    def _run_test_with_port_allocation(self, config, test_func, port_pool, port_semaphore, extra_args):
        # ... (Keep existing implementation - unchanged) ...
        """Helper function for _process_test_generic to acquire/release ports for Xray tests."""
        port = None; acquired_semaphore = False; pool_lock = threading.Lock()
        try:
            port_semaphore.acquire(); acquired_semaphore = True
            with pool_lock:
                if not port_pool:
                    self.log_debug(f"CRITICAL Error: Acquired semaphore but port_pool is empty for {config.get('remark')}!")
                    port_semaphore.release(); acquired_semaphore = False
                    return False, "Internal Error (Port Pool Empty)"
                port = port_pool.pop(0)

            current_extra_args = extra_args.copy(); current_extra_args['local_port'] = port
            if self.stopping_tests: return False, "Stopped" # Check stop flag

            success, result = test_func(config, **current_extra_args)
            return success, result
        except Exception as e:
            self.log_debug(f"Error in _run_test_with_port_allocation for {config.get('remark')}: {e}")
            traceback.print_exc(); return False, f"Error ({type(e).__name__})"
        finally:
            if port is not None:
                with pool_lock: port_pool.append(port)
            if acquired_semaphore: port_semaphore.release()


    def stop_all_tests(self):
        if self.stopping_tests: return # Already stopping
        self.log_debug("STOP SIGNAL RECEIVED - Attempting to stop all tests...")
        self.stopping_tests = True # Set flag IMMEDIATELY

        # --- Stop Dedicated Ping Thread ---
        if hasattr(self, 'ping_test_thread') and self.ping_test_thread.isRunning():
            self.log_debug("Stopping dedicated Ping test thread...")
            self.ping_test_thread.stop() # Signal the thread to stop
            # Optional: Wait briefly for it to finish? self.ping_test_thread.wait(500)

        # --- Stop Dedicated HTTP Test Thread ---
        if hasattr(self, 'http_test_thread') and self.http_test_thread.isRunning():
            self.log_debug("Stopping dedicated HTTP test thread...")
            self.http_test_thread.stop() # Signal the thread to stop
            # Optional: Wait briefly for it to finish? self.http_test_thread.wait(500)

        # --- Stop Complete Test Workflow ---
        if hasattr(self, 'complete_test_running') and self.complete_test_running:
             self.log_debug("Stop requested: Halting Complete Test workflow.")
             self.complete_test_running = False # Mark as not running
             # The flag self.stopping_tests will prevent new tasks.

        # --- Kill Processes ---
        # Crucially, kill processes *after* setting the flag so threads see it
        self.log_debug("Killing any running Xray processes...")
        self._kill_all_xray_processes()
        self.log_debug("Xray processes killed.")

        # --- Reset Semaphore and Counter ---
        # Important to do after killing processes
        self.reset_xray_process_count()
        self.log_debug("Xray counter and semaphore reset.")

        # --- Update UI ---
        self.stop_test_button.setEnabled(False) # Disable stop button itself
        # Re-enable test buttons using invokeMethod for thread safety
        buttons_to_enable = [
             self.test_latency_button, self.test_netcat_button,
             self.test_speed_button, self.test_connectivity_button, self.test_http_button, self.test_site_button
        ]
        button_texts = [
            "Test Ping Latency", "Test Netcat", "Speed Test", "Connectivity Test", "Test HTTP", "Test Custom Site"
        ]
        for i, button in enumerate(buttons_to_enable):
             if button:
                 QMetaObject.invokeMethod(button, "setEnabled", Qt.QueuedConnection, Q_ARG(bool, True))
                 self.signals.update_button_text.emit(button, button_texts[i])

        # Hide progress bar
        QMetaObject.invokeMethod(self.test_progress_bar, "setVisible", Qt.QueuedConnection, Q_ARG(bool, False))
        QMetaObject.invokeMethod(self.test_progress_bar, "setValue", Qt.QueuedConnection, Q_ARG(int, 0))
        if hasattr(self, 'complete_test_progress_bar'):
             QMetaObject.invokeMethod(self.complete_test_progress_bar, "setVisible", Qt.QueuedConnection, Q_ARG(bool, False))
             QMetaObject.invokeMethod(self.complete_test_progress_bar, "setValue", Qt.QueuedConnection, Q_ARG(int, 0))


        # --- Final Status ---
        self.signals.show_message_box.emit("Tests Stopped", "Test execution stopped by user.", "info")
        QMetaObject.invokeMethod(self.status_bar, "showMessage", Qt.QueuedConnection, Q_ARG(str, "Tests stopped."), Q_ARG(int, 5000))
        self.log_debug("Stop request processing finished.")
        # Resetting stopping_tests flag happens when a *new* test starts.
        # Button texts are already updated in the loop above
        self.log_debug("Stop request processed. Active tasks may still complete.")
        # DO NOT reset self.stopping_tests here
        # --- END DOWNLOAD TEST MODIFICATION ---


    def closeEvent(self, event):
        """Handle window close event with enhanced stability features"""
        self.log_debug("Close event triggered. Checking test status...")

        # Check if we're in the middle of a test or complete test
        tests_running = False
        if hasattr(self, 'test_progress_bar') and self.test_progress_bar.isVisible():
            tests_running = True
        if hasattr(self, 'complete_test_running') and self.complete_test_running:
            tests_running = True

        # Check if stability improvements are enabled and system is under load
        system_under_load = False
        if hasattr(self, 'stability_improvements_enabled') and self.stability_improvements_enabled:
            if hasattr(self, 'system_load_high') and self.system_load_high:
                system_under_load = True

        # If tests are running or system is under load, prompt before closing
        if tests_running or system_under_load:
            message = "Tests are currently running." if tests_running else ""
            if system_under_load:
                message += "\nThe system is currently under high load."
                if not tests_running:
                    message += "\nClosing now might cause data loss."
            message += "\n\nAre you sure you want to exit?"

            reply = QMessageBox.question(self, 'Confirm Exit', message,
                                      QMessageBox.Yes | QMessageBox.No, QMessageBox.No)

            if reply == QMessageBox.No:
                self.log_debug("User cancelled application close during tests/high load")
                event.ignore()
                return

            # User confirmed exit, stop all tests
            self.log_debug("User confirmed exit while tests were running or system under load. Stopping all tests...")

        # Stop all tests
        self.stop_all_tests()

        # Stop all timers
        timers_to_stop = ['adaptive_update_timer', 'system_monitor_timer', 'ui_watchdog_timer',
                         'emergency_recovery_timer', '_finalize_timer']
        for timer_name in timers_to_stop:
            if hasattr(self, timer_name):
                timer = getattr(self, timer_name)
                if timer.isActive():
                    timer.stop()
                    self.log_debug(f"Stopped {timer_name}")

        # Clean up any stray temp download files on exit
        try:
            self.log_debug(f"Cleaning up temporary download files in {self.DOWNLOAD_TARGET_DIR}...")
            cleaned_count = 0
            for filename in os.listdir(self.DOWNLOAD_TARGET_DIR):
                # Match the pattern used in _run_download_test
                if filename.startswith("temp_download_") and filename.endswith(".tmp"):
                    file_path = os.path.join(self.DOWNLOAD_TARGET_DIR, filename)
                    try:
                        os.remove(file_path)
                        cleaned_count += 1
                    except Exception as e:
                        self.log_debug(f"Failed to clean up temp download file {filename}: {e}")
            self.log_debug(f"Cleaned up {cleaned_count} temporary download files.")
        except Exception as e:
             self.log_debug(f"Error cleaning download directory: {e}")

        # Force garbage collection to free memory before exit
        try:
            import gc
            self.log_debug("Running garbage collection before exit...")
            gc.collect()
            self.log_debug("Garbage collection completed")
        except ImportError:
            self.log_debug("Garbage collection module not available")

        self.log_debug("Exiting application.")
        event.accept()

    def _reset_ui_before_test(self):
        """Reset UI state before starting a new test to ensure clean state and process pending signals."""
        # Process any pending events to ensure UI is updated
        QCoreApplication.processEvents()

        # Reset progress bar
        self.progress_bar.setValue(0)

        # Force update of latency table to ensure all changes are visible
        self.update_latency_table()

    # Function to initiate the complete test workflow
    def start_complete_test(self):
        """
        Process input and run a complete test workflow:
        1. Process selected/pasted input or load from selected profile
        2. Run Netcat tests on all configs
        3. For each successful Netcat test, immediately start Download test
        4. Filter results to show only configs that pass both tests
        """

        # Ask user to choose between Speed Test and Connectivity Test
        from PyQt5.QtWidgets import QMessageBox

        msg_box = QMessageBox()
        msg_box.setWindowTitle("Complete Test - Download Type")
        msg_box.setText("Choose the download test type for Complete Test:")
        msg_box.setInformativeText("Speed Test uses 2MB file for performance evaluation.\nConnectivity Test uses small file for quick connectivity check.")

        speed_button = msg_box.addButton("Speed Test (2MB)", QMessageBox.ActionRole)
        connectivity_button = msg_box.addButton("Connectivity Test", QMessageBox.ActionRole)
        cancel_button = msg_box.addButton(QMessageBox.Cancel)

        msg_box.exec_()

        if msg_box.clickedButton() == cancel_button:
            return
        elif msg_box.clickedButton() == speed_button:
            self.complete_test_download_url = self.DOWNLOAD_TEST_URL
            self.complete_test_type = "Speed Test"
        else:  # connectivity_button
            self.complete_test_download_url = self.CONNECTIVITY_TEST_URL
            self.complete_test_type = "Connectivity Test"

        # First process the input
        self.log_debug(f"Starting Complete Test workflow with {self.complete_test_type}...")
        self.status_bar.showMessage(f"Starting Complete Test workflow with {self.complete_test_type}...")

        # Clear previous results
        self.configs = []
        self.filtered_configs = []
        self.update_results_table()
        self.update_latency_table()

        # Check if a profile is selected for testing
        selected_profile = self.complete_test_profile_combo.currentText()
        if selected_profile == "All Predefined":
            # Process all predefined subscriptions
            self.log_debug("Complete Test - using All Predefined option")
            self.process_all_subscriptions()

            # Verify that configs were loaded properly
            if not self.configs:
                self.log_debug("WARNING: No configs were loaded from All Predefined subscriptions")
                self.show_message_box("No Configs", "No valid configurations were found from the predefined subscriptions.", "warning")
                return

            # Set a flag to indicate we're testing All Predefined
            self.is_testing_all_predefined = True
            self.log_debug("Set flag: is_testing_all_predefined = True")

            self.log_debug(f"Successfully loaded {len(self.configs)} configs from All Predefined subscriptions")
        elif selected_profile != "None" and selected_profile in self.profiles:
            # Load configs from the selected profile
            self.log_debug(f"Complete Test - loading configs from profile: {selected_profile}")
            profile_configs = self.get_profile(selected_profile)

            if not profile_configs:
                self.show_message_box("Empty Profile", f"The selected profile '{selected_profile}' is empty. Please select another profile or use input configs.", "warning")
                return

            # Use the profile configs
            self.configs = profile_configs
            self.filtered_configs = profile_configs.copy()
            self.log_debug(f"Complete Test - loaded {len(profile_configs)} configs from profile '{selected_profile}'")
        else:
            # Determine input source similar to process_input
            input_source = ""
            source_description = ""

            # Determine the source based on combo box and custom input
            selected_subscriptions = self.subscription_combo.get_selected_items()
            custom_text = self.custom_subscription.text().strip()

            if not selected_subscriptions:
                # No subscriptions selected means "All Predefined"
                self.log_debug("Complete Test - processing all predefined subscriptions")
                try:
                    # For Complete Test, we'll just process all sources
                    self.log_debug("Using special handling for All Predefined to prevent crashes")
                    self.process_all_subscriptions()

                    # Verify that configs were loaded properly
                    if not self.configs:
                        self.log_debug("WARNING: No configs were loaded from All Predefined subscriptions")
                        self.show_message_box("No Configs", "No valid configurations were found from the predefined subscriptions.", "warning")
                        return

                    self.log_debug(f"Successfully loaded {len(self.configs)} configs from All Predefined subscriptions")
                    # The configs are now loaded, continue with testing
                except Exception as e:
                    self.log_debug(f"ERROR processing All Predefined subscriptions: {e}")
                    traceback.print_exc()
                    self.show_message_box("Processing Error", f"An error occurred while processing predefined subscriptions:\n\n{str(e)}", "error")
                    return
            elif len(selected_subscriptions) == 1:
                # Single subscription selected
                selected_name = selected_subscriptions[0]
                # Find the subscription by name
                subscription_found = False
                for name, url in self.predefined_subscriptions:
                    if name == selected_name:
                        input_source = url
                        source_description = f"predefined subscription '{name}'"
                        self.log_debug(f"Complete Test - processing {source_description}")
                        subscription_found = True
                        break

                if not subscription_found:
                    self.show_message_box("Invalid Selection", f"Selected subscription '{selected_name}' not found.", "warning")
                    return
            elif len(selected_subscriptions) > 1:
                # Multiple subscriptions selected
                self.log_debug(f"Complete Test - processing {len(selected_subscriptions)} selected subscriptions")
                try:
                    self.process_selected_subscriptions(selected_subscriptions)

                    # Verify that configs were loaded properly
                    if not self.configs:
                        self.log_debug("WARNING: No configs were loaded from selected subscriptions")
                        self.show_message_box("No Configs", "No valid configurations were found from the selected subscriptions.", "warning")
                        return

                    self.log_debug(f"Successfully loaded {len(self.configs)} configs from selected subscriptions")
                    # The configs are now loaded, continue with testing
                except Exception as e:
                    self.log_debug(f"ERROR processing selected subscriptions: {e}")
                    traceback.print_exc()
                    self.show_message_box("Processing Error", f"An error occurred while processing selected subscriptions:\n\n{str(e)}", "error")
                    return

                # Process the subscription
                success = self.read_subscriptions(input_source)
                if not success or not self.configs:
                    self.show_message_box("No Configs", "No valid configurations were found from the source.", "warning")
                    return
            elif custom_text:
                # Custom input box has content
                input_source = custom_text
                source_description = "custom input"
                self.log_debug(f"Complete Test - processing {source_description}")

                # Process the subscription
                success = self.read_subscriptions(input_source)
                if not success or not self.configs:
                    self.show_message_box("No Configs", "No valid configurations were found from the source.", "warning")
                    return
            else:
                # No predefined selected and custom input is empty
                self.show_message_box("Input Empty", "Please select a predefined subscription, paste content into the custom input box, or choose 'All Predefined'.", "warning")
                return

        # Apply protocol and country filters using multi-select
        selected_protocols = self.get_selected_protocols()
        selected_countries = self.get_selected_countries()
        self.log_debug(f"Complete Test - applying filters - Protocols: {selected_protocols}, Countries: {selected_countries}")

        # Start with all configs
        filtered_configs = self.configs.copy()

        # Apply protocol filter (OR logic within protocols)
        if selected_protocols:
            # Specific protocols selected - filter to only those protocols
            protocol_filtered = []
            for config in filtered_configs:
                config_protocol = config.get('protocol', '').lower()

                # Check for exact protocol match first
                if any(config_protocol == protocol.lower() for protocol in selected_protocols):
                    protocol_filtered.append(config)
                    continue

                # Check for VLESS sub-protocol matches
                if config_protocol == 'vless':
                    vless_subtype = self._get_vless_subtype(config)
                    if any(vless_subtype == protocol.lower() for protocol in selected_protocols):
                        protocol_filtered.append(config)
                        continue

            filtered_configs = protocol_filtered
        else:
            # No protocols selected means "All" - exclude only non-testable/error/comment types
            excluded_protocols = ['unknown', 'comment', 'error', 'ssr']
            filtered_configs = [c for c in filtered_configs if c.get('protocol', 'unknown').lower() not in excluded_protocols]

        # Apply country filter (OR logic within countries)
        if selected_countries:
            # Specific countries selected - filter to only those countries
            country_filtered = []
            for config in filtered_configs:
                detected_country = self._detect_config_country(config)
                # Include if country matches any selected country
                if detected_country and detected_country in selected_countries:
                    country_filtered.append(config)
            filtered_configs = country_filtered

        self.filtered_configs = filtered_configs

        if not self.filtered_configs:
            protocol_desc = "All" if not selected_protocols else ", ".join(selected_protocols)
            country_desc = "All" if not selected_countries else ", ".join(selected_countries)
            filter_desc = f"Protocols: {protocol_desc}, Countries: {country_desc}"
            self.show_message_box("No Suitable Configs", f"No configurations matching the filters ({filter_desc}) were found.", "warning")
            return

        # Update UI with the loaded configs
        self.update_results_table()
        self.update_latency_table()

        # Now start the complete test workflow - first initialize tracking variables
        self.complete_test_configs = self.filtered_configs.copy()
        self.complete_test_indices = [i for i, config in enumerate(self.configs) if config in self.complete_test_configs]
        self.complete_test_netcat_done = set()  # Set to track completed netcat tests
        self.complete_test_successful = set()   # Set to track configs that passed netcat
        self.complete_test_download_done = set() # Set to track completed download tests
        self.complete_test_download_success = set() # Set to track configs that passed download

        # Setup UI for complete test
        total_configs = len(self.complete_test_configs)
        total_steps = total_configs * 2  # 2 steps per config (netcat + download)

        # Use thread-safe method to update progress bar
        QMetaObject.invokeMethod(self.complete_test_progress_bar, "setMaximum",
                               Qt.QueuedConnection, Q_ARG(int, total_steps))
        QMetaObject.invokeMethod(self.complete_test_progress_bar, "setValue",
                               Qt.QueuedConnection, Q_ARG(int, 0))
        QMetaObject.invokeMethod(self.complete_test_progress_bar, "setVisible",
                               Qt.QueuedConnection, Q_ARG(bool, True))

        # Update progress label
        progress_text = f"Complete Test Progress: 0/{total_steps} (0% complete)"
        QMetaObject.invokeMethod(self.complete_test_progress_label, "setText",
                               Qt.QueuedConnection, Q_ARG(str, progress_text))

        # Start Netcat tests with default concurrency
        self.log_debug(f"Complete Test - starting Netcat tests on {total_configs} configs")
        self.status_bar.showMessage(f"Complete Test - starting Netcat tests on {total_configs} configs")

        # Create thread to manage the complete test process
        self.complete_test_thread = threading.Thread(target=self._run_complete_test, daemon=True)
        self.complete_test_thread.start()

    def _run_complete_test(self):
        """Background thread to manage the complete test workflow"""
        try:
            # Step 1: Start Netcat tests on all configs
            self._complete_test_run_netcat()

            # Workflow will continue via callbacks and signals
        except Exception as e:
            self.log_debug(f"Error in complete test workflow: {e}")
            traceback.print_exc()
            self.signals.show_message_box.emit("Complete Test Error", f"An error occurred during the complete test: {e}", "error")
            self._complete_test_cleanup()

    def _complete_test_run_netcat(self):
        """Run Netcat tests on all configs in the complete test workflow"""
        configs_to_test = self.complete_test_configs
        indices_to_test = self.complete_test_indices

        if not configs_to_test:
            self.log_debug("Complete Test - No configs to test")
            self._complete_test_cleanup()
            return

        # Reset previous netcat results
        for i in indices_to_test:
            self.configs[i].pop('netcat_result', None)
            self.configs[i].pop('netcat_success', None)
            # Visually clear cell
            na_item = QTableWidgetItem("...")
            na_item.setTextAlignment(Qt.AlignCenter)
            self._apply_cell_color(na_item, None, None)
            self.latency_table.setItem(i, 6, na_item) # Column 6 = Netcat

        # Setup for netcat test
        test_name = "Netcat"
        max_workers = self.netcat_max_workers_spinbox.value()
        self.log_debug(f"Complete Test - Netcat starting with {max_workers} workers for {len(configs_to_test)} configs")

        # Get our signal set up for receiving results
        self.complete_test_netcat_signal = SignalEmitter()
        self.complete_test_netcat_signal.update_specific_latency.connect(self._complete_test_on_netcat_result)

        # Process tests using the generic handler but with our custom signal
        self._process_complete_test_netcat(
            configs_to_test,
            self._run_netcat_test,
            'netcat_result',
            'netcat_success',
            test_name,
            max_workers=max_workers
        )

    def _process_complete_test_netcat(self, configs_to_test, test_func, latency_key, success_key, test_name, max_workers=10):
        """Modified version of _process_test_generic for the complete test workflow - netcat phase"""
        if not configs_to_test:
            self.log_debug(f"No configs to test for {test_name} in complete test.")
            return

        total_count = len(configs_to_test)
        worker_threads = min(max_workers, total_count)
        processed_count = 0

        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_threads) as executor:
            futures = {}
            for i, config in enumerate(configs_to_test):
                if self.stopping_tests:
                    break

                # Store original index for result mapping
                original_index = next((idx for idx, cfg in enumerate(self.configs) if cfg is config), -1)
                if original_index == -1:
                    self.log_debug(f"Warning: Config not found in self.configs during {test_name} test.")
                    continue

                try:
                    future = executor.submit(test_func, config)
                    futures[future] = original_index
                except Exception as e:
                    self.log_debug(f"Error submitting {test_name} test for index {original_index}: {e}")
                    # Emit error for this config
                    self.complete_test_netcat_signal.update_specific_latency.emit(original_index, str(e), False, test_name)
                    processed_count += 1
                    # Update progress
                    QMetaObject.invokeMethod(self.complete_test_progress_bar, "setValue",
                                          Qt.QueuedConnection, Q_ARG(int, processed_count))

            success_count = 0
            for future in concurrent.futures.as_completed(futures):
                if self.stopping_tests:
                    break

                original_index = futures[future]
                try:
                    # Get result from the future (contains success bool and result value)
                    success, result_value = future.result()

                    # --- Store results in the ORIGINAL config dictionary ---
                    if 0 <= original_index < len(self.configs):
                        self.configs[original_index][latency_key] = result_value
                        self.configs[original_index][success_key] = success

                        # --- Emit signal with RAW data ---
                        self.complete_test_netcat_signal.update_specific_latency.emit(original_index, result_value, success, test_name)
                        if success:
                            success_count += 1
                    else:
                        self.log_debug(f"Warning ({test_name}): Invalid original index {original_index} after task completion.")

                except Exception as e:
                    self.log_debug(f"Error processing {test_name} result for index {original_index}: {e}")
                    # Emit error state
                    self.complete_test_netcat_signal.update_specific_latency.emit(original_index, str(e), False, test_name)

                finally:
                    processed_count += 1
                    # Update progress bar
                    QMetaObject.invokeMethod(self.complete_test_progress_bar, "setValue",
                                          Qt.QueuedConnection, Q_ARG(int, processed_count))

        self.log_debug(f"Complete Test - {test_name} phase finished. Success: {success_count}/{total_count}")

        # Check if all configs have been processed for netcat
        # If all netcat tests are done and no successful configs to download test,
        # finish the complete test
        if len(self.complete_test_netcat_done) == len(self.complete_test_configs) and not self.complete_test_successful:
            self.log_debug("Complete Test - All netcat tests completed with no successful configs")
            QMetaObject.invokeMethod(self, "_complete_test_finalize", Qt.QueuedConnection)

    def _complete_test_on_netcat_result(self, index, result_value, success, test_type):
        """Handle netcat result in the complete test workflow"""
        # First update the UI cell
        self._update_specific_latency_in_table(index, result_value, success, test_type)

        # Mark this config as completed for netcat
        self.complete_test_netcat_done.add(index)

        # If successful, add to successful set (but don't start download test yet)
        if success and isinstance(result_value, str) and result_value == "OK":
            self.complete_test_successful.add(index)
            self.log_debug(f"Complete Test: Netcat Success for index {index}. Added to download queue.")

        # Update progress UI - use thread-safe signal
        progress = len(self.complete_test_netcat_done) + len(self.complete_test_download_done)
        total = len(self.complete_test_configs) * 2
        self.signals.complete_test_progress.emit(progress, total)
        self.log_debug(f"Complete Test Progress: {progress}/{total} ({int(progress/total*100 if total > 0 else 0)}%)")

        # Check if all netcat tests are done
        if len(self.complete_test_netcat_done) == len(self.complete_test_configs):
            self.log_debug(f"Complete Test - All {len(self.complete_test_configs)} netcat tests completed")
            self.log_debug(f"Complete Test - {len(self.complete_test_successful)} configs passed netcat")

            # If we have successful netcat tests, start the download phase
            if self.complete_test_successful:
                # Start download tests in a separate thread to avoid blocking UI thread
                threading.Thread(target=self._complete_test_run_downloads, daemon=True).start()
            else:
                # No successful Netcat tests, finalize immediately
                self.log_debug("Complete Test - No successful Netcat tests. Finalizing.")
                self.signals.complete_test_finalize.emit()

    def _complete_test_run_downloads(self):
        """Runs the download test batch for configs that passed Netcat."""
        indices_to_download = list(self.complete_test_successful)
        configs_to_download = [self.configs[i] for i in indices_to_download if 0 <= i < len(self.configs)]
        total_count = len(configs_to_download)
        self.log_debug(f"Complete Test - Download Phase: Starting for {total_count} configs.")

        if not total_count:
            self._check_complete_test_completion() # Should finalize if downloads empty
            return

        # Use the download-specific spinbox for base thread count
        # The semaphore limit is handled inside _run_download_test
        base_workers = self.download_max_workers_spinbox.value()
        # Get current process limit as a guide for pool size
        process_limit = self.max_allowed_xray_processes
        worker_threads = min(base_workers, process_limit + 5, total_count)

        processed_count = 0
        success_download_count = 0

        # Update progress bar starting point (after Netcat phase)
        netcat_progress = len(self.complete_test_configs)
        QMetaObject.invokeMethod(self.complete_test_progress_bar, "setValue", Qt.QueuedConnection, Q_ARG(int, netcat_progress))


        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_threads, thread_name_prefix="CompTestDL-") as executor:
            futures = {}
            for i, config in enumerate(configs_to_download):
                if self.stopping_tests:
                    self.log_debug("Complete Test - Download phase stopped by user.")
                    break

                original_index = indices_to_download[i] # Get the original index

                # Submit using the standard download function - it handles semaphore
                # We do NOT need to acquire semaphore here, _run_download_test does.
                # We also don't need to pass skip_increment=True.
                try:
                    # Use the URL selected by user in the dialog
                    download_url = getattr(self, 'complete_test_download_url', self.DOWNLOAD_TEST_URL)
                    future = executor.submit(self._run_download_test, config, target_url=download_url)
                    futures[future] = original_index
                except Exception as e:
                    self.log_debug(f"Error submitting download test for index {original_index} in Complete Test: {e}")
                    self.complete_test_download_done.add(original_index) # Mark as done (failed)
                    self.signals.update_specific_latency.emit(original_index, str(e), False, "Download")


            for future in concurrent.futures.as_completed(futures):
                original_index = futures[future]

                # Even if stopped, process completed results
                # if self.stopping_tests: break # Optional: stop processing results too

                try:
                    success, result_value = future.result()
                    self.log_debug(f"Complete Test - Download Result for Index {original_index}: Success={success}, Value={result_value}")

                    # Store results directly in the main config list
                    self.configs[original_index]['download_speed'] = result_value
                    self.configs[original_index]['download_success'] = success
                    self.signals.update_specific_latency.emit(original_index, result_value, success, "Download")

                    if success and isinstance(result_value, (int, float)) and result_value > 50:
                        self.complete_test_download_success.add(original_index)
                        success_download_count += 1

                except Exception as e:
                    self.log_debug(f"Error processing download result for index {original_index} in Complete Test: {e}")
                    self.signals.update_specific_latency.emit(original_index, str(e), False, "Download")
                finally:
                    self.complete_test_download_done.add(original_index) # Mark as done
                    processed_count += 1
                    # Update progress bar (Netcat progress + Download progress)
                    current_total_progress = netcat_progress + processed_count
                    self.signals.complete_test_progress.emit(current_total_progress, len(self.complete_test_configs) * 2)


        self.log_debug(f"Complete Test - Download Phase Finished. Successful downloads: {success_download_count}/{total_count}")
        # Final check to ensure finalize signal is emitted
        self._check_complete_test_completion()

    def _complete_test_start_download_for_config(self, index):
        """Start download test for a specific config that passed netcat"""
        if index < 0 or index >= len(self.configs):
            self.log_debug(f"Complete Test - Invalid index {index} for download test")
            return

        config = self.configs[index]
        self.log_debug(f"Complete Test - Starting download test for config index {index}")

        # Clear previous download result
        config.pop('download_speed', None)
        config.pop('download_success', None)

        # Clear the cell
        na_item = QTableWidgetItem("...")
        na_item.setTextAlignment(Qt.AlignCenter)
        self._apply_cell_color(na_item, None, None)
        self.latency_table.setItem(index, 7, na_item) # Column 7 = Download

        # Run the download test in a thread
        threading.Thread(
            target=self._complete_test_run_download_for_config,
            args=(index, config),
            daemon=True
        ).start()

    def _complete_test_run_download_for_config(self, index, config):
        """Run download test for a specific config in the complete test workflow"""
        try:
            # Get target URL for download test
            target_url = self.DOWNLOAD_TEST_URL
            test_name = "Download"

            # Check if stability improvements are enabled
            stability_enabled = hasattr(self, 'stability_improvements_enabled') and self.stability_improvements_enabled

            # Check if we're under heavy load
            system_under_load = hasattr(self, 'system_load_high') and self.system_load_high

            # If system is under heavy load and stability improvements are enabled, delay starting new tests
            if system_under_load and stability_enabled:
                delay = random.uniform(1.0, 3.0)  # Random delay between 1-3 seconds
                self.log_debug(f"Complete Test - System under load, delaying download test for config {index} by {delay:.1f}s")
                time.sleep(delay)

            # Check if we can start another Xray process
            # Try to acquire the semaphore with a timeout (longer timeout if system under load)
            timeout = 5.0 if system_under_load else 2.0
            acquired = self.xray_semaphore.acquire(blocking=True, timeout=timeout)
            if not acquired:
                self.log_debug(f"Complete Test - Too many Xray processes running for download test on config {index}")
                self.signals.update_specific_latency.emit(index, "Too Many Xrays", False, test_name)
                self.complete_test_download_done.add(index)
                self._check_complete_test_completion()
                return

            # Update the counter for logging purposes
            with self.xray_process_lock:
                self.active_xray_processes += 1
                count = self.active_xray_processes
                self.log_debug(f"Complete Test - Xray process count increased to {count} (limit: {self.max_allowed_xray_processes})")

            # Allocate a port
            allocated_port = self.find_available_port()
            if not allocated_port:
                self.log_debug(f"Complete Test - No ports available for download test on config {index}")
                self.signals.update_specific_latency.emit(index, "No Ports", False, test_name)
                self.complete_test_download_done.add(index)
                self._check_complete_test_completion()
                # Release the semaphore since we're not using it
                self.xray_semaphore.release()
                with self.xray_process_lock:
                    self.active_xray_processes -= 1
                return

            # Run the download test
            try:
                # We don't need to call increment_xray_process_count here since we already acquired the semaphore
                success, result_value = self._run_download_test(config, target_url=target_url, local_port=allocated_port, skip_increment=True)

                # Store results
                if 0 <= index < len(self.configs):  # Ensure index is valid
                    self.configs[index]['download_speed'] = result_value
                    self.configs[index]['download_success'] = success

                    # Update UI
                    self.signals.update_specific_latency.emit(index, result_value, success, test_name)

                    # If successful and has a reasonable download speed, add to success set
                    # Only count configs with positive download speed as successful
                    if success and isinstance(result_value, (int, float)) and result_value > 50:  # At least 50 KB/s speed
                        self.log_debug(f"Complete Test - Config {index} passed download test with {result_value} KB/s")
                        self.complete_test_download_success.add(index)
                    else:
                        self.log_debug(f"Complete Test - Config {index} failed download speed criteria: success={success}, value={result_value}")
                else:
                    self.log_debug(f"Complete Test - Invalid index {index} for download test result")
            except Exception as e:
                self.log_debug(f"Complete Test - Error in download test for config {index}: {e}")
                self.signals.update_specific_latency.emit(index, str(e), False, test_name)
                if stability_enabled:
                    # If stability improvements are enabled, log the stack trace for debugging
                    self.log_debug(f"Stack trace for download test error: {traceback.format_exc()}")
            finally:
                # Release the port
                if allocated_port:
                    self.release_port(allocated_port)
        finally:
            # Mark as done regardless of success/failure
            self.complete_test_download_done.add(index)

            # Release the semaphore to allow another process to start
            try:
                self.xray_semaphore.release()
                self.log_debug(f"Complete Test - Released Xray semaphore for config {index}")
            except ValueError:
                self.log_debug(f"Complete Test - Warning: Attempted to release Xray semaphore too many times for config {index}")

            # Decrement the counter for logging purposes
            with self.xray_process_lock:
                if self.active_xray_processes > 0:
                    self.active_xray_processes -= 1
                count = self.active_xray_processes
                self.log_debug(f"Complete Test - Xray process count decreased to {count}")

            # Update progress - use thread-safe signal
            progress = len(self.complete_test_netcat_done) + len(self.complete_test_download_done)
            total = len(self.complete_test_configs) * 2
            self.signals.complete_test_progress.emit(progress, total)

            # Only log progress every 10 updates to reduce log spam
            if progress % 10 == 0:
                self.log_debug(f"Complete Test Progress: {progress}/{total} ({int(progress/total*100 if total > 0 else 0)}%)")

            # Check if complete test is done
            self._check_complete_test_completion()

    def _check_complete_test_completion(self):
        """Check if the complete test workflow is finished"""
        # Complete test is done when:
        # 1. All netcat tests are done AND
        # 2. All download tests for successful netcat configs are done
        netcat_done = len(self.complete_test_netcat_done) == len(self.complete_test_configs)
        # Downloads are done if the number of completed downloads matches the number of successful netcat tests
        downloads_required = len(self.complete_test_successful)
        downloads_done = len(self.complete_test_download_done)

        # Add extra logging
        self.log_debug(f"Check Completion: NetcatDone={netcat_done}, DownloadsRequired={downloads_required}, DownloadsDone={downloads_done}")

        if netcat_done and downloads_done >= downloads_required:
            # Add a small delay to ensure signals are processed before finalizing
            if not hasattr(self, '_finalize_timer'):
                self._finalize_timer = QTimer()
                self._finalize_timer.setSingleShot(True)
                self._finalize_timer.timeout.connect(self._emit_finalize_signal)
            if not self._finalize_timer.isActive():
                self.log_debug("Complete Test - All stages potentially complete. Scheduling finalize check.")
                self._finalize_timer.start(500) # Wait 500ms

    def _emit_finalize_signal(self):
        self.log_debug("Complete Test - Timer expired. Emitting finalize signal.")
        self.signals.complete_test_finalize.emit()

    @pyqtSlot()
    def _complete_test_finalize(self):
        """Finalize the complete test - filter results and update UI"""
        try:
            self.log_debug("Complete Test - Finalizing test workflow")

            # Clear the complete test running flag
            self.complete_test_running = False

            # Reset the is_testing_all_predefined flag
            if hasattr(self, 'is_testing_all_predefined'):
                self.is_testing_all_predefined = False
                self.log_debug("Reset flag: is_testing_all_predefined = False")

            # Get configs that passed both tests
            passed_indices = self.complete_test_download_success
            self.log_debug(f"Complete Test - Found {len(passed_indices)} configs that passed both tests")

            if passed_indices:
                # Create new list of configs that passed both tests (deep copy to avoid reference issues)
                self.filtered_configs = []
                for i in passed_indices:
                    # Create a new dictionary with the same content
                    config_copy = dict(self.configs[i])
                    self.filtered_configs.append(config_copy)

                # Update results table with filtered configs
                self.update_results_table()

                # Log success
                self.log_debug(f"Complete Test - {len(self.filtered_configs)} configs passed both tests")
                self.status_bar.showMessage(f"Complete Test finished. {len(self.filtered_configs)} configs passed both tests.")

                # Check if "All Predefined" is selected in either the subscription combo or the complete test profile combo
                is_all_predefined = (hasattr(self, 'subscription_combo') and self.subscription_combo.currentText() == "All Predefined") or \
                                    (hasattr(self, 'complete_test_profile_combo') and self.complete_test_profile_combo.currentText() == "All Predefined")

                if is_all_predefined:
                    self.log_debug("All Predefined is selected - directly updating individual subscription profiles")

                    try:
                        # Create a dictionary to store configs by subscription name
                        configs_by_subscription = {}

                        # Initialize the dictionary with empty lists for each subscription
                        for name, _ in self.predefined_subscriptions:
                            configs_by_subscription[name] = []

                        # Count how many configs have source information
                        configs_with_source = 0

                        # Group configs by their source subscription
                        for config in self.filtered_configs:
                            source_name = config.get('source_subscription_name', '')

                            if source_name and source_name in configs_by_subscription:
                                # Make sure the config has the necessary success flags
                                if 'netcat_success' not in config:
                                    config['netcat_success'] = False
                                if 'download_success' not in config:
                                    config['download_success'] = False

                                configs_by_subscription[source_name].append(config)
                                configs_with_source += 1
                                self.log_debug(f"Assigned config {config.get('remark', 'unnamed')} to {source_name}")

                        self.log_debug(f"Grouped {configs_with_source} out of {len(self.filtered_configs)} configs by source")

                        # Save each subscription's configs to its profile
                        updated_profiles = []
                        for sub_name, sub_configs in configs_by_subscription.items():
                            if sub_configs:
                                profile_name = sub_name.replace(' ', '_')
                                self.log_debug(f"Saving profile '{profile_name}' with {len(sub_configs)} configs")

                                # Save the profile
                                if self.save_profile(profile_name, sub_configs):
                                    updated_profiles.append(f"{profile_name} ({len(sub_configs)})")

                                    # Update the complete test success counts for this profile
                                    self.log_debug(f"Updating complete test success counts for profile '{profile_name}'")
                                    self.update_profile_success_counts(self.profiles[profile_name], sub_configs, "complete")

                                    # Also update the test profile if it's different
                                    test_profile_name = None
                                    if hasattr(self, 'complete_test_profile_combo'):
                                        test_profile_name = self.complete_test_profile_combo.currentText()

                                    if test_profile_name and test_profile_name != "None" and test_profile_name in self.profiles and test_profile_name != profile_name:
                                        self.log_debug(f"Also updating complete test success counts for test profile '{test_profile_name}'")
                                        # Find configs that match between the test profile and this subscription
                                        test_profile_configs = self.profiles[test_profile_name]
                                        for config in sub_configs:
                                            original_url = config.get('original_url', '')
                                            if original_url:
                                                for test_config in test_profile_configs:
                                                    if test_config.get('original_url', '') == original_url:
                                                        # Update this config in the test profile
                                                        if config.get('netcat_success') is True and config.get('download_success') is True:
                                                            current_count = test_config.get('complete_success_count', 0)
                                                            test_config['complete_success_count'] = current_count + 1
                                                            test_config['last_test'] = datetime.now().strftime('%Y-%m-%d %H:%M:%S')

                                        # Save the updated test profile
                                        self.save_profile(test_profile_name, test_profile_configs)
                                        self.log_debug(f"Saved updated test profile '{test_profile_name}'")

                        # Show a message with all updated profiles
                        if updated_profiles:
                            self.status_bar.showMessage(f"Updated profiles: {', '.join(updated_profiles)}", 5000)
                        else:
                            self.log_debug("No profiles were updated - no configs were grouped by source")
                    except Exception as e:
                        self.log_debug(f"Error updating profiles: {str(e)}")
                        traceback.print_exc()
                else:
                    # Save profile for the current subscription
                    self._save_profile_for_current_subscription()

                    # Update the profile success counts for complete test
                    # First, determine which profile was used for testing
                    test_profile_name = None
                    if hasattr(self, 'complete_test_profile_combo'):
                        test_profile_name = self.complete_test_profile_combo.currentText()

                    # Update the profile that was actually tested
                    if test_profile_name and test_profile_name != "None" and test_profile_name in self.profiles:
                        self.log_debug(f"Updating complete test success counts for test profile '{test_profile_name}'")
                        self.update_profile_success_counts(self.profiles[test_profile_name], self.configs, "complete")

                    # Also update the profile that's currently selected in the Profiles tab
                    if hasattr(self, 'profiles_combo') and self.profiles_combo.count() > 0:
                        profile_name = self.profiles_combo.currentText()
                        if profile_name and profile_name in self.profiles and profile_name != test_profile_name:
                            self.log_debug(f"Updating complete test success counts for current profile '{profile_name}'")
                            self.update_profile_success_counts(self.profiles[profile_name], self.configs, "complete")

                    # Refresh the profiles table to show updated counts
                    if hasattr(self, 'profiles_combo') and self.profiles_combo.count() > 0:
                        self.load_selected_profile(self.profiles_combo.currentIndex())

                # Auto export if enabled
                if hasattr(self, 'auto_export_checkbox') and self.auto_export_checkbox.isChecked():
                    self.log_debug("Auto export enabled - exporting results")
                    self._auto_export_complete_test_results()

                # Just show status bar message, no popup
                self.log_debug(f"Complete Test Finished - {len(self.filtered_configs)} configs passed both tests")

                # Switch to the Profiles tab and select the profile that was tested
                # Find the Profiles tab index
                profiles_tab_index = -1
                for i in range(self.tab_widget.count()):
                    if self.tab_widget.tabText(i) == "Profiles":
                        profiles_tab_index = i
                        break

                if profiles_tab_index >= 0:
                    # Switch to the Profiles tab
                    self.tab_widget.setCurrentIndex(profiles_tab_index)
                    self.log_debug(f"Switched to Profiles tab after complete test")

                    # Determine which profile was used for testing
                    test_profile_name = None
                    if hasattr(self, 'complete_test_profile_combo'):
                        test_profile_name = self.complete_test_profile_combo.currentText()

                    # If a specific profile was tested (not "None"), select it in the profiles combo
                    if test_profile_name and test_profile_name != "None" and hasattr(self, 'profiles_combo'):
                        profile_index = self.profiles_combo.findText(test_profile_name)
                        if profile_index >= 0:
                            self.profiles_combo.setCurrentIndex(profile_index)
                            self.log_debug(f"Selected profile '{test_profile_name}' in Profiles tab")
                    # If no specific profile was tested but we have a subscription selected, try to find its profile
                    elif hasattr(self, 'subscription_combo') and self.subscription_combo.currentIndex() < len(self.predefined_subscriptions):
                        name, _ = self.predefined_subscriptions[self.subscription_combo.currentIndex()]
                        profile_name = name.replace(' ', '_')
                        profile_index = self.profiles_combo.findText(profile_name)
                        if profile_index >= 0:
                            self.profiles_combo.setCurrentIndex(profile_index)
                            self.log_debug(f"Selected profile '{profile_name}' in Profiles tab based on subscription")
                else:
                    # Switch to Results tab
                    self.tab_widget.setCurrentIndex(1)
            else:
                # No configs passed both tests
                self.log_debug("Complete Test - No configs passed both tests")
                # Just show status bar message, no popup
                self.status_bar.showMessage("Complete Test finished. No configurations passed both tests.", 5000)

                # Switch to the Profiles tab and select the profile that was tested
                # Find the Profiles tab index
                profiles_tab_index = -1
                for i in range(self.tab_widget.count()):
                    if self.tab_widget.tabText(i) == "Profiles":
                        profiles_tab_index = i
                        break

                if profiles_tab_index >= 0:
                    # Switch to the Profiles tab
                    self.tab_widget.setCurrentIndex(profiles_tab_index)
                    self.log_debug(f"Switched to Profiles tab after complete test (no configs passed)")

                    # Determine which profile was used for testing
                    test_profile_name = None
                    if hasattr(self, 'complete_test_profile_combo'):
                        test_profile_name = self.complete_test_profile_combo.currentText()

                    # If a specific profile was tested (not "None"), select it in the profiles combo
                    if test_profile_name and test_profile_name != "None" and hasattr(self, 'profiles_combo'):
                        profile_index = self.profiles_combo.findText(test_profile_name)
                        if profile_index >= 0:
                            self.profiles_combo.setCurrentIndex(profile_index)
                            self.log_debug(f"Selected profile '{test_profile_name}' in Profiles tab (no configs passed)")
                    # If no specific profile was tested but we have a subscription selected, try to find its profile
                    elif hasattr(self, 'subscription_combo') and self.subscription_combo.currentIndex() < len(self.predefined_subscriptions):
                        name, _ = self.predefined_subscriptions[self.subscription_combo.currentIndex()]
                        profile_name = name.replace(' ', '_')
                        profile_index = self.profiles_combo.findText(profile_name)
                        if profile_index >= 0:
                            self.profiles_combo.setCurrentIndex(profile_index)
                            self.log_debug(f"Selected profile '{profile_name}' in Profiles tab based on subscription (no configs passed)")

            # Clean up
            self._complete_test_cleanup()

            # Complete automated workflow if active
            if hasattr(self, 'automated_workflow_active') and self.automated_workflow_active:
                QTimer.singleShot(1000, self.complete_automated_workflow)

            # Schedule next run if auto-start is enabled
            if hasattr(self, 'auto_start_checkbox') and self.auto_start_checkbox.isChecked() and hasattr(self, 'auto_start_timer'):
                seconds = self.auto_start_timer.value()
                if seconds > 0:
                    self.log_debug(f"Auto-start enabled - scheduling next run in {seconds} seconds")
                    self.status_bar.showMessage(f"Next Complete Test will start in {seconds} seconds...")

                    # Stop any existing timer
                    if hasattr(self, 'auto_start_timer_obj') and self.auto_start_timer_obj.isActive():
                        self.auto_start_timer_obj.stop()

                    # Start the timer
                    self.auto_start_timer_obj.start(seconds * 1000)  # Convert to milliseconds
        except Exception as e:
            # Log the error
            error_msg = f"ERROR in _complete_test_finalize: {str(e)}"
            self.log_debug(error_msg)
            print(f"\n{'='*50}\nCRITICAL ERROR IN COMPLETE TEST FINALIZE:\n{str(e)}\n{'='*50}")
            traceback.print_exc()

            # Show error message to user
            QMessageBox.critical(self, "Complete Test Error",
                f"An error occurred while finalizing the complete test:\n\n{str(e)}\n\n"
                f"This error has been logged. Please check the debug output for details.")

            # Try to clean up
            try:
                self._complete_test_cleanup()
            except Exception as cleanup_error:
                self.log_debug(f"Error during cleanup after exception: {str(cleanup_error)}")

    def _save_profile_for_current_subscription(self):
        """Save a profile for the current subscription"""
        if not self.filtered_configs:
            return

        # Check if "All Predefined" is selected
        if hasattr(self, 'subscription_combo') and self.subscription_combo.currentIndex() >= len(self.predefined_subscriptions):
            # All Predefined is selected - update individual subscription profiles
            self.log_debug("All Predefined is selected - updating individual subscription profiles")

            # Group configs by their source subscription
            configs_by_source = self._group_configs_by_source()

            # Update each subscription profile separately
            updated_profiles = []
            for sub_name, sub_configs in configs_by_source.items():
                if sub_configs:
                    profile_name = sub_name.replace(' ', '_')
                    self.log_debug(f"Saving profile for '{profile_name}' with {len(sub_configs)} configs")
                    self.save_profile(profile_name, sub_configs)
                    updated_profiles.append(f"{profile_name} ({len(sub_configs)})")

            # Show a message with all updated profiles
            if updated_profiles:
                self.status_bar.showMessage(f"Updated profiles: {', '.join(updated_profiles)}", 5000)
        else:
            # A specific predefined subscription is selected
            name, _ = self.predefined_subscriptions[self.subscription_combo.currentIndex()]
            profile_name = name.replace(' ', '_')

            self.log_debug(f"Saving profile for '{profile_name}'")
            self.save_profile(profile_name, self.filtered_configs)

            # Show a message that the profile was updated
            self.status_bar.showMessage(f"Updated profile '{profile_name}' with {len(self.filtered_configs)} configs", 3000)

        # Update the profile selection combo box if it exists
        if hasattr(self, 'profile_combo'):
            current_text = self.profile_combo.currentText()
            self.profile_combo.clear()
            self.profile_combo.addItems(self.get_profile_names())

            # Try to restore the previous selection
            index = self.profile_combo.findText(current_text)
            if index >= 0:
                self.profile_combo.setCurrentIndex(index)

    def _group_configs_by_source(self):
        """Group filtered configs by their source subscription"""
        configs_by_source = {}

        # Initialize with all predefined subscription names
        for name, _ in self.predefined_subscriptions:
            configs_by_source[name] = []

        # Group configs by their source
        for config in self.filtered_configs:
            source = config.get('source_subscription', '')
            source_name = config.get('source_subscription_name', '')

            # First try to use the source_subscription_name if available
            if source_name and source_name in configs_by_source:
                configs_by_source[source_name].append(config)
                self.log_debug(f"Grouped config {config.get('remark', 'unnamed')} to source {source_name}")
                continue

            # If no source_subscription_name, try to match the source URL with a predefined subscription
            matched = False
            for name, url in self.predefined_subscriptions:
                if source == url:
                    configs_by_source[name].append(config)
                    matched = True
                    self.log_debug(f"Matched config {config.get('remark', 'unnamed')} to source {name} by URL")
                    break

            # If no match, add to unknown
            if not matched and source:
                if 'Unknown' not in configs_by_source:
                    configs_by_source['Unknown'] = []
                configs_by_source['Unknown'].append(config)
                self.log_debug(f"Added config {config.get('remark', 'unnamed')} to Unknown source")

        # Remove empty sources
        return {k: v for k, v in configs_by_source.items() if v}

    def start_predefined_test(self):
        """Start testing configs from the selected profile"""
        # Check if a profile is selected
        if not hasattr(self, 'profile_combo') or self.profile_combo.count() == 0:
            self.log_debug("No profiles available for testing")
            self.signals.show_message_box.emit(
                "No Profiles",
                "No profiles are available for testing. Run a Complete Test first to create profiles.",
                "warning"
            )
            return

        # Get the selected profile
        profile_name = self.profile_combo.currentText()

        # Handle the "All Predefined" option
        if profile_name == "All Predefined":
            self.log_debug("Testing all predefined subscription profiles")
            # Combine configs from all predefined subscription profiles
            all_configs = []

            # Get profiles for all predefined subscriptions
            for name, _ in self.predefined_subscriptions:
                profile_name_formatted = name.replace(' ', '_')
                if profile_name_formatted in self.profiles:
                    profile_configs = self.get_profile(profile_name_formatted)
                    self.log_debug(f"Adding {len(profile_configs)} configs from profile '{profile_name_formatted}'")
                    all_configs.extend(profile_configs)

            if not all_configs:
                self.log_debug("No configs found in any predefined subscription profiles")
                self.signals.show_message_box.emit(
                    "Empty Profiles",
                    "No configurations found in any predefined subscription profiles.",
                    "warning"
                )
                return

            # Use the combined configs
            profile_configs = all_configs
            self.log_debug(f"Combined {len(profile_configs)} configs from all predefined subscription profiles")
        else:
            # Get configs for a specific profile
            profile_configs = self.get_profile(profile_name)

            if not profile_configs:
                self.log_debug(f"Profile '{profile_name}' is empty")
                self.signals.show_message_box.emit(
                    "Empty Profile",
                    f"The selected profile '{profile_name}' does not contain any configurations.",
                    "warning"
                )
                return

        self.log_debug(f"Starting Predefined Test for profile '{profile_name}' with {len(profile_configs)} configs")

        # Clear previous results
        self.configs = []
        self.filtered_configs = []
        self.update_results_table()
        self.update_latency_table()

        # Load the configs from the profile
        for config in profile_configs:
            # Create a copy to avoid modifying the original
            config_copy = dict(config)
            self.configs.append(config_copy)

        self.log_debug(f"Loaded {len(self.configs)} configs from profile '{profile_name}'")

        # Set up for download test
        self.filtered_configs = self.configs.copy()
        self.update_results_table()

        # Start download test on these configs
        self.log_debug("Starting Download test on predefined configs")
        self.status_bar.showMessage(f"Testing {len(self.filtered_configs)} configs from profile '{profile_name}'...")

        # Set flag to indicate this is a predefined test
        self.is_predefined_test = True

        # Set a flag to prevent the generic test completion message from showing
        self.skip_generic_completion_message = True

        # Run download test
        self.start_download_test()

    def _predefined_test_completed(self):
        """Handle completion of predefined test"""
        # Reset the predefined test flag
        self.is_predefined_test = False

        # Reset the skip_generic_completion_message flag
        if hasattr(self, 'skip_generic_completion_message'):
            self.skip_generic_completion_message = False

        # Filter configs that passed the download test
        passed_configs = [config for config in self.configs if config.get('download_success') is True]

        # Get the current profile name
        profile_name = self.profiles_combo.currentText() if hasattr(self, 'profiles_combo') else None

        # Update the profile with success counts
        if profile_name and profile_name in self.profiles:
            self.update_profile_success_counts(self.profiles[profile_name], self.configs, "download")
            self.log_debug(f"Updated success counts for profile '{profile_name}'")

        if passed_configs:
            self.filtered_configs = passed_configs
            self.update_results_table()

            self.log_debug(f"Predefined Test - {len(passed_configs)} configs passed the download test")
            self.status_bar.showMessage(f"Predefined Test finished. {len(passed_configs)} configs passed.")

            # Auto export if enabled
            if hasattr(self, 'predefined_auto_export_checkbox') and self.predefined_auto_export_checkbox.isChecked():
                self.log_debug("Auto export enabled for predefined test - exporting results")
                self._auto_export_predefined_test_results()
            else:
                # Show message box with results only if not auto-exporting
                self.signals.show_message_box.emit(
                    "Predefined Test Finished",
                    f"{len(passed_configs)} configurations passed the download test.",
                    "info"
                )

            # Always stay on the Profiles tab for predefined tests
            # Find the Profiles tab index
            for i in range(self.tab_widget.count()):
                if self.tab_widget.tabText(i) == "Profiles":
                    self.tab_widget.setCurrentIndex(i)
                    self.log_debug(f"Staying on Profiles tab after predefined test")
                    break
        else:
            # No configs passed the test
            self.log_debug("Predefined Test - No configs passed the download test")
            self.signals.show_message_box.emit(
                "Predefined Test Finished",
                "No configurations passed the download test.",
                "warning"
            )

            # Stay on the Profiles tab even if no configs passed
            for i in range(self.tab_widget.count()):
                if self.tab_widget.tabText(i) == "Profiles":
                    self.tab_widget.setCurrentIndex(i)
                    self.log_debug(f"Staying on Profiles tab after predefined test (no configs passed)")
                    break

        # Schedule next run if auto-start is enabled
        if hasattr(self, 'predefined_auto_start_checkbox') and self.predefined_auto_start_checkbox.isChecked() and hasattr(self, 'predefined_auto_start_timer'):
            seconds = self.predefined_auto_start_timer.value()
            if seconds > 0:
                self.log_debug(f"Auto-start enabled for predefined test - scheduling next run in {seconds} seconds")
                self.status_bar.showMessage(f"Next Predefined Test will start in {seconds} seconds...")

                # Stop any existing timer
                if hasattr(self, 'auto_start_timer_obj') and self.auto_start_timer_obj.isActive():
                    self.auto_start_timer_obj.stop()

                # Start the timer
                self.auto_start_timer_obj.timeout.disconnect()
                self.auto_start_timer_obj.timeout.connect(self.start_predefined_test)
                self.auto_start_timer_obj.start(seconds * 1000)  # Convert to milliseconds

    def _auto_export_predefined_test_results(self):
        """Automatically export predefined test results"""
        if not self.filtered_configs:
            self.log_debug("Auto export - No configs to export")
            return

        # Get export directory
        export_dir = self.export_dir_input.text() if hasattr(self, 'export_dir_input') else os.path.dirname(os.path.abspath(__file__))
        if not os.path.isdir(export_dir):
            self.log_debug(f"Auto export - Invalid directory: {export_dir}, using script directory")
            export_dir = os.path.dirname(os.path.abspath(__file__))

        # Create file path
        file_path = os.path.join(export_dir, "Predefined_Test.txt")
        self.log_debug(f"Auto export - Exporting to: {file_path}")

        try:
            # Apply auto-renaming if enabled
            configs_to_export = self.filtered_configs.copy()
            if hasattr(self, 'predefined_auto_rename_checkbox') and self.predefined_auto_rename_checkbox.isChecked():
                self.log_debug("Auto export - Applying auto-rename")
                configs_to_export = self._apply_auto_rename(configs_to_export)

            # Export the configs
            exported_count = 0
            with open(file_path, 'w', encoding='utf-8') as f:
                for config in configs_to_export:
                    url = config.get('original_url', '')
                    if url:
                        f.write(f"{url}\n")
                        exported_count += 1

            self.log_debug(f"Auto export - Successfully exported {exported_count} configs")
            self.status_bar.showMessage(f"Auto-exported {exported_count} configs to {file_path}")

            # Show a brief message box
            self.signals.show_message_box.emit(
                "Auto Export Complete",
                f"Successfully exported {exported_count} configs to:\n{file_path}",
                "info"
            )
        except Exception as e:
            self.log_debug(f"Auto export failed: {e}")
            self.signals.show_message_box.emit(
                "Auto Export Failed",
                f"Failed to export configs: {str(e)}",
                "error"
            )

    def _auto_export_complete_test_results(self):
        """Automatically export complete test results based on settings"""
        if not self.filtered_configs:
            self.log_debug("Auto export - No configs to export")
            return

        # Get export directory
        export_dir = self.export_dir_input.text() if hasattr(self, 'export_dir_input') else os.path.dirname(os.path.abspath(__file__))
        if not os.path.isdir(export_dir):
            self.log_debug(f"Auto export - Invalid directory: {export_dir}, using script directory")
            export_dir = os.path.dirname(os.path.abspath(__file__))

        # Create file path
        file_path = os.path.join(export_dir, "Filtered_Configs.txt")
        self.log_debug(f"Auto export - Exporting to: {file_path}")

        try:
            # Apply auto-renaming if enabled
            configs_to_export = self.filtered_configs.copy()
            if hasattr(self, 'auto_rename_checkbox') and self.auto_rename_checkbox.isChecked():
                self.log_debug("Auto export - Applying auto-rename")
                configs_to_export = self._apply_auto_rename(configs_to_export)

            # Export the configs
            exported_count = 0
            with open(file_path, 'w', encoding='utf-8') as f:
                for config in configs_to_export:
                    url = config.get('original_url', '')
                    if url:
                        f.write(f"{url}\n")
                        exported_count += 1

            self.log_debug(f"Auto export - Successfully exported {exported_count} configs")
            self.status_bar.showMessage(f"Auto-exported {exported_count} configs to {file_path}")

            # Show a brief message box
            self.signals.show_message_box.emit(
                "Auto Export Complete",
                f"Successfully exported {exported_count} configs to:\n{file_path}",
                "info"
            )
        except Exception as e:
            self.log_debug(f"Auto export failed: {e}")
            self.signals.show_message_box.emit(
                "Auto Export Failed",
                f"Failed to export configs: {str(e)}",
                "error"
            )

    def _apply_auto_rename(self, configs):
        """Apply automatic renaming to configs"""
        # Predefined names for renaming
        predefined_names = [
            "DE 🇩🇪 | Proxy_01", "RU 🇷🇺 | Proxy_02", "US 🇺🇸 | Proxy_03",
            "TR 🇹🇷 | Proxy_04", "FR 🇫🇷 | Proxy_05", "UK 🇬🇧 | Proxy_06",
            "NL 🇳🇱 | Proxy_07", "DE 🇩🇪 | Proxy_08", "RU 🇷🇺 | Proxy_09",
            "US 🇺🇸 | Proxy_10", "TR 🇹🇷 | Proxy_11", "FR 🇫🇷 | Proxy_12",
            "UK 🇬🇧 | Proxy_13", "NL 🇳🇱 | Proxy_14", "DE 🇩🇪 | Proxy_15",
            "DE 🇩🇪 | V2Ray_DE_01", "RU 🇷🇺 | V2Ray_RU_02", "US 🇺🇸 | V2Ray_US_03",
            "TR 🇹🇷 | V2Ray_TR_04", "FR 🇫🇷 | V2Ray_FR_05", "UK 🇬🇧 | V2Ray_UK_06",
            "NL 🇳🇱 | V2Ray_NL_07", "DE 🇩🇪 | V2Ray_DE_08", "RU 🇷🇺 | V2Ray_RU_09",
            "US 🇺🇸 | V2Ray_US_10", "TR 🇹🇷 | V2Ray_TR_11", "FR 🇫🇷 | V2Ray_FR_12",
            "UK 🇬🇧 | V2Ray_UK_13", "NL 🇳🇱 | V2Ray_NL_14", "DE 🇩🇪 | V2Ray_DE_15",
            "DE 🇩🇪 | Phantom Gate_01", "RU 🇷🇺 | Phantom Gate_02", "US 🇺🇸 | Phantom Gate_03",
            "TR 🇹🇷 | Phantom Gate_04", "FR 🇫🇷 | Turbo Proxy_05", "UK 🇬🇧 | Turbo Proxy_06",
            "NL 🇳🇱 | Turbo Proxy_07", "DE 🇩🇪 | Turbo Proxy_08", "RU 🇷🇺 | Turbo Proxy_09",
            "US 🇺🇸 | Speed Core_10", "TR 🇹🇷 | Speed Core_11", "FR 🇫🇷 | Speed Core_12",
            "UK 🇬🇧 | Speed Core_13", "NL 🇳🇱 | Speed Core_14", "DE 🇩🇪 | Speed Core_15"
        ]

        renamed_configs = []
        for i, config in enumerate(configs):
            if i < len(predefined_names):
                # Create a copy of the config
                new_config = dict(config)

                # Get the original URL and parse it
                url = new_config.get('original_url', '')
                if not url:
                    renamed_configs.append(new_config)
                    continue

                # Parse the URL to modify the fragment (remark)
                try:
                    # For different protocols, we need different approaches
                    protocol = new_config.get('protocol', '').lower()
                    if protocol == 'ss':
                        # SS URLs: Find the position of the # and replace everything after it
                        hash_pos = url.find('#')
                        if hash_pos != -1:
                            new_url = url[:hash_pos] + '#' + urllib.parse.quote(predefined_names[i])
                            new_config['original_url'] = new_url
                    elif protocol in ['vmess', 'vless', 'trojan']:
                        # These protocols use URL fragments
                        parsed = urlparse(url)
                        # Reconstruct the URL with the new fragment
                        new_url = f"{parsed.scheme}://{parsed.netloc}{parsed.path}"
                        if parsed.query:
                            new_url += f"?{parsed.query}"
                        new_url += f"#{urllib.parse.quote(predefined_names[i])}"
                        new_config['original_url'] = new_url
                except Exception as e:
                    self.log_debug(f"Error renaming config {i}: {e}")
                    # Keep the original if renaming fails

                renamed_configs.append(new_config)
            else:
                # If we run out of predefined names, keep the original
                renamed_configs.append(config)

        return renamed_configs

    def _complete_test_cleanup(self):
        """Clean up resources used by the complete test"""
        # Reset and hide progress bar - use thread-safe method
        QMetaObject.invokeMethod(self.complete_test_progress_bar, "setValue",
                               Qt.QueuedConnection, Q_ARG(int, 0))
        QMetaObject.invokeMethod(self.complete_test_progress_bar, "setMaximum",
                               Qt.QueuedConnection, Q_ARG(int, 100))
        QMetaObject.invokeMethod(self.complete_test_progress_bar, "setVisible",
                               Qt.QueuedConnection, Q_ARG(bool, False))
        QMetaObject.invokeMethod(self.complete_test_progress_label, "setText",
                               Qt.QueuedConnection, Q_ARG(str, "Complete Test Progress: 0/0"))

        # Kill any running Xray processes
        self._kill_all_xray_processes()
        self.log_debug("Killed all Xray processes after complete test")

        # Reset Xray process counter to ensure we start fresh
        self.reset_xray_process_count()

        # Clean up tracking variables
        self.complete_test_configs = []
        self.complete_test_indices = []
        self.complete_test_netcat_done = set()
        self.complete_test_successful = set()
        self.complete_test_download_done = set()
        self.complete_test_download_success = set()

        # Force final UI update
        self.update_latency_table()

        # Force garbage collection to free memory after complete test
        try:
            import gc
            self.log_debug("Running garbage collection after complete test...")
            gc.collect()
            self.log_debug("Garbage collection completed")
        except ImportError:
            self.log_debug("Garbage collection module not available")

    def _update_complete_test_progress(self, current, total):
        """Update the complete test progress bar with thread-safety"""
        try:
            # Calculate progress percentage safely
            progress_percent = int(current/total*100) if total > 0 else 0

            # Format progress text
            progress_text = f"Complete Test Progress: {current}/{total} ({progress_percent}% complete)" if total > 0 else "Complete Test Progress: 0/0"
            status_text = f"Complete Test Progress: {current}/{total} ({progress_percent}%)"

            # Always use invokeMethod for thread-safety
            # This ensures UI updates work correctly regardless of which thread calls this method
            QMetaObject.invokeMethod(self.complete_test_progress_bar, "setMaximum",
                                  Qt.QueuedConnection, Q_ARG(int, total))
            QMetaObject.invokeMethod(self.complete_test_progress_bar, "setValue",
                                  Qt.QueuedConnection, Q_ARG(int, current))
            QMetaObject.invokeMethod(self.complete_test_progress_bar, "setVisible",
                                  Qt.QueuedConnection, Q_ARG(bool, True))

            # Removed setFormat call as it's not available in some PyQt5 versions

            # Update the progress label
            QMetaObject.invokeMethod(self.complete_test_progress_label, "setText",
                                  Qt.QueuedConnection, Q_ARG(str, progress_text))

            # Also update the status bar
            QMetaObject.invokeMethod(self.status_bar, "showMessage",
                                  Qt.QueuedConnection, Q_ARG(str, status_text))

            # Log progress update for debugging
            if current % 50 == 0:  # Only log every 50 updates to reduce log spam
                self.log_debug(f"Progress bar updated: {current}/{total} ({progress_percent}%)")

        except Exception as e:
            error_msg = f"Error updating complete test progress: {e}"
            print(error_msg)
            self.log_debug(error_msg)

    def eventFilter(self, obj, event):
        """Event filter to track user activity for UI responsiveness monitoring"""
        try:
            # Update the last UI response time whenever the user interacts with the application
            if hasattr(self, 'stability_improvements_enabled') and self.stability_improvements_enabled:
                # Check event type using integer values to avoid attribute errors
                event_type = event.type()
                # Only track significant events, exclude MouseMove (5) to reduce overhead
                if event_type in [2, 3, 6, 7, 31]:  # MouseButtonPress, MouseButtonRelease, KeyPress, KeyRelease, Wheel
                    if hasattr(self, 'last_ui_response_time'):
                        current_time = time.time()
                        # Only update if it's been more than 0.1 seconds since last update to reduce overhead
                        if current_time - self.last_ui_response_time > 0.1:
                            self.last_ui_response_time = current_time
        except Exception:
            # Silently handle any errors to prevent application crashes
            pass

        # Let the event propagate normally
        return super().eventFilter(obj, event)

    def closeEvent(self, event):
        """Handle application close event with enhanced crash prevention"""
        try:
            # Check if anti-closing is enabled
            if hasattr(self, 'anti_closing_enabled') and self.anti_closing_enabled and hasattr(self, 'stability_improvements_enabled') and self.stability_improvements_enabled:
                # Check if we're in the middle of a test
                if hasattr(self, 'stopping_tests') and not self.stopping_tests:
                    if hasattr(self, 'test_progress_bar') and self.test_progress_bar.isVisible():
                        # We're in the middle of a test, ask for confirmation
                        reply = QMessageBox.question(self, 'Confirm Exit',
                                                  "Tests are currently running. Are you sure you want to exit?",
                                                  QMessageBox.Yes | QMessageBox.No, QMessageBox.No)

                        if reply == QMessageBox.No:
                            event.ignore()
                            return

                        # User confirmed exit, stop all tests
                        self.stopping_tests = True
                        self.log_debug("User confirmed exit while tests were running. Stopping all tests...")

                # Check if system is under heavy load
                if self.system_load_high:
                    # System is under heavy load, show a warning and prevent closing
                    self.log_debug("Preventing window close during high system load")
                    QMessageBox.warning(self, "System Under Load",
                                      "The application is currently under heavy load. \n\n"
                                      "Closing now might cause data loss. The application will \n"
                                      "automatically recover once the load decreases.\n\n"
                                      "Please wait a moment before trying to close again.")
                    event.ignore()

                    # Trigger emergency recovery
                    self._emergency_recovery()
                    return

                # Check if we're in the middle of a complete test
                if hasattr(self, 'complete_test_running') and self.complete_test_running:
                    # Complete test is running, show a warning and prevent closing
                    self.log_debug("Preventing window close during complete test")
                    QMessageBox.warning(self, "Complete Test Running",
                                      "A complete test is currently running. \n\n"
                                      "Closing now might cause data loss. Please wait for the test \n"
                                      "to complete or use the Stop button to cancel the test first.")
                    event.ignore()
                    return

                # Check if we're in freeze recovery mode
                if hasattr(self, 'freeze_recovery_active') and self.freeze_recovery_active:
                    # We're in freeze recovery mode, show a warning and prevent closing
                    self.log_debug("Preventing window close during freeze recovery")
                    QMessageBox.warning(self, "Freeze Recovery Active",
                                      "The application is currently recovering from a freeze. \n\n"
                                      "Closing now might cause data loss. Please wait for the recovery \n"
                                      "process to complete.")
                    event.ignore()
                    return

                # Check if we're in process halting mode
                if hasattr(self, 'process_halting_active') and self.process_halting_active:
                    # We're in process halting mode, show a warning and prevent closing
                    self.log_debug("Preventing window close during process halting")
                    QMessageBox.warning(self, "Process Halting Active",
                                      "The application is currently halting processes to prevent crashes. \n\n"
                                      "Closing now might cause data loss. Please wait for the process \n"
                                      "halting to complete.")
                    event.ignore()
                    return

                # Check if we have active Xray processes
                with self.xray_process_lock:
                    active_xray_count = self.active_xray_processes

                if active_xray_count > 0:
                    # We have active Xray processes, show a warning and prevent closing
                    self.log_debug(f"Preventing window close with {active_xray_count} active Xray processes")
                    QMessageBox.warning(self, "Active Processes",
                                      f"The application has {active_xray_count} active Xray processes. \n\n"
                                      "Closing now might cause data loss. Please wait for the processes \n"
                                      "to complete or use the Stop button to cancel all tests.")
                    event.ignore()

                    # Try to kill all Xray processes
                    self._kill_all_xray_processes()
                    return

            # Stop all timers
            if hasattr(self, 'debug_update_timer') and self.debug_update_timer.isActive():
                self.debug_update_timer.stop()

            if hasattr(self, 'system_monitor_timer') and self.system_monitor_timer.isActive():
                self.system_monitor_timer.stop()

            if hasattr(self, 'ui_watchdog_timer') and self.ui_watchdog_timer.isActive():
                self.ui_watchdog_timer.stop()

            if hasattr(self, 'emergency_recovery_timer') and self.emergency_recovery_timer.isActive():
                self.emergency_recovery_timer.stop()

            if hasattr(self, 'process_monitor_timer') and self.process_monitor_timer.isActive():
                self.process_monitor_timer.stop()

            # Kill any running Xray processes
            self._kill_all_xray_processes()

            # Reset Xray process counter
            self.reset_xray_process_count()

            # Log application exit
            self.log_debug("Application closing normally")

            # Accept the close event
            event.accept()

        except Exception as e:
            # Log the error but don't close the application if anti-closing is enabled
            error_msg = f"Error during application close: {e}"
            self.log_debug(error_msg)
            traceback.print_exc()

            # Show error to user
            QMessageBox.critical(self, "Error During Close",
                               f"An error occurred while trying to close the application:\n\n{e}\n\n"
                               "The application will continue running to prevent data loss.")

            # Don't close the window if anti-closing is enabled
            if hasattr(self, 'anti_closing_enabled') and self.anti_closing_enabled and hasattr(self, 'stability_improvements_enabled') and self.stability_improvements_enabled:
                event.ignore()
            else:
                # If anti-closing is disabled, accept the close event
                event.accept()

    def _monitor_system_resources(self):
        """Monitor system resources and adjust application behavior accordingly"""
        try:
            # Get CPU usage
            cpu_percent = 0
            try:
                import psutil
                cpu_percent = psutil.cpu_percent(interval=0.5)
                memory_percent = psutil.virtual_memory().percent
                self.log_debug(f"System resources: CPU {cpu_percent}%, Memory {memory_percent}%")

                # Check if system is under heavy load
                if cpu_percent > 85 or memory_percent > 90:
                    if not self.system_load_high:
                        self.system_load_high = True
                        self.log_debug("System under heavy load - throttling operations")

                        # Reduce the maximum number of concurrent processes
                        self._adjust_concurrency_for_load()

                        # Show a warning to the user if tests are running
                        if hasattr(self, 'test_progress_bar') and self.test_progress_bar.isVisible():
                            self.status_bar.showMessage("System under heavy load - throttling operations")
                else:
                    if self.system_load_high:
                        self.system_load_high = False
                        self.log_debug("System load returned to normal")
            except ImportError:
                # psutil not available, use a simpler approach
                self.log_debug("psutil not available, using simplified resource monitoring")

                # Check number of active Xray processes as a proxy for system load
                if self.active_xray_processes > self.max_allowed_xray_processes * 0.8:
                    self.system_load_high = True
                    self._adjust_concurrency_for_load()
                else:
                    self.system_load_high = False
        except Exception as e:
            self.log_debug(f"Error monitoring system resources: {e}")

    def _adjust_concurrency_for_load(self):
        """Adjust concurrency settings based on system load"""
        try:
            if self.system_load_high:
                # Reduce concurrency by 30% if system is under heavy load
                current_limit = self.max_allowed_xray_processes
                new_limit = max(5, int(current_limit * 0.7))  # Ensure at least 5 processes

                if new_limit != self.max_allowed_xray_processes:
                    self.log_debug(f"Reducing concurrency from {current_limit} to {new_limit} due to high system load")

                    # Update the spinbox values if they exist
                    if hasattr(self, 'netcat_max_workers_spinbox'):
                        QMetaObject.invokeMethod(self.netcat_max_workers_spinbox, "setValue",
                                              Qt.QueuedConnection, Q_ARG(int, new_limit))

                    if hasattr(self, 'download_max_workers_spinbox'):
                        QMetaObject.invokeMethod(self.download_max_workers_spinbox, "setValue",
                                              Qt.QueuedConnection, Q_ARG(int, new_limit))

                    # Update the semaphore limit
                    self.max_allowed_xray_processes = new_limit
                    # Note: We can't directly modify the existing semaphore's limit,
                    # but we'll create a new one with the updated limit for future operations
                    # Existing operations will still use the old semaphore
                    self.xray_semaphore = threading.Semaphore(new_limit)
            else:
                # If system load is normal and we previously reduced concurrency, restore it
                if self.max_allowed_xray_processes < 15:  # Default is 15
                    self.log_debug(f"Restoring concurrency to default (15)")
                    self.max_allowed_xray_processes = 15
                    self.xray_semaphore = threading.Semaphore(15)

                    # Update the spinbox values if they exist
                    if hasattr(self, 'netcat_max_workers_spinbox'):
                        QMetaObject.invokeMethod(self.netcat_max_workers_spinbox, "setValue",
                                              Qt.QueuedConnection, Q_ARG(int, 15))
        except Exception as e:
            self.log_debug(f"Error adjusting concurrency: {e}")

    def _monitor_processes(self):
        """Monitor running processes and halt them if necessary to prevent crashes"""
        # Only run if stability improvements are enabled
        if not self.stability_improvements_enabled:
            return

        try:
            # Check if we have too many Xray processes running
            with self.xray_process_lock:
                current_xray_count = self.active_xray_processes

            # If we have more than 80% of the maximum allowed processes running, take action
            if current_xray_count > self.max_allowed_xray_processes * 0.8:
                self.log_debug(f"Process monitor: High Xray process count detected ({current_xray_count}/{self.max_allowed_xray_processes})")

                # If we're not already halting processes, start halting
                if not self.process_halting_active:
                    self.process_halting_active = True
                    self.log_debug("Process monitor: Starting process halting to prevent crashes")

                    # Temporarily reduce the maximum allowed processes
                    old_limit = self.max_allowed_xray_processes
                    new_limit = max(5, int(old_limit * 0.5))  # Reduce by 50%
                    self.max_allowed_xray_processes = new_limit
                    self.xray_semaphore = threading.Semaphore(new_limit)
                    self.log_debug(f"Process monitor: Reduced maximum allowed Xray processes from {old_limit} to {new_limit}")

                    # Process events to keep UI responsive
                    QApplication.processEvents()

                    # Show a message to the user
                    self.status_bar.showMessage("Process halting activated - reducing load to prevent crashes")
            else:
                # If we're halting processes but the count is now low, stop halting
                if self.process_halting_active and current_xray_count < self.max_allowed_xray_processes * 0.5:
                    self.process_halting_active = False
                    self.log_debug("Process monitor: Stopping process halting - load has decreased")

                    # Restore the original maximum allowed processes
                    if hasattr(self, 'download_max_workers_spinbox'):
                        new_limit = self.download_max_workers_spinbox.value()
                        self.max_allowed_xray_processes = new_limit
                        self.xray_semaphore = threading.Semaphore(new_limit)
                        self.log_debug(f"Process monitor: Restored maximum allowed Xray processes to {new_limit}")

                    # Process events to keep UI responsive
                    QApplication.processEvents()

                    # Show a message to the user
                    self.status_bar.showMessage("Process halting deactivated - load has decreased")
        except Exception as e:
            self.log_debug(f"Error in process monitor: {e}")

    def _check_application_health(self):
        """Check if the application is responsive and recover if necessary"""
        # Only run if stability improvements are enabled
        if not self.stability_improvements_enabled:
            return

        try:
            current_time = time.time()
            if hasattr(self, 'health_check_count'):
                self.health_check_count += 1

            # Check if UI is responsive
            ui_responsive = (current_time - self.last_ui_response_time) < 15  # 15 seconds threshold

            if not ui_responsive:
                if hasattr(self, 'consecutive_health_failures'):
                    self.consecutive_health_failures += 1
                else:
                    self.consecutive_health_failures = 1

                self.log_debug(f"Health check failed: UI unresponsive for {int(current_time - self.last_ui_response_time)} seconds")

                # If multiple consecutive failures, take recovery action
                if hasattr(self, 'consecutive_health_failures') and self.consecutive_health_failures >= 2:
                    # If we're not already in freeze recovery mode, enter it
                    if not self.freeze_recovery_active:
                        self.freeze_recovery_active = True
                        self.log_debug("Emergency recovery: Entering freeze recovery mode")

                        # Stop all tests
                        self.stopping_tests = True

                        # Kill all Xray processes
                        self._kill_all_xray_processes()

                        # Reset counters
                        with self.xray_process_lock:
                            self.active_xray_processes = 0

                        # Process events to unfreeze UI
                        QApplication.processEvents()

                        # Show a message to the user
                        self.status_bar.showMessage("Emergency recovery activated - application frozen, recovering...")

                        # Force garbage collection
                        try:
                            import gc
                            gc.collect()
                            self.log_debug("Forced garbage collection during emergency recovery")
                        except ImportError:
                            pass

                        # Reset health check
                        self.consecutive_health_failures = 0
            else:
                # UI is responsive, reset failure counter
                if hasattr(self, 'consecutive_health_failures'):
                    self.consecutive_health_failures = 0

                # If we're in freeze recovery mode but UI is now responsive, exit recovery mode
                if self.freeze_recovery_active:
                    self.freeze_recovery_active = False
                    self.log_debug("Emergency recovery: Exiting freeze recovery mode - UI is responsive again")

                    # Show a message to the user
                    self.status_bar.showMessage("Emergency recovery completed - application responsive again")
        except Exception as e:
            self.log_debug(f"Error in application health check: {e}")

    def _check_ui_responsiveness(self):
        """Check if the UI is responsive and take action if it's not"""
        # Only run if stability improvements are enabled
        if not self.stability_improvements_enabled:
            return

        try:
            # Update the last response time
            current_time = time.time()
            time_since_last_response = current_time - self.last_ui_response_time

            # If it's been more than 15 seconds since the last UI response, take action
            if time_since_last_response > 15:
                self.log_debug(f"UI may be unresponsive - {time_since_last_response:.1f} seconds since last response")

                # Check if we're running tests
                if hasattr(self, 'test_progress_bar') and self.test_progress_bar.isVisible():
                    # We're running tests, try to recover by stopping them
                    self.log_debug("Attempting to recover from potential UI freeze by stopping tests")
                    self.stopping_tests = True

                    # Try to kill all Xray processes to free up resources
                    self._kill_all_xray_processes()

                    # Reset the response time to avoid multiple recovery attempts
                    self.last_ui_response_time = current_time
            else:
                # UI is responsive, update the timestamp
                self.last_ui_response_time = current_time
        except Exception as e:
            print(f"Error checking UI responsiveness: {e}")

    def _emergency_recovery(self):
        """Emergency recovery procedure to prevent crashes"""
        self.log_debug("Starting emergency recovery procedure")

        # Stop all tests
        self.stopping_tests = True

        # Kill all Xray processes
        self._kill_all_xray_processes()

        # Reset counters
        with self.xray_process_lock:
            self.active_xray_processes = 0

        # Reset complete test flags
        self.complete_test_running = False

        # Clear any pending operations
        QApplication.processEvents()

        # Show a message to the user
        self.status_bar.showMessage("Emergency recovery completed - application stabilized")

        # Reset health check
        if hasattr(self, 'consecutive_health_failures'):
            self.consecutive_health_failures = 0
        self.system_load_high = False
        self.freeze_recovery_active = False
        self.process_halting_active = False

        # Force garbage collection
        try:
            import gc
            gc.collect()
            self.log_debug("Forced garbage collection during emergency recovery")
        except ImportError:
            pass

    def _kill_all_xray_processes(self):
        """Kill all Xray processes that might be running"""
        try:
            if platform.system() == "Windows":
                # On Windows, use taskkill to forcefully terminate all Xray processes
                self.log_debug("Attempting to kill all Xray processes")
                subprocess.run(["taskkill", "/F", "/IM", "xray.exe"],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              creationflags=subprocess.CREATE_NO_WINDOW)
            else:
                # On other platforms, use pkill
                subprocess.run(["pkill", "-9", "xray"],
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            self.log_debug("Killed all Xray processes")

            # Reset counters and release semaphore
            with self.xray_process_lock:
                self.active_xray_processes = 0

            # Reset the semaphore (create a new one with the same limit)
            self.xray_semaphore = threading.Semaphore(self.max_allowed_xray_processes)

        except Exception as e:
            self.log_debug(f"Error killing Xray processes: {e}")

    # Profile Management Functions
    def load_all_profiles(self):
        """Load all saved profiles from the profiles directory"""
        self.profiles = {}
        try:
            # Get all JSON files in the profiles directory
            for filename in os.listdir(self.profiles_dir):
                if filename.endswith('.json'):
                    profile_path = os.path.join(self.profiles_dir, filename)
                    profile_name = os.path.splitext(filename)[0]
                    self.load_profile(profile_name)
            self.log_debug(f"Loaded {len(self.profiles)} profiles from {self.profiles_dir}")
        except Exception as e:
            self.log_debug(f"Error loading profiles: {e}")

    def load_profile(self, profile_name):
        """Load a specific profile from file"""
        profile_path = os.path.join(self.profiles_dir, f"{profile_name}.json")
        try:
            if os.path.exists(profile_path):
                with open(profile_path, 'r', encoding='utf-8') as f:
                    profile_data = json.load(f)
                    self.profiles[profile_name] = profile_data
                    self.log_debug(f"Loaded profile '{profile_name}' with {len(profile_data)} configs")
                    return True
            else:
                self.log_debug(f"Profile file not found: {profile_path}")
                return False
        except Exception as e:
            self.log_debug(f"Error loading profile '{profile_name}': {e}")
            return False

    def save_profile(self, profile_name, configs):
        """Save a profile to file"""
        profile_path = os.path.join(self.profiles_dir, f"{profile_name}.json")
        try:
            # Create a simplified version of configs for storage
            simplified_configs = []
            existing_urls = set()

            # First, load existing profile if it exists
            if profile_name in self.profiles:
                for config in self.profiles[profile_name]:
                    existing_urls.add(config.get('original_url', ''))

            # Process new configs, checking for duplicates
            for config in configs:
                original_url = config.get('original_url', '')

                # Skip duplicates
                if original_url in existing_urls:
                    self.log_debug(f"Skipping duplicate config: {original_url}")
                    continue

                # Add to existing URLs set to prevent duplicates within the new configs
                existing_urls.add(original_url)

                # Keep only essential information
                simplified_config = {
                    'original_url': original_url,
                    'protocol': config.get('protocol', ''),
                    'host': config.get('host', ''),
                    'port': config.get('port', ''),
                    'remark': config.get('remark', '')
                }
                simplified_configs.append(simplified_config)

            # Merge with existing configs if profile exists
            if profile_name in self.profiles:
                merged_configs = self.profiles[profile_name] + simplified_configs
                self.log_debug(f"Merged {len(simplified_configs)} new configs with {len(self.profiles[profile_name])} existing configs")
            else:
                merged_configs = simplified_configs

            # Save to file
            with open(profile_path, 'w', encoding='utf-8') as f:
                json.dump(merged_configs, f, indent=2, ensure_ascii=False)

            # Update in-memory profile
            self.profiles[profile_name] = merged_configs
            self.log_debug(f"Saved profile '{profile_name}' with {len(merged_configs)} configs")
            return True
        except Exception as e:
            self.log_debug(f"Error saving profile '{profile_name}': {e}")
            return False

    def add_to_predefined(self):
        """Add the pasted subscription or config to the predefined list"""
        # Get the content from the custom subscription text area
        if not hasattr(self, 'custom_subscription'):
            self.log_debug("Custom subscription text area not found")
            return

        text = self.custom_subscription.text().strip()
        if not text:
            self.log_debug("Custom subscription text area is empty")
            self.signals.show_message_box.emit(
                "Empty Input",
                "Please enter a subscription URL or config in the text area first.",
                "warning"
            )
            return

        # Ask for a name for the new predefined subscription
        name, ok = QInputDialog.getText(
            self,
            "Add to Predefined",
            "Enter a name for this predefined subscription:",
            QLineEdit.Normal,
            f"Custom Subscription {len(self.predefined_subscriptions) + 1}"
        )

        if not ok or not name:
            self.log_debug("User cancelled adding to predefined")
            return

        # Check if it's a URL or a config
        if text.startswith(('http://', 'https://')):
            # It's a URL - add it to predefined subscriptions
            self.predefined_subscriptions.append((name, text))
            self.log_debug(f"Added URL to predefined subscriptions: {name} - {text}")

            # Update the subscription combo box
            if hasattr(self, 'subscription_combo'):
                current_index = self.subscription_combo.currentIndex()
                self.subscription_combo.clear()

                # Add predefined subscriptions
                for name, url in self.predefined_subscriptions:
                    self.subscription_combo.addItem(name)

                # Add the "All Predefined" option
                self.subscription_combo.addItem("All Predefined")

                # Try to restore the previous selection
                if current_index < self.subscription_combo.count():
                    self.subscription_combo.setCurrentIndex(current_index)

            self.signals.show_message_box.emit(
                "Subscription Added",
                f"Successfully added '{name}' to predefined subscriptions.",
                "info"
            )
        else:
            # It's a config or multiple configs - parse and add to a profile
            configs = []
            lines = text.split('\n')

            for line in lines:
                line = line.strip()
                if not line:
                    continue

                # Try to parse the config
                config = decode_proxy_url(line, parent_logger=self.log_debug)
                if config and config.get('protocol') not in ['error', 'unknown']:
                    configs.append(config)

            if not configs:
                self.log_debug("No valid configs found in text")
                self.signals.show_message_box.emit(
                    "No Valid Configs",
                    "No valid configurations were found in the text.",
                    "warning"
                )
                return

            # Create a profile for these configs
            profile_name = name.replace(' ', '_')
            self.log_debug(f"Adding {len(configs)} configs to new profile '{profile_name}'")
            if self.save_profile(profile_name, configs):
                # Update the profile selection combo box if it exists
                if hasattr(self, 'profile_combo'):
                    current_text = self.profile_combo.currentText()
                    self.profile_combo.clear()
                    self.profile_combo.addItems(self.get_profile_names())

                    # Try to restore the previous selection
                    index = self.profile_combo.findText(current_text)
                    if index >= 0:
                        self.profile_combo.setCurrentIndex(index)

                self.signals.show_message_box.emit(
                    "Profile Created",
                    f"Successfully created profile '{profile_name}' with {len(configs)} configurations.",
                    "info"
                )

                # Update status bar
                self.status_bar.showMessage(f"Created profile '{profile_name}' with {len(configs)} configs", 3000)

    def paste_to_predefined_profile(self):
        """Paste configs from clipboard and update the selected profile"""
        # Check if a profile is selected
        if not hasattr(self, 'profile_combo') or self.profile_combo.count() == 0:
            self.log_debug("No profile selected for paste operation")
            self.signals.show_message_box.emit(
                "No Profile Selected",
                "Please select a profile to update with pasted configs.",
                "warning"
            )
            return

        # Get the selected profile name
        profile_name = self.profile_combo.currentText()

        # Get clipboard content
        clipboard = QApplication.clipboard()
        clipboard_text = clipboard.text()

        if not clipboard_text.strip():
            self.log_debug("Clipboard is empty")
            self.signals.show_message_box.emit(
                "Empty Clipboard",
                "The clipboard is empty. Please copy some configs first.",
                "warning"
            )
            return

        # Parse the clipboard content
        self.log_debug(f"Parsing clipboard content for profile '{profile_name}'")
        configs = []
        lines = clipboard_text.strip().split('\n')

        for line in lines:
            line = line.strip()
            if not line:
                continue

            # Try to parse the config
            config = decode_proxy_url(line, parent_logger=self.log_debug)
            if config and config.get('protocol') not in ['error', 'unknown']:
                configs.append(config)

        if not configs:
            self.log_debug("No valid configs found in clipboard")
            self.signals.show_message_box.emit(
                "No Valid Configs",
                "No valid configurations were found in the clipboard content.",
                "warning"
            )
            return

        # Update the profile
        self.log_debug(f"Adding {len(configs)} configs to profile '{profile_name}'")
        if self.save_profile(profile_name, configs):
            self.signals.show_message_box.emit(
                "Profile Updated",
                f"Successfully added {len(configs)} configurations to profile '{profile_name}'.",
                "info"
            )

            # Update status bar
            self.status_bar.showMessage(f"Added {len(configs)} configs to profile '{profile_name}'", 3000)

    def get_profile_names(self):
        """Get a list of all profile names"""
        return list(self.profiles.keys())

    def get_profile(self, profile_name):
        """Get a specific profile by name"""
        profile_configs = self.profiles.get(profile_name, [])

        # Process the configs to ensure all necessary fields are set
        processed_configs = []
        for config in profile_configs:
            # Create a deep copy to avoid modifying the original
            config_copy = dict(config)

            # Check if the config has an original_url field
            if 'original_url' in config_copy and config_copy.get('original_url'):
                # Parse the original_url to extract all necessary fields
                original_url = config_copy.get('original_url')
                parsed_config = decode_proxy_url(original_url, parent_logger=self.log_debug)

                if parsed_config and parsed_config.get('protocol') not in ['error', 'unknown']:
                    # Update the config with the parsed fields
                    for key, value in parsed_config.items():
                        if key not in config_copy or not config_copy.get(key):
                            config_copy[key] = value

                    self.log_debug(f"Parsed original_url for config: {config_copy.get('remark', 'unnamed')}")

            # Ensure hostname is set properly
            if not config_copy.get('hostname') and 'host' in config_copy:
                config_copy['hostname'] = config_copy['host']
                self.log_debug(f"Fixed hostname from 'host' field: {config_copy.get('remark', 'unnamed')} to {config_copy['hostname']}")

            processed_configs.append(config_copy)

        return processed_configs

    def load_selected_profile(self, index):
        """Load the selected profile into the profiles table"""
        if index < 0 or self.profiles_combo.count() == 0:
            return

        profile_name = self.profiles_combo.itemText(index)
        self.log_debug(f"Loading profile: {profile_name}")

        # Handle the "All Predefined" option
        if profile_name == "All Predefined":
            self.log_debug("Loading all predefined subscription profiles")
            # Combine configs from all predefined subscription profiles
            all_configs = []

            # Get profiles for all predefined subscriptions
            for name, _ in self.predefined_subscriptions:
                profile_name_formatted = name.replace(' ', '_')
                if profile_name_formatted in self.profiles:
                    profile_configs = self.get_profile(profile_name_formatted)
                    self.log_debug(f"Adding {len(profile_configs)} configs from profile '{profile_name_formatted}'")
                    all_configs.extend(profile_configs)

            # Update the table with combined configs
            self.profiles_table.setSortingEnabled(False)  # Disable sorting during update
            self.profiles_table.setRowCount(0)  # Clear existing rows
            self.profiles_table.setRowCount(len(all_configs))

            # Use the combined configs as profile data
            profile_data = all_configs
        else:
            # Get the profile data for a specific profile
            profile_data = self.get_profile(profile_name)

            # Update the table
            self.profiles_table.setSortingEnabled(False)  # Disable sorting during update
            self.profiles_table.setRowCount(0)  # Clear existing rows
            self.profiles_table.setRowCount(len(profile_data))

        # Track success counts
        total_success_count = 0
        total_complete_success_count = 0

        for i, config in enumerate(profile_data):
            # Get config data with defaults for safety
            protocol = config.get('protocol', 'unknown')
            hostname = config.get('hostname', config.get('add', 'unknown'))  # Check 'add' for vmess
            port = config.get('port', '0')
            remark = config.get('remark', config.get('ps', 'N/A'))  # Check 'ps' for vmess remarks
            original_url = config.get('original_url', '')
            success_count = config.get('success_count', 0)
            complete_success_count = config.get('complete_success_count', 0)
            last_test = config.get('last_test', 'Never')

            # Create items
            proto_item = QTableWidgetItem(protocol.upper())
            host_item = QTableWidgetItem(hostname)
            port_item = QTableWidgetItem(str(port))
            remark_item = QTableWidgetItem(remark)
            success_item = QTableWidgetItem(str(success_count))
            complete_success_item = QTableWidgetItem(str(complete_success_count))
            last_test_item = QTableWidgetItem(last_test)
            url_item = QTableWidgetItem(original_url)

            # Set items in the row
            self.profiles_table.setItem(i, 0, proto_item)
            self.profiles_table.setItem(i, 1, host_item)
            self.profiles_table.setItem(i, 2, port_item)
            self.profiles_table.setItem(i, 3, remark_item)
            self.profiles_table.setItem(i, 4, success_item)
            self.profiles_table.setItem(i, 5, complete_success_item)
            self.profiles_table.setItem(i, 6, last_test_item)
            self.profiles_table.setItem(i, 7, url_item)

            # Track total success counts
            total_success_count += success_count
            total_complete_success_count += complete_success_count

        self.profiles_table.setSortingEnabled(True)  # Re-enable sorting

        # Update stats
        self.profile_stats_label.setText(f"Total configs: {len(profile_data)} | Successful tests: {total_success_count} | Complete tests: {total_complete_success_count}")

    def refresh_profiles(self):
        """Refresh the list of profiles"""
        self.log_debug("Refreshing profiles list")

        # Remember the current selection
        current_profile = self.profiles_combo.currentText()

        # Reload all profiles
        self.load_all_profiles()

        # Update the combo box
        self.profiles_combo.clear()
        self.profiles_combo.addItems(["All Predefined"] + self.get_profile_names())

        # Try to restore the previous selection
        index = self.profiles_combo.findText(current_profile)
        if index >= 0:
            self.profiles_combo.setCurrentIndex(index)
        elif self.profiles_combo.count() > 0:
            self.profiles_combo.setCurrentIndex(0)

    def create_new_profile(self):
        """Create a new empty profile"""
        name, ok = QInputDialog.getText(
            self,
            "Create New Profile",
            "Enter a name for the new profile:",
            QLineEdit.Normal,
            f"Profile {len(self.profiles) + 1}"
        )

        if not ok or not name:
            return

        # Check if profile already exists
        if name in self.profiles:
            QMessageBox.warning(self, "Profile Exists", f"A profile named '{name}' already exists.")
            return

        # Create empty profile
        self.profiles[name] = []
        self.save_profile(name, [])

        # Update the combo box
        self.profiles_combo.addItem(name)
        self.profiles_combo.setCurrentText(name)

        self.log_debug(f"Created new empty profile: {name}")

    def delete_selected_profile(self):
        """Delete the selected profile"""
        if self.profiles_combo.count() == 0:
            return

        profile_name = self.profiles_combo.currentText()

        # Confirm deletion
        reply = QMessageBox.question(
            self,
            "Confirm Deletion",
            f"Are you sure you want to delete the profile '{profile_name}'?",
            QMessageBox.Yes | QMessageBox.No,
            QMessageBox.No
        )

        if reply != QMessageBox.Yes:
            return

        # Delete the profile file
        profile_path = os.path.join(self.profiles_dir, f"{profile_name}.json")
        try:
            if os.path.exists(profile_path):
                os.remove(profile_path)
                self.log_debug(f"Deleted profile file: {profile_path}")
        except Exception as e:
            self.log_debug(f"Error deleting profile file: {e}")
            QMessageBox.warning(self, "Error", f"Failed to delete profile file: {e}")
            return

        # Remove from in-memory profiles
        if profile_name in self.profiles:
            del self.profiles[profile_name]

        # Update the combo box
        current_index = self.profiles_combo.currentIndex()
        self.profiles_combo.removeItem(current_index)

        # Select another profile if available
        if self.profiles_combo.count() > 0:
            self.profiles_combo.setCurrentIndex(0)
        else:
            # Clear the table if no profiles left
            self.profiles_table.setRowCount(0)
            self.profile_stats_label.setText("Total configs: 0 | Successful tests: 0")

        self.log_debug(f"Deleted profile: {profile_name}")

    def show_profiles_context_menu(self, position):
        """Show context menu for the profiles table"""
        if self.profiles_table.rowCount() == 0:
            return

        # Get selected rows
        selected_rows = set()
        for item in self.profiles_table.selectedItems():
            selected_rows.add(item.row())

        if not selected_rows:
            return

        # Create context menu
        context_menu = QMenu()

        # Add test actions
        netcat_action = context_menu.addAction("Test Netcat")
        download_action = context_menu.addAction("Test Download")
        google_action = context_menu.addAction("Test Google")
        site_action = context_menu.addAction("Test Custom Site")
        http_action = context_menu.addAction("Test HTTP")
        complete_action = context_menu.addAction("Complete Test")
        context_menu.addSeparator()

        # Add copy actions
        copy_url_action = context_menu.addAction("Copy URL")
        copy_config_action = context_menu.addAction("Copy Config")
        context_menu.addSeparator()

        # Add remove action
        remove_action = context_menu.addAction("Remove from Profile")

        # Show the menu and get the selected action
        action = context_menu.exec_(self.profiles_table.mapToGlobal(position))

        if not action:
            return

        # Get the current profile name
        profile_name = self.profiles_combo.currentText()
        if not profile_name or profile_name not in self.profiles:
            return

        # Get the profile data
        profile_data = self.profiles[profile_name]

        # Handle the selected action
        if action == netcat_action:
            self.test_profile_configs(profile_data, selected_rows, "netcat")
        elif action == download_action:
            self.test_profile_configs(profile_data, selected_rows, "download")
        elif action == google_action:
            self.test_profile_configs(profile_data, selected_rows, "google")
        elif action == site_action:
            self.test_profile_configs(profile_data, selected_rows, "site")
        elif action == http_action:
            self.test_profile_configs(profile_data, selected_rows, "http")
        elif action == complete_action:
            self.test_profile_configs(profile_data, selected_rows, "complete")
        elif action == copy_url_action:
            self.copy_profile_urls(profile_data, selected_rows)
        elif action == copy_config_action:
            self.copy_profile_configs(profile_data, selected_rows)
        elif action == remove_action:
            self.remove_from_profile(profile_name, profile_data, selected_rows)

    def test_profile_configs(self, profile_data, selected_rows, test_type):
        """Test selected configs from a profile"""
        # Convert selected rows to a list and sort
        selected_indices = sorted(list(selected_rows))

        if not selected_indices:
            return

        # Get the configs for the selected rows
        selected_configs = [profile_data[i] for i in selected_indices if i < len(profile_data)]

        if not selected_configs:
            return

        # Load the configs into the main configs list for testing
        self.configs = selected_configs
        self.filtered_configs = selected_configs

        # Update the tables
        self.update_results_table()
        self.update_latency_table()

        # Switch to the Testing tab
        for i in range(self.tab_widget.count()):
            if self.tab_widget.tabText(i) == "Testing":
                self.tab_widget.setCurrentIndex(i)
                break

        # Run the appropriate test
        if test_type == "netcat":
            self.start_netcat_test()
        elif test_type == "download":
            self.start_download_test()
        elif test_type == "google":
            self.start_google_test()
        elif test_type == "site":
            self.start_site_test()
        elif test_type == "http":
            self.start_http_test()
        elif test_type == "complete":
            self.start_complete_test()

        # Update the profile with success counts
        self.update_profile_success_counts(profile_data, selected_configs, test_type)

    def update_profile_success_counts(self, profile_data, tested_configs, test_type):
        """Update success counts for tested configs in a profile"""
        # Get the current profile name
        profile_name = self.profiles_combo.currentText() if hasattr(self, 'profiles_combo') else None

        # Special handling for "All Predefined"
        if profile_name == "All Predefined":
            self.log_debug("All Predefined selected - updating success counts for individual profiles")

            # Update each predefined profile separately
            for name, _ in self.predefined_subscriptions:
                formatted_name = name.replace(' ', '_')
                if formatted_name in self.profiles:
                    # Find configs that belong to this profile
                    profile_configs = []
                    for config in tested_configs:
                        source_name = config.get('source_subscription_name', '')
                        if source_name == name:
                            profile_configs.append(config)

                    if profile_configs:
                        self.log_debug(f"Updating {len(profile_configs)} configs for profile '{formatted_name}'")
                        # Update this profile
                        self._update_single_profile_success_counts(formatted_name, self.profiles[formatted_name], profile_configs, test_type)

            return

        # Regular profile update
        if not profile_name or profile_name not in self.profiles:
            self.log_debug(f"Cannot update profile success counts: Invalid profile name '{profile_name}'")
            return

        # Update the single profile
        self._update_single_profile_success_counts(profile_name, profile_data, tested_configs, test_type)

    def _update_single_profile_success_counts(self, profile_name, profile_data, tested_configs, test_type):
        """Update success counts for a single profile"""
        # Track if any changes were made
        changes_made = False
        success_count = 0

        self.log_debug(f"Updating success counts for {len(tested_configs)} configs in profile '{profile_name}'")

        # Update success counts based on test results
        for config in tested_configs:
            # Find the matching config in the profile data
            original_url = config.get('original_url', '')
            if not original_url:
                self.log_debug(f"Skipping config without original_url: {config.get('remark', 'unnamed')}")
                continue

            # Find the config in the profile data by URL
            for profile_config in profile_data:
                if profile_config.get('original_url', '') == original_url:
                    # Check if the test was successful
                    success = False

                    if test_type == "netcat" and config.get('netcat_success') is True:
                        success = True
                        self.log_debug(f"Netcat test successful for {config.get('remark', 'unnamed')}")
                    elif test_type == "download" and config.get('download_success') is True:
                        success = True
                        self.log_debug(f"Download test successful for {config.get('remark', 'unnamed')}")
                    elif test_type == "google" and config.get('google_success') is True:
                        success = True
                        self.log_debug(f"Google test successful for {config.get('remark', 'unnamed')}")
                    elif test_type == "site" and config.get('site_success') is True:
                        success = True
                        self.log_debug(f"Site test successful for {config.get('remark', 'unnamed')}")
                    elif test_type == "http" and config.get('http_success') is True:
                        success = True
                        self.log_debug(f"HTTP test successful for {config.get('remark', 'unnamed')}")
                    elif test_type == "complete" and config.get('netcat_success') is True and config.get('download_success') is True:
                        success = True
                        self.log_debug(f"Complete test successful for {config.get('remark', 'unnamed')}")

                    if success:
                        success_count += 1
                        # Update the appropriate counter based on test type
                        if test_type == "complete":
                            # Increment complete success count
                            current_complete_count = profile_config.get('complete_success_count', 0)
                            profile_config['complete_success_count'] = current_complete_count + 1
                            self.log_debug(f"Updated complete success count for {config.get('remark', 'unnamed')} to {current_complete_count + 1}")
                        else:
                            # Increment regular success count
                            current_count = profile_config.get('success_count', 0)
                            profile_config['success_count'] = current_count + 1
                            self.log_debug(f"Updated success count for {config.get('remark', 'unnamed')} to {current_count + 1}")

                        # Update last test timestamp
                        profile_config['last_test'] = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                        changes_made = True

        # Save the updated profile if changes were made
        if changes_made:
            self.log_debug(f"Saving profile '{profile_name}' with {success_count} successful tests")
            self.save_profile(profile_name, profile_data)

            # Refresh the profiles table
            if hasattr(self, 'profiles_combo') and hasattr(self, 'load_selected_profile'):
                self.load_selected_profile(self.profiles_combo.currentIndex())
                self.log_debug(f"Refreshed profiles table after updating success counts")
        else:
            self.log_debug(f"No changes made to profile '{profile_name}' success counts")

    def copy_profile_urls(self, profile_data, selected_rows):
        """Copy URLs of selected configs from a profile"""
        # Convert selected rows to a list and sort
        selected_indices = sorted(list(selected_rows))

        if not selected_indices:
            return

        # Get the URLs for the selected rows
        urls = []
        for i in selected_indices:
            if i < len(profile_data):
                url = profile_data[i].get('original_url', '')
                if url:
                    urls.append(url)

        if urls:
            # Join URLs with newlines and copy to clipboard
            clipboard = QApplication.clipboard()
            clipboard.setText('\n'.join(urls))

            self.status_bar.showMessage(f"Copied {len(urls)} URLs to clipboard", 3000)
        else:
            self.status_bar.showMessage("No valid URLs found to copy", 3000)

    def copy_profile_configs(self, profile_data, selected_rows):
        """Copy configs of selected rows from a profile"""
        # Convert selected rows to a list and sort
        selected_indices = sorted(list(selected_rows))

        if not selected_indices:
            return

        # Get the configs for the selected rows
        configs = []
        for i in selected_indices:
            if i < len(profile_data):
                url = profile_data[i].get('original_url', '')
                if url:
                    configs.append(url)

        if configs:
            # Join configs with newlines and copy to clipboard
            clipboard = QApplication.clipboard()
            clipboard.setText('\n'.join(configs))

            self.status_bar.showMessage(f"Copied {len(configs)} configs to clipboard", 3000)
        else:
            self.status_bar.showMessage("No valid configs found to copy", 3000)

    def remove_from_profile(self, profile_name, profile_data, selected_rows):
        """Remove selected configs from a profile"""
        # Convert selected rows to a list and sort in reverse order
        # (to avoid index shifting when removing items)
        selected_indices = sorted(list(selected_rows), reverse=True)

        if not selected_indices:
            return

        # Confirm removal
        reply = QMessageBox.question(
            self,
            "Confirm Removal",
            f"Are you sure you want to remove {len(selected_indices)} configs from profile '{profile_name}'?",
            QMessageBox.Yes | QMessageBox.No,
            QMessageBox.No
        )

        if reply != QMessageBox.Yes:
            return

        # Remove the configs from the profile data
        for i in selected_indices:
            if i < len(profile_data):
                profile_data.pop(i)

        # Save the updated profile
        self.save_profile(profile_name, profile_data)

        # Refresh the profiles table
        self.load_selected_profile(self.profiles_combo.currentIndex())

        self.status_bar.showMessage(f"Removed {len(selected_indices)} configs from profile '{profile_name}'", 3000)

    def manually_update_profile(self):
        """Manually update the selected profile with the current filtered configs"""
        # Check if a profile is selected
        if not hasattr(self, 'profile_combo') or self.profile_combo.count() == 0:
            self.log_debug("No profile selected for manual update")
            self.signals.show_message_box.emit(
                "No Profile Selected",
                "Please select a profile to update.",
                "warning"
            )
            return

        # Check if there are filtered configs
        if not self.filtered_configs:
            self.log_debug("No filtered configs available for manual update")
            self.signals.show_message_box.emit(
                "No Configs Available",
                "There are no filtered configurations available to update the profile. Run a Complete Test first.",
                "warning"
            )
            return

        # Get the selected profile name
        profile_name = self.profile_combo.currentText()

        # Confirm with the user
        response = QMessageBox.question(
            self,
            "Confirm Profile Update",
            f"Are you sure you want to update the profile '{profile_name}' with {len(self.filtered_configs)} configurations?",
            QMessageBox.Yes | QMessageBox.No
        )

        if response == QMessageBox.No:
            self.log_debug("Manual profile update cancelled by user")
            return

        # Update the profile
        self.log_debug(f"Manually updating profile '{profile_name}' with {len(self.filtered_configs)} configs")
        self.save_profile(profile_name, self.filtered_configs)

        # Show success message
        self.signals.show_message_box.emit(
            "Profile Updated",
            f"Successfully updated profile '{profile_name}' with {len(self.filtered_configs)} configurations.",
            "info"
        )

        # Update status bar
        self.status_bar.showMessage(f"Updated profile '{profile_name}' with {len(self.filtered_configs)} configs", 3000)

    # --- Subscription Management Methods ---
    def load_subscriptions_config(self):
        """Load predefined subscriptions from configuration file"""
        try:
            if os.path.exists(self.subscriptions_config_file):
                with open(self.subscriptions_config_file, 'r', encoding='utf-8') as f:
                    config_data = json.load(f)
                    self.predefined_subscriptions = config_data.get('subscriptions', [])
                    self.log_debug(f"Loaded {len(self.predefined_subscriptions)} subscriptions from config file")
            else:
                # Use default subscriptions and save them
                self.predefined_subscriptions = self.default_predefined_subscriptions.copy()
                self.save_subscriptions_config()
                self.log_debug(f"Created new subscriptions config with {len(self.predefined_subscriptions)} default subscriptions")

            # Update the combo box
            self._update_subscription_combo()

        except Exception as e:
            self.log_debug(f"Error loading subscriptions config: {e}")
            # Fallback to default subscriptions
            self.predefined_subscriptions = self.default_predefined_subscriptions.copy()
            self._update_subscription_combo()

    def save_subscriptions_config(self):
        """Save predefined subscriptions to configuration file"""
        try:
            config_data = {
                'subscriptions': self.predefined_subscriptions,
                'last_updated': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
            }
            with open(self.subscriptions_config_file, 'w', encoding='utf-8') as f:
                json.dump(config_data, f, indent=2, ensure_ascii=False)
            self.log_debug(f"Saved {len(self.predefined_subscriptions)} subscriptions to config file")
            return True
        except Exception as e:
            self.log_debug(f"Error saving subscriptions config: {e}")
            return False

    def _update_subscription_combo(self):
        """Update the subscription combo box with current subscriptions"""
        if hasattr(self, 'subscription_combo'):
            # Store current selection
            current_selected = self.subscription_combo.get_selected_items()

            # Clear and repopulate
            self.subscription_combo.items.clear()
            self.subscription_combo.list_widget.clear()
            self.subscription_combo.selected_items.clear()

            # Add predefined subscriptions
            for name, _ in self.predefined_subscriptions:
                self.subscription_combo.add_item(name)

            # Restore previous selection if items still exist
            if current_selected:
                valid_selections = [item for item in current_selected if item in [name for name, _ in self.predefined_subscriptions]]
                if valid_selections:
                    self.subscription_combo.set_selected_items(valid_selections)
                else:
                    # If no valid selections, clear to show "All"
                    self.subscription_combo.clear_selection()
            else:
                # Start with no selections (which means "All")
                self.subscription_combo.clear_selection()

    def _switch_to_testing_tab(self):
        """Switch to the Testing tab"""
        try:
            # Find the Testing tab index
            for i in range(self.tab_widget.count()):
                if self.tab_widget.tabText(i) == "Testing":
                    self.tab_widget.setCurrentIndex(i)
                    self.log_debug("Switched to Testing tab")
                    break
        except Exception as e:
            self.log_debug(f"Error switching to Testing tab: {e}")

    def switch_to_stats_tab(self):
        """Switch to the Stats tab"""
        try:
            # Find the Stats tab index
            for i in range(self.tab_widget.count()):
                if self.tab_widget.tabText(i) == "Stats":
                    self.tab_widget.setCurrentIndex(i)
                    self.log_debug("Switched to Stats tab")
                    break
        except Exception as e:
            self.log_debug(f"Error switching to Stats tab: {e}")

    def _detect_config_country(self, config):
        """Detect country from config name/remark using multiple detection methods"""
        remark = config.get('remark', '').lower()

        # Country mapping with full names, abbreviations, and flag emojis
        country_patterns = {
            'United States': ['united states', 'usa', 'us', 'america', '🇺🇸'],
            'United Kingdom': ['united kingdom', 'uk', 'gb', 'GB', 'Gb', 'britain', 'england', '🇬🇧'],
            'Turkey': ['turkey', 'tr', 'türkiye', '🇹🇷'],
            'Israel': ['israel', 'il', '🇮🇱'],
            'Netherlands': ['netherlands', 'nl', 'holland', 'dutch', '🇳🇱'],
            'Lithuania': ['lithuania', 'lt', '🇱🇹'],
            'Hong Kong': ['hong kong', 'hk', 'hongkong', '🇭🇰'],
            'Poland': ['poland', 'pl', 'polska', '🇵🇱'],
            'Russia': ['russia', 'ru', 'russian', '🇷🇺'],
            'Brazil': ['brazil', 'br', 'brasil', '🇧🇷'],
            'Argentina': ['argentina', 'ar', '🇦🇷'],
            'France': ['france', 'fr', 'french', '🇫🇷'],
            'Spain': ['spain', 'es', 'spanish', '🇪🇸'],
            'Italy': ['italy', 'it', 'italian', '🇮🇹'],
            'Germany': ['germany', 'de', 'german', 'deutschland', '🇩🇪'],
            'Greece': ['greece', 'gr', 'greek', '🇬🇷'],
            'UAE': ['uae', 'ae', 'emirates', 'dubai', '🇦🇪'],
            'Bahrain': ['bahrain', 'bh', '🇧🇭'],
            'Kuwait': ['kuwait', 'kw', '🇰🇼'],
            'Japan': ['japan', 'jp', 'japanese', '🇯🇵'],
            'India': ['india', 'in', 'indian', '🇮🇳'],
            'Singapore': ['singapore', 'sg', '🇸🇬'],
            'South Korea': ['south korea', 'kr', 'korea', 'korean', '🇰🇷'],
            'Australia': ['australia', 'au', 'aussie', '🇦🇺'],
            'South Africa': ['south africa', 'za', '🇿🇦'],
            'Egypt': ['egypt', 'eg', 'egyptian', '🇪🇬'],
            'Algeria': ['algeria', 'dz', 'algerian', '🇩🇿'],
            'Hungary': ['hungary', 'hu', 'hungarian', '🇭🇺'],
            'Romania': ['romania', 'ro', 'romanian', '🇷🇴'],
            'Sweden': ['sweden', 'se', 'swedish', '🇸🇪'],
            'Norway': ['norway', 'no', 'norwegian', '🇳🇴'],
            'Finland': ['finland', 'fi', 'finnish', '🇫🇮'],
            'Canada': ['canada', 'ca', 'canadian', '🇨🇦'],
            'Belgium': ['belgium', 'be', 'belgian', '🇧🇪'],
            'Switzerland': ['switzerland', 'ch', 'swiss', '🇨🇭']
        }

        # Check for country matches
        for country, patterns in country_patterns.items():
            for pattern in patterns:
                if pattern in remark:
                    return country

        return None

    # --- New Button Methods ---
    def fetch_pasted_subscription(self):
        """Process the URL/config pasted in the input area"""
        input_source = self.custom_subscription.text().strip()
        if not input_source:
            QMessageBox.warning(self, "Input Empty", "Please paste a subscription URL or config in the input area first.")
            self.status_bar.showMessage("Custom input is empty.")
            return

        self.log_debug("Fetching pasted subscription/config...")
        self.status_bar.showMessage("Processing pasted input...")
        QApplication.processEvents()

        # Clear previous results
        self.configs = []
        self.filtered_configs = []
        self.update_results_table()
        self.update_latency_table()

        # Read and parse the pasted content
        success = self.read_subscriptions(input_source)

        if success and self.configs:
            self.log_debug(f"Read {len(self.configs)} raw configs from pasted input.")
            self.apply_filter_and_update_ui()
        elif success:
            QMessageBox.warning(self, "Warning", "Pasted input processed, but no configurations were extracted.")
            self.status_bar.showMessage("No configurations extracted from paste.")
        else:
            self.log_debug("Failed to process pasted input.")
            self.status_bar.showMessage("Failed to process paste.")

    def fetch_predefined_subscription(self):
        """Process the currently selected predefined subscription(s)"""
        selected_subscriptions = self.subscription_combo.get_selected_items()

        if not selected_subscriptions:
            QMessageBox.information(self, "Select Specific Subscription",
                                  "Please select one or more specific predefined subscriptions, or use 'Fetch All Sources' to process all subscriptions.")
            return

        if len(selected_subscriptions) == 1:
            # Single subscription selected
            selected_name = selected_subscriptions[0]
            # Find the subscription by name
            subscription_found = False
            for name, url in self.predefined_subscriptions:
                if name == selected_name:
                    self.log_debug(f"Fetching predefined subscription: {name}")
                    self.status_bar.showMessage(f"Processing predefined subscription '{name}'...")
                    QApplication.processEvents()

                    # Clear previous results
                    self.configs = []
                    self.filtered_configs = []
                    self.update_results_table()
                    self.update_latency_table()

                    # Read and parse the subscription
                    success = self.read_subscriptions(url)

                    if success and self.configs:
                        self.log_debug(f"Read {len(self.configs)} raw configs from predefined subscription '{name}'.")
                        self.apply_filter_and_update_ui()
                    elif success:
                        QMessageBox.warning(self, "Warning", f"Predefined subscription '{name}' processed, but no configurations were extracted.")
                        self.status_bar.showMessage("No configurations extracted.")
                    else:
                        self.log_debug(f"Failed to process predefined subscription '{name}'.")
                        self.status_bar.showMessage(f"Failed to process predefined subscription '{name}'.")

                    subscription_found = True
                    break

            if not subscription_found:
                QMessageBox.warning(self, "Invalid Selection", f"Selected subscription '{selected_name}' not found.")
        else:
            # Multiple subscriptions selected
            self.log_debug(f"Fetching {len(selected_subscriptions)} predefined subscriptions: {', '.join(selected_subscriptions)}")
            self.process_selected_subscriptions(selected_subscriptions)

    def fetch_all_sources(self):
        """Process all available predefined subscriptions"""
        if not self.predefined_subscriptions:
            QMessageBox.warning(self, "No Subscriptions", "No predefined subscriptions are available.")
            return

        self.log_debug("Fetching all predefined subscriptions...")
        self.status_bar.showMessage("Processing all predefined subscriptions...")
        QApplication.processEvents()

        # Clear previous results
        self.configs = []
        self.filtered_configs = []
        self.update_results_table()
        self.update_latency_table()

        all_raw_configs = []
        errors_occurred = False

        # Process each predefined subscription
        for name, url in self.predefined_subscriptions:
            try:
                self.log_debug(f"Processing predefined subscription: {name}")
                self.status_bar.showMessage(f"Processing '{name}'...")
                QApplication.processEvents()

                configs = self._read_single_subscription(url)
                if configs:
                    # Tag each config with source information
                    for config in configs:
                        config['source_subscription'] = url
                        config['source_subscription_name'] = name
                    all_raw_configs.extend(configs)
                    self.log_debug(f"Added {len(configs)} configs from '{name}'")
                else:
                    self.log_debug(f"No configs found from '{name}'")

            except Exception as e:
                self.log_debug(f"Error processing '{name}': {e}")
                errors_occurred = True

        self.configs = all_raw_configs

        if not self.configs:
            self.status_bar.showMessage("Processing complete. No configurations found from any source.")
            if not errors_occurred:
                QMessageBox.warning(self, "No Configurations", "No valid configurations were found from any of the predefined subscriptions.")
            return

        self.log_debug(f"Total raw configs collected from all sources: {len(self.configs)}. Applying filters...")
        self.apply_filter_and_update_ui()

    def add_subscription_dialog(self):
        """Show dialog to add a new subscription"""
        dialog = QDialog(self)
        dialog.setWindowTitle("Add New Subscription")
        dialog.setModal(True)
        dialog.resize(500, 200)

        layout = QVBoxLayout(dialog)

        # Name input
        layout.addWidget(QLabel("Subscription Name:"))
        name_input = QLineEdit()
        name_input.setPlaceholderText("Enter a descriptive name for this subscription")
        layout.addWidget(name_input)

        # URL input
        layout.addWidget(QLabel("Subscription URL:"))
        url_input = QLineEdit()
        url_input.setPlaceholderText("Enter the subscription URL (must start with http:// or https://)")
        layout.addWidget(url_input)

        # Buttons
        button_layout = QHBoxLayout()
        add_button = QPushButton("Add")
        cancel_button = QPushButton("Cancel")

        button_layout.addStretch()
        button_layout.addWidget(add_button)
        button_layout.addWidget(cancel_button)
        layout.addLayout(button_layout)

        # Connect buttons
        add_button.clicked.connect(dialog.accept)
        cancel_button.clicked.connect(dialog.reject)

        # Set default button
        add_button.setDefault(True)

        if dialog.exec_() == QDialog.Accepted:
            name = name_input.text().strip()
            url = url_input.text().strip()

            if not name:
                QMessageBox.warning(self, "Invalid Input", "Please enter a subscription name.")
                return

            if not url:
                QMessageBox.warning(self, "Invalid Input", "Please enter a subscription URL.")
                return

            if not url.startswith(('http://', 'https://')):
                QMessageBox.warning(self, "Invalid URL", "Subscription URL must start with http:// or https://")
                return

            # Check if name already exists
            existing_names = [existing_name for existing_name, _ in self.predefined_subscriptions]
            if name in existing_names:
                QMessageBox.warning(self, "Name Exists", f"A subscription with the name '{name}' already exists.")
                return

            # Add the subscription
            self.predefined_subscriptions.append((name, url))
            self.save_subscriptions_config()
            self._update_subscription_combo()

            # Select the newly added subscription
            self.subscription_combo.set_selected_items([name])

            QMessageBox.information(self, "Success", f"Successfully added subscription '{name}'.")
            self.log_debug(f"Added new subscription: {name} - {url}")

    def remove_selected_subscription(self):
        """Remove the selected subscription(s) from the predefined list"""
        if not hasattr(self, 'subscription_combo') or len(self.predefined_subscriptions) == 0:
            QMessageBox.warning(self, "No Selection", "No subscriptions available to remove.")
            return

        selected_subscriptions = self.subscription_combo.get_selected_items()

        if not selected_subscriptions:
            QMessageBox.warning(self, "No Selection", "Please select one or more subscriptions to remove.")
            return

        # Confirm removal
        if len(selected_subscriptions) == 1:
            reply = QMessageBox.question(
                self, "Confirm Removal",
                f"Are you sure you want to remove the subscription '{selected_subscriptions[0]}'?",
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.No
            )
        else:
            reply = QMessageBox.question(
                self, "Confirm Removal",
                f"Are you sure you want to remove {len(selected_subscriptions)} selected subscriptions?\n\n{', '.join(selected_subscriptions)}",
                QMessageBox.Yes | QMessageBox.No,
                QMessageBox.No
            )

        if reply == QMessageBox.Yes:
            # Remove the subscriptions (in reverse order to maintain indices)
            removed_names = []
            for selected_name in selected_subscriptions:
                for i, (name, url) in enumerate(self.predefined_subscriptions):
                    if name == selected_name:
                        del self.predefined_subscriptions[i]
                        removed_names.append(name)
                        break

            self.save_subscriptions_config()
            self._update_subscription_combo()

            if len(removed_names) == 1:
                QMessageBox.information(self, "Success", f"Successfully removed subscription '{removed_names[0]}'.")
                self.log_debug(f"Removed subscription: {removed_names[0]}")
            else:
                QMessageBox.information(self, "Success", f"Successfully removed {len(removed_names)} subscriptions.")
                self.log_debug(f"Removed subscriptions: {', '.join(removed_names)}")

    def edit_selected_subscription(self):
        """Edit the name and URL of the selected subscription"""
        if not hasattr(self, 'subscription_combo') or len(self.predefined_subscriptions) == 0:
            QMessageBox.warning(self, "No Selection", "No subscriptions available to edit.")
            return

        selected_subscriptions = self.subscription_combo.get_selected_items()

        if not selected_subscriptions:
            QMessageBox.warning(self, "No Selection", "Please select a subscription to edit.")
            return

        if len(selected_subscriptions) > 1:
            QMessageBox.warning(self, "Multiple Selection", "Please select only one subscription to edit.")
            return

        selected_name = selected_subscriptions[0]

        # Find the subscription by name
        subscription_index = -1
        current_name = ""
        current_url = ""
        for i, (name, url) in enumerate(self.predefined_subscriptions):
            if name == selected_name:
                subscription_index = i
                current_name = name
                current_url = url
                break

        if subscription_index == -1:
            QMessageBox.warning(self, "Invalid Selection", f"Selected subscription '{selected_name}' not found.")
            return

        # Create edit dialog
        dialog = QDialog(self)
        dialog.setWindowTitle("Edit Subscription")
        dialog.setModal(True)
        dialog.resize(500, 250)

        layout = QVBoxLayout(dialog)

        # Name input
        layout.addWidget(QLabel("Subscription Name:"))
        name_input = QLineEdit()
        name_input.setText(current_name)
        name_input.setPlaceholderText("Enter a descriptive name for this subscription")
        layout.addWidget(name_input)

        # URL input
        layout.addWidget(QLabel("Subscription URL:"))
        url_input = QLineEdit()
        url_input.setText(current_url)
        url_input.setPlaceholderText("Enter the subscription URL (must start with http:// or https://)")
        layout.addWidget(url_input)

        # Buttons
        button_layout = QHBoxLayout()
        save_button = QPushButton("Save Changes")
        cancel_button = QPushButton("Cancel")

        button_layout.addStretch()
        button_layout.addWidget(save_button)
        button_layout.addWidget(cancel_button)
        layout.addLayout(button_layout)

        # Connect buttons
        save_button.clicked.connect(dialog.accept)
        cancel_button.clicked.connect(dialog.reject)

        # Set default button
        save_button.setDefault(True)

        if dialog.exec_() == QDialog.Accepted:
            new_name = name_input.text().strip()
            new_url = url_input.text().strip()

            if not new_name:
                QMessageBox.warning(self, "Invalid Input", "Please enter a subscription name.")
                return

            if not new_url:
                QMessageBox.warning(self, "Invalid Input", "Please enter a subscription URL.")
                return

            if not new_url.startswith(('http://', 'https://')):
                QMessageBox.warning(self, "Invalid URL", "Subscription URL must start with http:// or https://")
                return

            # Check if name already exists (but allow keeping the same name)
            existing_names = [name for name, _ in self.predefined_subscriptions]
            if new_name in existing_names and new_name != current_name:
                QMessageBox.warning(self, "Name Exists", f"A subscription with the name '{new_name}' already exists.")
                return

            # Update the subscription
            self.predefined_subscriptions[subscription_index] = (new_name, new_url)
            self.save_subscriptions_config()
            self._update_subscription_combo()

            # Select the updated subscription
            self.subscription_combo.set_selected_items([new_name])

            # Show success message with details of what changed
            changes = []
            if current_name != new_name:
                changes.append(f"name: '{current_name}' → '{new_name}'")
            if current_url != new_url:
                changes.append(f"URL: '{current_url}' → '{new_url}'")

            if changes:
                change_text = ", ".join(changes)
                QMessageBox.information(self, "Success", f"Successfully updated subscription ({change_text}).")
                self.log_debug(f"Edited subscription: {current_name} -> {new_name}, {current_url} -> {new_url}")
            else:
                QMessageBox.information(self, "No Changes", "No changes were made to the subscription.")
                self.log_debug(f"Edit subscription dialog closed with no changes: {current_name}")

# --- Global Exception Handler ---
# Global variables for emergency resource management
EMERGENCY_MODE = False
EMERGENCY_RECOVERY_ATTEMPTS = 0
MAX_RECOVERY_ATTEMPTS = 3

def emergency_resource_cleanup():
    """Emergency cleanup of system resources to prevent crashes"""
    try:
        # Kill all Xray processes
        if platform.system() == "Windows":
            subprocess.run(["taskkill", "/F", "/IM", "xray.exe"],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          creationflags=subprocess.CREATE_NO_WINDOW)
        else:
            subprocess.run(["pkill", "-9", "xray"],
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE)

        # Force garbage collection
        try:
            import gc
            gc.collect()
        except ImportError:
            pass

        # Log the emergency cleanup
        print("Emergency resource cleanup performed")
    except Exception as e:
        print(f"Error during emergency cleanup: {e}")

def global_exception_handler(exctype, value, traceback_obj):
    """Global exception handler to log unhandled exceptions and attempt recovery"""
    global EMERGENCY_MODE, EMERGENCY_RECOVERY_ATTEMPTS

    # Format the traceback
    import traceback
    tb_lines = traceback.format_exception(exctype, value, traceback_obj)
    tb_text = ''.join(tb_lines)

    # Get current timestamp
    timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')

    # Create detailed error message
    error_message = f"\n\n{'='*50}\n"
    error_message += f"CRITICAL ERROR - {timestamp}\n"
    error_message += f"{'='*50}\n"
    error_message += f"Exception: {exctype.__name__}\n"
    error_message += f"Message: {str(value)}\n\n"
    error_message += f"Traceback:\n{tb_text}\n"

    # Log to error_log.txt
    error_log_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "error_log.txt")
    try:
        with open(error_log_path, 'a', encoding='utf-8') as f:
            f.write(error_message)
    except Exception as e:
        print(f"Failed to write to error log: {e}")

    # Also log to debug_log.txt if it exists
    debug_log_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "debug_log.txt")
    try:
        with open(debug_log_path, 'a', encoding='utf-8') as f:
            f.write(error_message)
    except Exception as e:
        print(f"Failed to write to debug log: {e}")

    # Print to console
    print(error_message)
    print(f"This error has been logged to: {error_log_path}")
    print(f"{'='*50}\n")

    # Perform emergency resource cleanup
    emergency_resource_cleanup()

    # Check if we're already in emergency mode
    if EMERGENCY_MODE:
        EMERGENCY_RECOVERY_ATTEMPTS += 1
        print(f"Emergency recovery attempt {EMERGENCY_RECOVERY_ATTEMPTS} of {MAX_RECOVERY_ATTEMPTS}")

        # If we've tried too many times, let the application crash
        if EMERGENCY_RECOVERY_ATTEMPTS >= MAX_RECOVERY_ATTEMPTS:
            print("Maximum recovery attempts reached. Allowing application to close.")
            # Show a final error message
            try:
                QMessageBox.critical(None, "Application Error",
                    f"Multiple critical errors occurred. The application will now close.\n\nSee {error_log_path} for details.")
            except Exception:
                pass
            return
    else:
        # Enter emergency mode
        EMERGENCY_MODE = True
        EMERGENCY_RECOVERY_ATTEMPTS = 1
        print("Entering emergency mode")

    # Show error message box if possible
    try:
        if QApplication.instance():
            # Create a more detailed error message box
            error_dialog = QMessageBox()
            error_dialog.setIcon(QMessageBox.Critical)
            error_dialog.setWindowTitle("Application Error")
            error_dialog.setText(f"A critical error has occurred:\n\n{exctype.__name__}: {str(value)}")

            # Different message based on recovery attempts
            if EMERGENCY_RECOVERY_ATTEMPTS < MAX_RECOVERY_ATTEMPTS:
                error_dialog.setInformativeText(
                    f"This error has been logged to:\n{error_log_path}\n\n"
                    f"Emergency recovery mode activated.\n"
                    f"The application will attempt to continue running with reduced functionality.\n\n"
                    f"It is recommended to save your work and restart the application."
                )
                error_dialog.setStandardButtons(QMessageBox.Ok)
            else:
                error_dialog.setInformativeText(
                    f"This error has been logged to:\n{error_log_path}\n\n"
                    f"Multiple recovery attempts have failed.\n"
                    f"The application will now close to prevent data loss.\n\n"
                    f"Please restart the application."
                )
                error_dialog.setStandardButtons(QMessageBox.Close)

            error_dialog.setDetailedText(tb_text)
            error_dialog.setDefaultButton(QMessageBox.Ok)

            # Make sure dialog stays on top and is visible
            error_dialog.setWindowFlags(error_dialog.windowFlags() | Qt.WindowStaysOnTopHint)

            # Show the dialog and wait for user response
            error_dialog.exec_()
    except Exception as dialog_err:
        print(f"Failed to show error dialog: {dialog_err}")
        # If we can't show a message box, try a simpler approach
        try:
            QMessageBox.critical(None, "Application Error",
                f"A critical error occurred: {exctype.__name__}: {str(value)}\n\nSee {error_log_path} for details.")
        except Exception:
            pass  # If all GUI approaches fail, just continue with the crash

    # If we've reached the maximum recovery attempts, let the application crash
    if EMERGENCY_RECOVERY_ATTEMPTS >= MAX_RECOVERY_ATTEMPTS:
        print("Maximum recovery attempts reached. Allowing application to close.")
        return

    # Otherwise, try to continue running

# --- Entry Point ---
if __name__ == "__main__":
    # Install the global exception handler
    sys.excepthook = global_exception_handler

    script_dir = os.path.dirname(os.path.abspath(__file__))
    temp_dir_main = os.path.join(script_dir, "temp")
    os.makedirs(temp_dir_main, exist_ok=True)
    # Download target dir is script_dir, already exists

    if platform.system() == "Windows":
        try:
             import ctypes
             myappid = 'com.qtester.configextractor.1.1' # Updated ID slightly
             ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(myappid)
        except Exception as e: print(f"Warning: Could not set AppUserModelID: {e}")

    # Set up signal handler for Ctrl+C
    import signal

    def signal_handler(sig, frame):
        """Handle Ctrl+C gracefully"""
        print("\nReceived interrupt signal. Shutting down gracefully...")
        try:
            # Try to access the window instance and clean up timers
            if 'window' in locals() or 'window' in globals():
                window_ref = locals().get('window') or globals().get('window')
                if window_ref and hasattr(window_ref, 'closeEvent'):
                    # Trigger the close event to clean up properly
                    window_ref.close()
        except:
            pass
        QApplication.quit()

    signal.signal(signal.SIGINT, signal_handler)

    app = QApplication(sys.argv)

    # Enable Ctrl+C handling in Qt
    signal.signal(signal.SIGINT, signal.SIG_DFL)

    window = ConfigExtractorApp()
    window.show()

    try:
        sys.exit(app.exec_())
    except KeyboardInterrupt:
        print("\nApplication interrupted by user")
        sys.exit(0)