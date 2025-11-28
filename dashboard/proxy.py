from logging import Handler
import requests
import re
from dashboard.dashboard_app import DASHBOARD_URL
from datetime import datetime
from typing import Dict, Any

class LogProxy(Handler):
    # This proxy is used to proxy the logs to the dashboard
    
    def __init__(self):
        super().__init__()
        self.dashboard_url = DASHBOARD_URL.rstrip('/')
        self.log_endpoint = f"{self.dashboard_url}/api/logs"

    def emit(self, record):
        """
        Parse log record and send to dashboard
        
        Expected log format: "[SORT] xxxxxxxxxxxx"
        """
        try:
            # Get the log message
            log_message = self.format(record)
            
            # Parse the log message
            parsed_log = self._parse_log_message(log_message, record)
            
            # Send to dashboard
            self._send_to_dashboard(parsed_log)
            
        except Exception as e:
            # Avoid infinite recursion by not logging errors
            print(f"LogProxy error: {e}")

    def _parse_log_message(self, log_message: str, record) -> Dict[str, Any]:
        """
        Parse log message in format "[SORT] xxxxxxxxxxxx"
        
        Returns:
            Dict with keys: timestamp, location, sort, content
        """
        # Extract timestamp from record
        timestamp = datetime.fromtimestamp(record.created).strftime('%Y-%m-%d %H:%M:%S')
        
        # Extract location (filename:line number)
        location = f"{record.filename}:{record.lineno}"
        
        # Parse the log message for [SORT] pattern
        sort_match = re.match(r'\[([^\]]+)\]\s*(.*)', log_message, re.DOTALL)
        
        if sort_match:
            sort = sort_match.group(1).strip()
            content = sort_match.group(2).strip()
        else:
            # If no [SORT] pattern found, use record level as sort
            sort = record.levelname
            content = log_message
        
        return {
            'timestamp': timestamp,
            'location': location,
            'sort': sort,
            'content': content
        }

    def _send_to_dashboard(self, log_data: Dict[str, Any]):
        """
        Send parsed log data to dashboard via HTTP POST
        """
        try:
            response = requests.post(
                self.log_endpoint,
                json=log_data,
                timeout=1.0  # Short timeout to avoid blocking
            )
            response.raise_for_status()
        except requests.exceptions.RequestException:
            # Silently fail to avoid infinite logging loops
            pass


# Example usage:
# import logging
# from dashboard.proxy import LogProxy
# 
# logger = logging.getLogger('my_app')
# logger.setLevel(logging.INFO)
# 
# # Add LogProxy handler
# log_proxy = LogProxy(dashboard_url='http://0.0.0.0:8050')
# logger.addHandler(log_proxy)
# 
# # Now log messages in format "[SORT] content" will be sent to dashboard
# logger.info("[STAGE] Application starting up")
# logger.error("[ERROR] Database connection failed")
        