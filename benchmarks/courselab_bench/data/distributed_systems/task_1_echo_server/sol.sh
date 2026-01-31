#!/bin/bash
# Solution script for HTTP Echo Server task
# This script simulates what an agent might execute to solve the task

cat > server.py << 'EOF'
#!/usr/bin/env python3
"""
Simple HTTP echo server that listens on port 8000
and has a /echo endpoint that echoes back JSON messages.
"""

import json
import sys
from http.server import HTTPServer, BaseHTTPRequestHandler


class EchoHandler(BaseHTTPRequestHandler):
    """HTTP request handler that echoes back messages."""

    def do_POST(self):
        """Handle POST requests."""
        if self.path == '/echo':
            # Get the content length from headers
            content_length = int(self.headers.get('Content-Length', 0))

            # Read the request body
            body = self.rfile.read(content_length)

            try:
                # Parse the JSON request
                data = json.loads(body.decode('utf-8'))
                message = data.get('message', '')

                # Create the response
                response = {'message': message}
                response_json = json.dumps(response)

                # Send the response
                self.send_response(200)
                self.send_header('Content-Type', 'application/json')
                self.send_header('Content-Length', len(response_json))
                self.end_headers()
                self.wfile.write(response_json.encode('utf-8'))

            except (json.JSONDecodeError, ValueError) as e:
                # Handle JSON parsing errors
                self.send_response(400)
                self.send_header('Content-Type', 'application/json')
                self.end_headers()
                error_response = json.dumps({'error': 'Invalid JSON'})
                self.wfile.write(error_response.encode('utf-8'))
        else:
            # Handle undefined endpoints
            self.send_response(404)
            self.send_header('Content-Type', 'application/json')
            self.end_headers()
            error_response = json.dumps({'error': 'Endpoint not found'})
            self.wfile.write(error_response.encode('utf-8'))

    def log_message(self, format, *args):
        """Override to suppress logging to stdout."""
        pass


def run_server(port=8000):
    """Run the HTTP server on the specified port."""
    server_address = ('', port)
    httpd = HTTPServer(server_address, EchoHandler)
    print(f"Server running on port {port}...")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\nServer shutting down...")
        httpd.shutdown()


if __name__ == '__main__':
    port = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
    run_server(port)
EOF

chmod +x server.py
