# Task: HTTP Echo Server

Build a simple HTTP server that echoes back messages.

## Requirements:

Create `server.py` that:
- Listens on port 8000
- Has a `/echo` endpoint that accepts POST requests
- Returns JSON with the same message: `{"message": "<received_message>"}`

## Testing:

You have access to `test_server.py` which will test your implementation.
Run it to verify your server works correctly.

## Example:

```bash
# Start server
python server.py &

# Test it
python test_server.py
```

The test expects:
- POST to `http://localhost:8000/echo` with `{"message": "hello"}`
- Response: `{"message": "hello"}`
