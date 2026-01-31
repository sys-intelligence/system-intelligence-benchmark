import requests
import json

def test_echo():
    url = "http://localhost:8000/echo"

    # Test 1: Simple message
    response = requests.post(url, json={"message": "hello"})
    assert response.status_code == 200, f"Expected 200, got {response.status_code}"
    data = response.json()
    assert data["message"] == "hello", f"Expected 'hello', got {data.get('message')}"

    # Test 2: Different message
    response = requests.post(url, json={"message": "world"})
    data = response.json()
    assert data["message"] == "world", f"Expected 'world', got {data.get('message')}"

    print("All tests passed!")

if __name__ == "__main__":
    test_echo()
