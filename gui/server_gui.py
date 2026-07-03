#!/usr/bin/env python3
"""A tiny local GUI for idris-mcp.

Spawns the compiled Idris2 server (the same binary Client.idr talks to) as a
subprocess, speaks JSON-RPC to it over its stdin/stdout pipe -- exactly the
same mechanism as Client.idr and Claude Code -- and exposes that over a
local HTTP page so you can click a button instead of running a script.

Usage:
    python3 gui/server_gui.py [path/to/server/binary]

Then open http://localhost:8765
"""
import json
import subprocess
import sys
import threading
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path

DEFAULT_SERVER = Path(__file__).resolve().parent.parent / "build" / "exec" / "server"
PORT = 8765

HTML_PAGE = """<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<title>idris-mcp</title>
<style>
  body { font-family: -apple-system, sans-serif; max-width: 720px; margin: 40px auto; padding: 0 16px; }
  h1 { font-size: 20px; }
  button { padding: 8px 16px; font-size: 14px; cursor: pointer; }
  input { padding: 6px 8px; font-size: 14px; }
  pre { background: #f4f4f4; padding: 12px; border-radius: 6px; overflow-x: auto; font-size: 12.5px; }
  .row { margin: 16px 0; }
  #tools { margin: 8px 0; }
  .tool { border: 1px solid #ddd; border-radius: 6px; padding: 10px; margin: 8px 0; }
</style>
</head>
<body>
<h1>idris-mcp -- server GUI</h1>
<p>Talking to a real Idris2 MCP server, spawned as a subprocess by this page's own tiny Python backend -- no Claude Code, no API key.</p>

<div class="row">
  <button onclick="loadTools()">tools/list</button>
  <span id="toolsStatus"></span>
  <div id="tools"></div>
</div>

<div class="row">
  <label>name argument: <input id="nameArg" value="Robert"></label>
  <button onclick="callHello()">tools/call hello</button>
</div>

<div class="row">
  <h3>Last request</h3>
  <pre id="reqBox">(nothing yet)</pre>
  <h3>Last response</h3>
  <pre id="resBox">(nothing yet)</pre>
</div>

<script>
async function loadTools() {
  document.getElementById('toolsStatus').textContent = ' loading...';
  const r = await fetch('/api/tools');
  const data = await r.json();
  document.getElementById('reqBox').textContent = 'tools/list';
  document.getElementById('resBox').textContent = JSON.stringify(data, null, 2);
  document.getElementById('toolsStatus').textContent = '';
  const toolsDiv = document.getElementById('tools');
  toolsDiv.innerHTML = '';
  for (const t of (data.tools || [])) {
    const el = document.createElement('div');
    el.className = 'tool';
    el.innerHTML = '<b>' + t.name + '</b> -- ' + t.description;
    toolsDiv.appendChild(el);
  }
}

async function callHello() {
  const name = document.getElementById('nameArg').value;
  const body = { name: 'hello', arguments: { name } };
  document.getElementById('reqBox').textContent = JSON.stringify(body, null, 2);
  const r = await fetch('/api/call', { method: 'POST', body: JSON.stringify(body) });
  const data = await r.json();
  document.getElementById('resBox').textContent = JSON.stringify(data, null, 2);
}

loadTools();
</script>
</body>
</html>
"""


class MCPBridge:
    """Owns the server subprocess and speaks JSON-RPC over its stdio pipe."""

    def __init__(self, server_path):
        self.proc = subprocess.Popen(
            [str(server_path)],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
            text=True, bufsize=1,
        )
        self.lock = threading.Lock()
        self.next_id = 1
        self._request("initialize", {
            "protocolVersion": "2025-06-18", "capabilities": {},
            "clientInfo": {"name": "idris-mcp-gui", "version": "0.1.0"},
        })
        self._notify("notifications/initialized", None)

    def _write(self, obj):
        self.proc.stdin.write(json.dumps(obj) + "\n")
        self.proc.stdin.flush()

    def _request(self, method, params):
        with self.lock:
            rid = self.next_id
            self.next_id += 1
            msg = {"jsonrpc": "2.0", "id": rid, "method": method}
            if params is not None:
                msg["params"] = params
            self._write(msg)
            line = self.proc.stdout.readline()
            return json.loads(line)

    def _notify(self, method, params):
        with self.lock:
            msg = {"jsonrpc": "2.0", "method": method}
            if params is not None:
                msg["params"] = params
            self._write(msg)

    def tools_list(self):
        return self._request("tools/list", None)

    def tools_call(self, name, arguments):
        return self._request("tools/call", {"name": name, "arguments": arguments})


class Handler(BaseHTTPRequestHandler):
    bridge: MCPBridge = None  # set in main()

    def _json(self, obj, status=200):
        body = json.dumps(obj).encode()
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        if self.path == "/":
            body = HTML_PAGE.encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/html")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif self.path == "/api/tools":
            resp = self.bridge.tools_list()
            self._json(resp.get("result", resp))
        else:
            self._json({"error": "not found"}, 404)

    def do_POST(self):
        if self.path == "/api/call":
            length = int(self.headers.get("Content-Length", 0))
            body = json.loads(self.rfile.read(length))
            resp = self.bridge.tools_call(body["name"], body.get("arguments", {}))
            self._json(resp.get("result", resp))
        else:
            self._json({"error": "not found"}, 404)

    def log_message(self, fmt, *args):
        pass  # keep the terminal quiet


def main():
    server_path = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_SERVER
    if not server_path.exists():
        print(f"server binary not found: {server_path}", file=sys.stderr)
        sys.exit(1)

    Handler.bridge = MCPBridge(server_path)
    httpd = HTTPServer(("localhost", PORT), Handler)
    print(f"idris-mcp GUI: http://localhost:{PORT}  (spawned {server_path})")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        Handler.bridge.proc.terminate()


if __name__ == "__main__":
    main()
