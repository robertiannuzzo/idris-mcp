# idris-mcp

An MCP (Model Context Protocol) server and client implemented from scratch in Idris2 — no
existing SDK, since none exists for Idris2. The point isn't "MCP in one more language": it's to
use Idris2's dependent types, built on real container theory, to make protocol conformance a
compile-time property rather than a runtime one.

See [`docs/idris-mcp-architecture.pdf`](docs/idris-mcp-architecture.pdf) for the full writeup —
file-by-file architecture, the container-theory design, what's verified, and what's next.

## What's here

- `src/` — the server and client, hand-written JSON-RPC 2.0 + stdio transport, and
  `MCP/Container.idr`, where the MCP method/result surface is modeled as a real container
  (`Method` = shapes, `ResultOf : Method -> Type` = the dependent response family), built on
  the vendored library below.
- `src/MCP/Proof.idr` — the `check` and `prove` methods (see below): a subprocess-based
  typecheck oracle plus an LLM proposer, where the Idris2 typechecker is the only thing
  ever trusted.
- `vendor/container-compendium/` — a vendored, patched slice of
  [André Videla's container-compendium](https://github.com/andrevidela/container-compendium-site).
  See [its README](vendor/container-compendium/README.md) for attribution and what was patched.
- `vendor/container-compendium/mcp-demo/` — a standalone demo of the client modeled as a literal
  value of the library's dependent-lens type, `(=%>)` (not wired into the live transport).
- `gui/server_gui.py` — a small, dependency-free local web GUI (stdlib only) that spawns the
  compiled server binary and lets you drive it from a browser instead of a terminal.
- `tools/extract_literate_idris.py` — the script that recovers compilable Idris2 source from
  container-compendium's literate `.idr.md` notes.

## Build and run

```sh
idris2 --build server.ipkg
idris2 --build client.ipkg

# your own client talking to your own server, no external dependency at all
./build/exec/client
```

To register the server with Claude Code:

```sh
claude mcp add idris-mcp -- "$(pwd)/build/exec/server"
```

To run the browser GUI instead:

```sh
python3 gui/server_gui.py
# open http://localhost:8765
```

## The compile-time safety demo

In `src/MCP/Container.idr`, `dispatch : (m : Method) -> IO (ResultOf m)` is exhaustive and
dependently typed — a handler returning the wrong result shape for its method is a compile
error, not a runtime bug. Try it: change a `dispatch` clause to return the wrong constructor
(e.g. swap in `MkCallToolResult [] False` where a `List Tool` is expected) and rebuild.

## Proof generation: `check` and `prove`

The server also exposes two theorem-proving methods. The design invariant for both: **the
Idris2 typechecker is the sole oracle.** Nothing that produces terms is trusted; every
candidate is verified by spawning the real `idris2 --check` on it, and only accepted terms
are ever returned as proofs.

- **`check`** — verify a caller-supplied signature + term. No LLM, no network:

  ```sh
  printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"check","params":{"signature":"triv : Nat -> Nat","term":"triv n = n"}}' | ./build/exec/server
  ```

- **`prove`** — takes an English prompt; an LLM (Anthropic API, `ANTHROPIC_API_KEY` env var
  required) translates it to an Idris2 signature and proposes a proof term; the typechecker
  verifies; on failure, the compiler's own diagnostic is fed back to the LLM in a bounded
  repair loop (3 attempts):

  ```sh
  export ANTHROPIC_API_KEY="sk-ant-..."
  printf '%s\n' '{"jsonrpc":"2.0","id":1,"method":"prove","params":{"prompt":"addition of natural numbers is commutative"}}' | ./build/exec/server
  ```

  Verified live: right-identity of addition, `xs ++ [] = xs`, and full commutativity of
  addition (for which the model invented two helper lemmas and composed them — all three
  definitions machine-checked) all come back `outcome: "checked"` with the accepted term
  and an English paraphrase of what was actually formalized.

Results carry evidence, never a bare boolean: `checked` (the accepted signature/term),
`refuted` (a specific candidate failed, with the compiler diagnostic verbatim), `unknown`
(out of attempts, with the full attempt history — absence of a proof is not evidence of
falsity), or `parse_error`. A hallucinated proof cannot come back `checked`; the honest
failure mode is `unknown`, never a wrong answer.
