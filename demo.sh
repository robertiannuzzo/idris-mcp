#!/bin/sh
# Demo driver for idris-mcp. Runs each step when you press Enter, so you
# control the pace. Run from the repo root:
#
#     ./demo.sh
#
# The prove steps need ANTHROPIC_API_KEY exported in this shell first;
# if it isn't set, those steps are skipped with a notice rather than
# failing mid-demo.

cd "$(dirname "$0")" || exit 1

bold=$(printf '\033[1m')
dim=$(printf '\033[2m')
reset=$(printf '\033[0m')

step() {
  echo
  echo "${bold}== $1 ==${reset}"
  echo "${dim}$2${reset}"
  printf '%s' "${dim}[press Enter to run]${reset}"
  read -r _
}

request() {
  printf '%s\n' "$1" | ./build/exec/server
}

echo "${bold}idris-mcp demo${reset}"
echo "Server binary: ./build/exec/server (Idris2, built from src/)"

step "1. Client <-> server, both Idris2, no Claude anywhere" \
     "Our own client spawns the server and runs the full MCP handshake."
./build/exec/client

step "2. check: a valid proof term is accepted" \
     "The server spawns the real Idris2 typechecker on the submitted term."
request '{"jsonrpc":"2.0","id":1,"method":"check","params":{"signature":"triv : Nat -> Nat","term":"triv n = n"}}'

step "3. check: an ill-typed term is refuted, with the compiler's own diagnostic" \
     "Same term, but returning a string where a Nat is required."
request '{"jsonrpc":"2.0","id":2,"method":"check","params":{"signature":"triv : Nat -> Nat","term":"triv n = \"nope\""}}'

if [ -z "$ANTHROPIC_API_KEY" ]; then
  echo
  echo "${bold}ANTHROPIC_API_KEY is not set -- skipping the prove steps.${reset}"
  echo "Export it in this shell and re-run to include them."
  exit 0
fi

step "4. prove: an easy lemma from plain English (takes ~15-60s)" \
     "LLM proposes signature+term; only typechecker-accepted terms come back."
request '{"jsonrpc":"2.0","id":3,"method":"prove","params":{"prompt":"zero is a right identity for addition on natural numbers"}}'

step "5. prove: commutativity of addition (the model invents helper lemmas)" \
     "Watch the term field: multiple machine-checked definitions."
request '{"jsonrpc":"2.0","id":4,"method":"prove","params":{"prompt":"addition of natural numbers is commutative"}}'

step "6. prove: something false -- this step is non-deterministic, know both outcomes" \
     "Unsound escape hatches (believe_me etc.) are blocked, so the model
CANNOT get 'checked' on the false claim itself. Observed live, same
prompt, different runs -- BOTH of these are correct, expected behavior:
  (a) 'checked' -- but read the signature: it silently swapped in the
      NEGATION (Not (n = S n)), a true statement. Say out loud:
      outcome=checked does NOT mean the original prompt was proven --
      read signature+paraphrase every time.
  (b) 'unknown' with the full attempt history -- it tried believe_me,
      got blocked, tried a couple of invalid 'impossible' cases, ran out
      of its 3-attempt budget, and honestly gave up rather than fake it.
Either way the invariant holds: the false claim itself never checks."
request '{"jsonrpc":"2.0","id":5,"method":"prove","params":{"prompt":"every natural number equals its successor"}}'

echo
echo "${bold}Done.${reset}"
