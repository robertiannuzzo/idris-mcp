#!/usr/bin/env python3
"""Extract compilable Idris2 source from container-compendium's literate
*.idr.md notes.

Each .idr.md interleaves prose/website markup with two kinds of real Idris
source, in document order:

  1. `<!-- idris ... -->` HTML comment blocks: compiler-only code (module
     headers, bare `public export` qualifiers) hidden from the web page.
  2. ` ```idris [{attrs}] ... ``` ` fenced code blocks, whether standalone
     or nested inside a ````definition/proposition/...```` prose wrapper,
     with or without a {hidden=...}/{label=...}/{caption=...} attribute.
     All of these are real Idris source, attributes only affect how the
     compendium's own web renderer displays them.

Concatenating both kinds of matches in file order (by string offset)
reconstructs the module's actual Idris source. This is the reverse of
quartz/plugins/transformers/literateIdris.ts, which strips these same
regions out for HTML display.

Usage:
    extract_literate_idris.py <vault-src-dir> <output-src-dir>

Copies plain .idr files through unchanged, and writes an extracted .idr
for every .idr.md (dropping the .md suffix), mirroring directory structure.
"""
import re
import shutil
import sys
from pathlib import Path

COMMENT_RE = re.compile(r"<!--\s*idris\s*\n(.*?)-->", re.DOTALL)
FENCE_RE = re.compile(r"```idris(?:\s+\{[^}]*\})?\n(.*?)```", re.DOTALL)


def extract(md_text: str) -> str:
    matches = [(m.start(), m.group(1)) for m in COMMENT_RE.finditer(md_text)]
    matches += [(m.start(), m.group(1)) for m in FENCE_RE.finditer(md_text)]
    matches.sort(key=lambda t: t[0])
    pieces = [content.strip("\n") for _, content in matches]
    return "\n".join(pieces) + "\n"


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__)
        return 1
    src_root = Path(sys.argv[1])
    out_root = Path(sys.argv[2])

    if not src_root.is_dir():
        print(f"not a directory: {src_root}", file=sys.stderr)
        return 1

    n_extracted = 0
    n_copied = 0
    for path in sorted(src_root.rglob("*")):
        if path.is_dir():
            continue
        rel = path.relative_to(src_root)
        if path.name.endswith(".idr.md"):
            out_path = out_root / rel.with_suffix("")  # drop trailing .md
            out_path.parent.mkdir(parents=True, exist_ok=True)
            out_path.write_text(extract(path.read_text()))
            n_extracted += 1
        elif path.suffix == ".idr":
            out_path = out_root / rel
            out_path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, out_path)
            n_copied += 1

    print(f"extracted {n_extracted} .idr.md -> .idr, copied {n_copied} plain .idr, into {out_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
