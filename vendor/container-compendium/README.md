# Vendored slice of container-compendium

This directory contains an extracted and lightly patched slice of
[André Videla's container-compendium](https://github.com/andrevidela/container-compendium-site)
— an Idris2 formalization of container theory (Abbott/Altenkirch/Ghani). All credit for the
theory and its original Idris2 encoding belongs to André Videla; nothing in this directory is
original work by this project.

## Why it's vendored here rather than depended on normally

The upstream repository is a Quartz-powered digital-garden website, not a standard Idris2
package. Most of its modules exist only as literate `.idr.md` notes for web publishing, with
the real Idris2 source embedded inside HTML comments and code fences — not as directly
compilable `.idr` files.

`src/` here was produced by running [`tools/extract_literate_idris.py`](../../tools/extract_literate_idris.py)
(in this repo) against a local clone of the upstream vault, which recovers the real source from
those literate notes.

## What was patched, and why

Two genuine defects were found and fixed, scoped to this vendored copy only (the upstream
repository was left untouched):

- **Unicode operators.** No Idris2 build checked (stable 0.8.0, or the `pack`-pinned nightly)
  accepts non-ASCII operator characters — the lexer's `isOpChar` is a fixed ASCII whitelist.
  Unused Unicode fixity declarations were commented out in `Data/Category/Ops.idr` and
  `Data/Ops.idr`.
- **A nonexistent `autobind` keyword** inside a record body in `Extension/Definition.idr`,
  present in neither Idris2 build checked. Removed as vestigial.

Two imports were also narrowed (`Morphism/Chart.idr` and `Container/Definition.idr`) to avoid
pulling in unrelated proof machinery (`Extension.Properties`, `Data.Sigma`) that this project
doesn't use and that has its own Unicode-identifier issues.

## What's actually built

Only 6 modules are declared in [`container-compendium.ipkg`](container-compendium.ipkg) and get
compiled/installed: `Data.Boundary`, `Data.Category.Ops`, `Data.Container.Definition`,
`Data.Container.Extension.Definition`, `Data.Container.Morphism.Chart`, and
`Data.Container.Morphism.Definition`. The rest of `src/` is the full extracted vault (kept for
reference / potential future use) but is not part of the build.

## License

The upstream repository's `LICENSE.txt` is MIT, attributed to `jackyzha0` — the author of the
Quartz site-generator template the site is built on, not necessarily a license André Videla
explicitly attached to his own Idris2 content specifically. Treat this vendored slice as
"included with attribution, upstream license terms unclear for the Idris2 content itself" rather
than as unambiguously MIT-licensed.
