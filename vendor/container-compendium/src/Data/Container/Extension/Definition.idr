module Data.Container.Extension.Definition

import Data.Container.Definition

||| Extension of a container as a functor, Also interpreted as "existential" monads
public export
record Ex (cont : Container) (ty : Type) where
  -- vendored for idris-mcp: `autobind` isn't a keyword in any Idris2 build
  -- we have (stable 0.8.0 or the pack-pinned nightly) and appears
  -- unnecessary here — ordinary record syntax already lets later fields
  -- (ex1, ex2) reference the record's own parameters (cont, ty).
  constructor MkEx
  ex1 : cont.req
  ex2 : cont.res ex1 -> ty
%pair Ex ex1 ex2
