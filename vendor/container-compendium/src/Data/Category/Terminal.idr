module Data.Category.Terminal

import Data.Category

public export
record HasTerminal {0 o : Type} (cat : Category o) where
  constructor MkTerminal

  -- The initial object
  terminal : o

  -- Each object has a morphism from the initial object
  termMap : (v : o) -> v ~> terminal

  -- Each morphism from the initial object is unique
  toTermUniq : (v : o) -> (m : v ~> terminal) -> m = termMap v
