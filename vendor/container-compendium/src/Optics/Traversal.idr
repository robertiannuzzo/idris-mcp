module Optics.Traversal

export
data FunList a b t = Done t | More a (FunList a b (b -> t))

public export
record Traversal (a, b, s, t : Type) where
  constructor MkTraversal
  extract : s -> FunList a b t
