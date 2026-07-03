module Optics.Prism

import Data.Coproduct

public export
record Prism (a, b, s, t : Type) where
  constructor MkPrism
  match : s -> t + a
  build : b -> t

public export
record Prism' (a, b, s, t : Type) where
  constructor MkPrism'
  0 res : Type
  match : s -> res + a
  build : res + b -> t

public export
toOptic : Prism a b s t -> Prism' a b s t
toOptic (MkPrism match build) = MkPrism' t match (choice id build)

record LinPrism (a, b, s, t : Type) where
  constructor MkLinPrism
  fn : s -> (t , b -> t) + a


toLin : Prism a b s t -> LinPrism a b s t
toLin (MkPrism match build) = MkLinPrism $ \xs =>
  case match xs of
    (<+ x) =>  <+ (x, build)
    (+> x) =>  +> x

fromLin : LinPrism a b s t -> Prism a b s t
fromLin (MkLinPrism fn) = MkPrism (mapFst fst . fn) ?fromLin_rhs_0

