module Data.Container.Coproduct.Definition

import Data.Container.Definition

import public Data.Coproduct

public export
(+) : (c1, c2 : Container) -> Container
(+) c1 c2 =
  (q : c1.request + c2.request) !> choice c1.response c2.response q
