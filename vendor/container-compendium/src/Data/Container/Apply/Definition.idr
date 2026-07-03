module Data.Container.Apply.Definition

import Data.Container.Definition
public export
(•) : (f : Type -> Type) -> Container -> Container
(•) f c = (x : c.req) !> f (c.res x)
