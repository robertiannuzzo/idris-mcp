module Data.Container.ForallSeq.Definition

import Data.Container.Definition
import Data.Container.Morphism.Definition
import Data.Container.Extension
import Data.Sigma

-- The new one
public export
(▶) : Container -> Container -> Container
(▶) c1 c2 = (x : Ex c1 c2.req) !>
            ((val : c1.res x.ex1) -> c2.res (x.ex2 val))
