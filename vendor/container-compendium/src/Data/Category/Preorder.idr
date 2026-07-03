module Data.Category.Preorder

import Control.Relation
import Data.Category
export
{cat : _} -> Reflexive cat.obj ((~:>) cat) where
    reflexive = cat.id _

%hint export
TCat : {cat : _} -> Transitive cat.obj ((~:>) cat)
TCat = MkTransitive $
    \ f, g => (|:>) cat f g
