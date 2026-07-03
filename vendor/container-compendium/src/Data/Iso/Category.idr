module Data.Iso.Category

import public Data.Iso.Generic
import Data.Category

import public Control.Relation
%hint public export
RCat : {cat : _} -> Reflexive cat.obj ((~:>) cat)
RCat = MkReflexive (cat.id _)
%hint public export
TCat : {cat : _} -> Transitive cat.obj ((~:>) cat)
TCat = MkTransitive $
    \ f, g => (|:>) cat f g
public export
CatIso : {0 o : Type} -> (cat : Category o) -> (a, b : o) -> Type
CatIso cat a b = GenIso o ((~:>) cat) (===) {tx = TCat, rx = RCat} a b
