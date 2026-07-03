module Data.Preorder

import public Control.Relation

public export
Preorder : (ty : Type) -> Rel ty -> Type
Preorder ty rel = Pair (Reflexive ty rel) (Transitive ty rel)
