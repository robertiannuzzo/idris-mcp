module Data.Iso.Generic

import public Control.Relation
import public Control.Order
%unbound_implicits off
public export
record GenIso (0 carrier : Type)
              (0 mor : Rel carrier)
              (0 equ : {0 x, y : carrier} -> Rel (mor x y))
              {auto tx : Transitive carrier mor}
              {auto rx : Reflexive carrier mor}
              (left, right : carrier) where
  constructor MkGenIso
  to : left `mor` right
  from : right `mor` left
  0 toFrom : (to `Relation.transitive` from) `equ` Relation.reflexive
  0 fromTo : (from `Relation.transitive` to) `equ` Relation.reflexive
