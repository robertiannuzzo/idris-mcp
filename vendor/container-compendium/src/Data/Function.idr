module Data.Function

import Control.Relation
import Control.Order

public export
Fn : Type -> Type -> Type
Fn x y = x -> y

public export
Transitive Type Fn where
  transitive f g x = g (f x)

public export
Reflexive Type Fn where
  reflexive = id

public export
Preorder Type Fn where
