module Data.Container.Morphism.Definition

import Data.Container.Definition
import public Data.Category.Ops
import Control.Order
import Control.Relation

||| A container morphism
public export
record (=%>) (c1, c2 : Container) where
  constructor (<!)
  fwd : c1.request -> c2.request
  bwd : (x : c1.request) -> c2.response (fwd x) -> c1.response x
%pair (=%>) fwd bwd

||| Identity of container morphisms
public export
identity : (0 a : Container) -> a =%> a
identity v = id <! (\_ => id)
||| Composition of container morphisms
public export
(|%>) : a =%> b -> b =%> c -> a =%> c
(|%>) x y =
    (y.fwd . x.fwd) <!
    (\z => x.bwd z . y.bwd (x.fwd z))
public export
Reflexive Container (=%>) where
  reflexive = identity _

public export
Transitive Container (=%>) where
  transitive = (|%>)

public export
Preorder Container (=%>) where
