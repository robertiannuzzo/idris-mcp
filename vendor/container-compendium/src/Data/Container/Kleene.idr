module Data.Container.Kleene

import Data.Container
import Data.Sigma
import Data.Product

import Data.Vect
import Data.Container.Morphism
import Data.Container.Lift
import Data.Container.Coproduct
import Data.Container.Descriptions.Maybe

import Proofs

%default total
public export
data StarFw : (0 _ : Container) -> Type where
  Done : StarFw c
  More : (x : c.req) -> (c.res x -> StarFw c) -> StarFw c

public export
data StarBw : (0 c : Container) -> StarFw c -> Type where
  StarU : StarBw c Done
  StarM : {0 c : Container} -> {0 x1 : c.req} -> {x2 : c.res x1 -> StarFw c} ->
          (x : c.res x1) -> (StarBw c (x2 x)) ->
          StarBw c (More x1 x2)
public export
Star : Container -> Container
Star c = (x : StarFw c) !> StarBw c x
public export
singleton : c.req -> StarFw c
singleton x = More x (\_ => Done)
