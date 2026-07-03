module Data.Container.Displayed

import Data.Container
import Data.Container.Morphism.Definition
import Data.List.Quantifiers
import Data.Container.Closed

export infixr 0 !!>

public export
record ICont (i : Type) where
  constructor (!!>)
  baseTy : i -> Type
  fibreTy : (c : i) -> baseTy c -> Type

private prefix 0 !!!
public export
record ICont' (i : Type) where
  constructor (!!!)
  contFn : i -> Σ (t : Type) | t -> Type

export infixl 0 =+>

public export
record (=+>) (i : Container) (ty : ICont i.request) where
  constructor MkTm
  baseTm : (c : i.request) -> ty.baseTy c
  fibreTm : (c : i.request) -> ty.fibreTy c (baseTm c) -> i.response c

public export
record Mor (i : Container) (ty : ICont' i.request) where
  constructor MkMor
  baseTm : (c : i.request) -> (ty.contFn c).π1
  fibreTm : (c : i.request) -> (ty.contFn c).π2 (baseTm c) -> i.response c

public export
record Mor' (i : Container) (ty : ICont' i.request) where
  constructor MkMor'
  baseTm : (c : i.request) ->
           Σ (s : (ty.contFn c).π1) | (ty.contFn c).π2 s -> i.response c

public export
reindex : (a -> b) -> ICont b -> ICont a
reindex m c = (c.baseTy . m) !!> (\xx => c.fibreTy (m xx) )

public export
precompose : (m : a =%> b) -> b =+> c -> a =+> reindex m.fwd c
precompose (fw <! bw) (MkTm fw' bw') = MkTm (\xx => fw' (fw xx)) (\xx, yy => bw xx (bw' (fw xx) yy))

namespace Any
  public export
  List : ICont i -> ICont i
  List x = List . x.baseTy !!>
           \xx => Any (x.fibreTy xx)

%unbound_implicits off
composePi :
  {a : Type} ->
  {b : a -> Type} ->
  {c : {x : a} -> b x -> Type} ->
  (f : (x : a) -> b x) ->
  (g : {x : a} -> (y : b x) -> c y) ->
  (x : a) -> c (f x)
composePi f g x = g (f x)



public export
depSeq : {0 d : Type} -> (c : d -> Container) -> (f : (x : d) -> (c x).request -> Container) -> d -> Container
depSeq c f dx = (c1 : Σ (x : (c dx).request) | (c dx).response x -> (f dx x).request)
              !> Σ (y : (c dx).response c1.π1) | (f dx c1.π1).response (c1.π2 y)
