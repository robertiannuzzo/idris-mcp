module Data.Container.MonadInterface

import Data.Fin
import Data.Sigma
import Data.Product
import Data.Container
import Data.Container.Cartesian
import Data.Container.Sequence.Bifunctor
import Data.Container.Descriptions.Maybe
import Data.Container.Descriptions.List
import Data.Container.Morphism
import Data.Container.Maybe.Functor

%hide Prelude.(&&)
%default total

public export
interface CFunctor (0 m : Container -> Container) where
  constructor MkCFunctor
  map : (a =%> b) -> m a =%> m b

public export
interface CFunctor m => CMonad m where
  constructor MkCMonad
  pure : c =%> m c
  join : m (m c) =%> m c

||| Kleisli composition
public export
(>=>) : CMonad m => a =%> m b -> b =%> m c -> a =%> m c
(>=>) x y = x |%> map {a=b} y |%> join

public export
CFunctor Any.Maybe where
  map = ?Huia

public export
CMonad Any.Maybe where
  pure = ?qoqo
  join = ?oqw -- ?Descriptions.Maybe.join


mapAction : a =%> b -> x ▶ a =%> x ▶ b
--mapAction = Data.Container.Cartesian.univFunctor

{-

public export
CFunctor Forall where
  map arg = mapAction {x = ListCont} arg

public export
CMonad Forall where
  pure = Descriptions.List.pure
  join = Descriptions.List.join

%hint
composeFunctor : CFunctor m1 => CFunctor m2 => CFunctor (m1 . m2)
composeFunctor = MkCFunctor (\x => map (map x))

composeMonadsDistrib :
  (cm1 : CMonad m1) => (cm2 : CMonad m2) =>
  ({0 x : Container} ->
  m2 (m1 x) =%> m1 (m2 x)) ->
  CMonad (m1 . m2)
composeMonadsDistrib distrib = MkCMonad ?bluheh
  --(pure {m = m1} ⨾ map @{cm1} ?aidojoij)
  ?dand -- (map {m=m1} (distrib {x = m2 _}) ⨾ join ⨾ map join)

