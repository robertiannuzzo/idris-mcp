module Data.Container.List.Monad

import Data.Category
import Data.Category.Action
import Data.Category.Functor
import Data.Category.Bifunctor
import Data.Category.Endofunctor
import Data.Category.Monad
import Data.Category.Monoid
import Data.Category.NaturalTransformation
import Data.Category.MonadAction

import Data.Container
import Data.Container.Category
import Data.Container.Morphism
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.ForallSeq.Bifunctor
import Data.Container.Sequence.Monoidal
import Data.Container.ForallSeq.Action
import Data.Container.Cartesian.Sequence.Monoidal as Cart
import Data.Container.Descriptions.Maybe
import Data.Container.Descriptions.List
import Data.Container.List.Desc
import Data.Container.List.Functor
import Data.Container.List.Monoid

import Data.Fin
import Data.List
import Data.Sigma
import Data.List.Quantifiers
import Data.List.Monad
import Data.Iso

import Proofs

import Syntax.PreorderReasoning
import Pipeline.Equality

%hide Prelude.Ops.infixl.(*>)
%default total
public export
ForallMonadCont : Monad Cont ForallFunctor
ForallMonadCont = MonadFromLaxAction ? ?
    ContCart Cont SequenceMonoidal Action.ForallLaxAction Cartesian.ListMonoid
ListMonoidalAction : Action Cont Cont SequenceMonoidal
ListMonoidalAction = monoidalSelfAction SequenceMonoidal

ForanyMonadCont : Monad Cont ForanyFunctor
-- ForanyMonadCont = MonadFromLaxAction ? ?
--     Cont Cont SequenceMonoidal (relax ListMonoidalAction) Cont.ListMonoid
