module Data.Container.Translation

import Data.Container.Morphism.Definition
import Data.Container.Morphism.Eq
import Data.Container.Closed
import Proofs.Sigma
import Proofs

export 0
toClosedEq : {m, n : a =%> b} ->
             m <%≡%> n ->
             ClosedEq (toClosed m) (toClosed n) SigEq'
toClosedEq eq = rewrite depLensEqToEq eq in reflEq sigEqRefl'

export 0
fromClosedEq : {m, n : a =&> b} ->
             ClosedEq m n SigEq' ->
             (fromClosed m) <%≡%> (fromClosed n)
fromClosedEq eq = rewrite clsEqToEq SigEq' sigEqToEq' eq in reflexive
