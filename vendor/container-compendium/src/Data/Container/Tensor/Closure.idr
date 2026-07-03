module Data.Container.Tensor.Closure

import Data.Container
import Data.Container.Tensor.Definition
import Data.Container.Tensor.Bifunctor
import Data.Container.Morphism
import Data.Product
export infixr 1 ⇒

(⇒) : Container -> Container -> Container
(⇒) a b = (m : a =%> b) !> Σ (i : a.request) | b.response (m.fwd i)

curryFwd : a ⊗ b =%> c -> a =%> b ⇒ c
curryFwd m =
  (\xa => curry m.fwd xa <! (\yb, ya => π2 (m.bwd (xa && yb) ya))) <!
  (\xa, pp => π1 (m.bwd (xa && pp.π1) pp.π2))

curry : (a ⊗ b ⇒ c) =%> (a ⇒ b ⇒ c)
curry = curryFwd <! curryBwd
  where
    curryBwd : (m : a ⊗ b =%> c) ->
               (a ⇒ b ⇒ c).response (curryFwd m) ->
               (a ⊗ b ⇒ c).response m
    curryBwd m x = (x.π1 && x.π2.π1) ## x.π2.π2

apply : (a ⇒ b) ⊗ a =%> b
apply =
  (\ls => ls.π1.fwd ls.π2)
  <! (\ls, bw => (ls.π2 ## bw) && ls.π1.bwd ls.π2 bw)

0
triangle : {a, b, c : Container} ->
  (m : a ⊗ b =%> c) ->
  let cc : a =%> (b ⇒ c)
      cc = curryFwd {a, b, c} m
  in (cc ~⊗~ identity b
  |%> apply {a =b , b=c}) === m
triangle m = depLensEqToEq
  $ MkDepLensEq
    (\xx => cong (m.fwd) (pairUniq xx))
    (\xx, yy => rewrite pairUniq xx in pairUniq ?)

0
uniq : {a, b, c : Container} ->
  (m : a =%> b ⇒ c) ->
  let mm : a ⊗ b =%> c
      mm = m ~⊗~ identity b |%> apply {a = b, b = c}
  in curryFwd mm === m
uniq (mfw  <! mbw) = depLensEqToEq
  $ MkDepLensEq
    (\xx => depLensEqToEq $ MkDepLensEq (\_ => Refl) (\_, _ => Refl))
    (\xx, yy => cong (mbw xx) (sigmaProjId yy))
