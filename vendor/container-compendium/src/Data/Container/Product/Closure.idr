module Data.Container.Product.Closure

import Data.Container
import Data.Container.Product
import Data.Container.Morphism
import Data.Container.Apply.Definition
import Data.Container.Lift

import Data.Product
import Data.Maybe
export infixr 1 ⇒

data IsNothing : Maybe a -> Type where
  N : IsNothing Nothing

Uninhabited (IsNothing (Just x)) where
  uninhabited _ impossible

(⇒) : Container -> Container -> Container
(⇒) a b = (m : Maybe • a =%> b) !> Σ (i : a.request) | Σ (j : b.response(m.fwd i)) | IsNothing (m.bwd i  j)

getRight : a + b -> Maybe b
getRight (<+ x) = Nothing
getRight (+> x) = Just x

left : (p : a + b) -> (contra : IsNothing (getRight p)) => a
left (<+ x) = x
left (+> x) = absurd contra

curryFwd : a * b =%> c -> a =%> (b ⇒ c)
curryFwd m = (\xa => curry m.fwd xa <! (\yb, ya => getRight (m.bwd (xa && yb) ya))) <!
             (\xa, pp => left (m.bwd (xa && pp.π1) pp.π2.π1) @{pp.π2.π2})



distribM : (f : Type -> Type) -> Functor f => f • (a * b) =%> (f • a) * (f • b)
distribM f = id <! (\x => distribF)

%unbound_implicits off
backward : {0 a, b, c : Container} ->
           (m : Maybe • (a * b) =%> c) ->
           (xa : a .request) ->
           (b ⇒ c).response (curry m.fwd xa <! (\yb, ya => (m.bwd (xa && yb) ya) >>= getRight))->
           Maybe (a .response xa)
backward (fw <! bw) xa (p1 ## p2 ## p3) with (bw (xa && p1) p2)
  backward (fw <! bw) xa (p1 ## p2 ## p3) | Nothing = Nothing
  backward (fw <! bw) xa (p1 ## p2 ## p3) | (Just (<+ x)) = Just x
  backward (fw <! bw) xa (p1 ## p2 ## p3) | (Just (+> x)) = absurd p3

%unbound_implicits on
curryF : Maybe • (a * b) =%> c ->
         Maybe • a =%> b ⇒ c
curryF m = (\xa => curry m.fwd xa <! (\yb, ya => (m.bwd (xa && yb) ya) >>= getRight)) <!
           backward m


curry : ((a * b) ⇒ c) =%> (a ⇒ (b ⇒ c))
curry = curryF <! curryBwd
  where

    curryBwd :
      (m : ((a * b) ⇒ c).request) ->
      let
        asd : Maybe • a =%> b ⇒ c
        asd = curryF m
      in (a ⇒ b ⇒ c) .response asd ->
         ((a * b) ⇒ c) .response m
    curryBwd (fw <! bw) (p1 ## (p2 ## p3 ## p4) ## p5) with (bw (p1 && p2) p3) proof p
      _ | Nothing = (p1 && p2) ## p3 ## (rewrite p in N)
      _ | Just (+> x) = (p1 && p2) ## p3 ## absurd p4
      _ | Just (<+ x) = (p1 && p2) ## p3 ## absurd p5
