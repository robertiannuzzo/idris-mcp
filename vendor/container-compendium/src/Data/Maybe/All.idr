module Data.Maybe.All

import Proofs.Transport
import Data.Maybe.Monad
namespace Maybe
  public export
  data All : (pred : x -> Type) -> Maybe x -> Type where
    Nay : All pred Nothing
    Yay : {0 v : x} -> pred v -> All pred (Just v)
public export
(.unwrap) : All p (Just a) -> p a
(.unwrap) (Yay x) = x
public export
allFunctorMap :
    {0 a, b : Type} -> {0 a' : a -> Type} -> {0 b' : b -> Type} ->
    (fw : a -> b) -> (bw : (x : a) -> b' (fw x) -> a' x) ->
    (y : Maybe a) ->
    (z : All b' (map fw y)) ->
    All a' y
allFunctorMap fw bw (Just x) (Yay y) = Yay (bw x y)
allFunctorMap fw bw Nothing _ = Nay
export 0
allFunctorMapId :
    {0 a : Type} -> {0 a' : a -> Type} ->
    (yy : Maybe a) ->
    (y : All a' (map Prelude.id yy)) ->
    allFunctorMap Prelude.id (\_ => Prelude.id) yy y ===
      transport (All a') (maybeFunctorId yy) y

export 0
allFunctorMapCompose :
    {a : Type} -> {a' : a -> Type} ->
    {b : Type} -> {b' : b -> Type} ->
    {c : Type} -> {c' : c -> Type} ->
    (f : a -> b) ->
    (f' : (x : a) -> b' (f x) -> a' x) ->
    (g : b -> c) ->
    (g' : (x : b) -> c' (g x) -> b' x) ->
    (xx : Maybe a) ->
    (yy : All c' (map (g . f) xx)) ->
    allFunctorMap
      (g . f)
      (\z => f' z . g' (f z)) xx yy
      =
    allFunctorMap
      f
      f'
      xx
      (allFunctorMap
        g
        g'
        (map f xx)
        (transport (All c')
            (sym (maybeFunctorCompose g f xx))
            yy
        )
      )
allFunctorMapCompose f f' g g' Nothing yy = Refl
allFunctorMapCompose f f' g g' (Just x) (Yay y) =
  rewrite applyRefl (All c') (Yay y) in Refl
