module Data.Maybe.Any
import Data.Maybe.Monad

||| Types of indexed maybe values that are always present
public export
data Any : (x -> Type) -> Maybe x -> Type where
  Aye : {v : x} -> pred v -> Any pred (Just v)
public export
(.unwrap) : Any p (Just x) -> p x
(.unwrap) (Aye y) = y
public export
Uninhabited (Any p Nothing) where
  uninhabited _ impossible
public export
anyFunctorMap :
    {0 a, b : Type} -> {0 a' : a -> Type} -> {0 b' : b -> Type} ->
    (fw : a -> b) -> (bw : (x : a) -> b' (fw x) -> a' x) ->
    (y : Maybe a) ->
    (z : Any b' (map fw y)) ->
    Any a' y
anyFunctorMap fw bw (Just x) y = Aye (bw x y.unwrap)

public export
anyJoin : {0 a : Type} -> {0 p : a -> Type} ->
          (x : Maybe (Maybe a)) ->
          Any p (joinMaybe x) ->
          Any (\x => Any p x) x
anyJoin Nothing y = absurd y
anyJoin (Just x) y = Aye y
