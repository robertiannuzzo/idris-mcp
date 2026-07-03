module Data.Container.Descriptions.Maybe

import Data.Container.Definition
import Data.Container.ForallSeq.Definition
import Data.Container.Morphism
import Data.Container.Morphism.Eq
import Data.Product
import Data.Sigma
import Data.Iso
import Data.Iso.Generic
import Data.Maybe
import Data.Maybe.Any as Maybe.Quantifier
import Proofs

%default total

{-
-- strict version of boolean operations
public export
and : Bool -> Bool -> Bool
and True x = x
and False _ = False

public export
or : Bool -> Bool -> Bool
or False x = x
or True _ = True
namespace Any
  public export
  Maybe : Container -> Container
  Maybe c = (m : Maybe c.req) !> Quantifier.Any c.res m
||| We can always convert from the `MaybeCont ▷` monad to the Idris definition
public export
MaybeToAny : MaybeAny x =%> Any.Maybe x
MaybeToAny =
    toIdris <! bwd
    where
      bwd : (v : MaybeType x.req) ->
            Any x.res (toIdris v) -> Σ (IsTrue v.ex1) (\y => x.res (v.ex2 y))
      bwd (MkEx True p) (Aye x) = TT ## x
      bwd (MkEx False p) _ impossible

||| We can always convert from the Idris definition to the `MaybeCont ▷` monad
public export
AnyToMaybe : Any.Maybe x =%> MaybeAny x
AnyToMaybe =
    fromIdris <! bwd
    where
      bwd : (v : Maybe x.req) -> (MaybeAny x).res (fromIdris v) -> Any x.res v
      bwd Nothing x = absurd x.π1
      bwd (Just y) x = Aye x.π2

||| Going from Idris to `MaybeCont ▷` and back to Idris is like doing nothing
AnyToMaybeToAny : {0 x : Container} -> (AnyToMaybe {x} ⨾ MaybeToAny {x}) <%≡%> (identity {a = Any.Maybe x})
AnyToMaybeToAny = MkDepLensEq
  toFromEq
  (\case Nothing => \x => absurd x
         (Just y) => \(Aye x) => Refl)

||| Going from `MaybeCont ▷` to Idris and back is like doing nothing
MaybeToAnyToMaybe : {0 x : Container} -> (MaybeToAny{x} ⨾ AnyToMaybe  {x}) <%≡%> (identity {a = MaybeAny x})
MaybeToAnyToMaybe = MkDepLensEq
  fromToEq
  bwdEq
  where
    0 bwdEq : (v : MaybeType x.req) -> (y : (MaybeAny x).res (fromIdris (toIdris v))) ->
              (MaybeToAny{x} ⨾ AnyToMaybe  {x}).bwd v y === replace {p = (MaybeAny x).res} (fromToEq v) y
    bwdEq (MkEx False ex2) y = absurd y.π1
    bwdEq (MkEx True ex2) y
        = sigEqToEq $ MkSigEq ?bb ?aa

||| Putting it all together
public export
AnyMaybeIso : ContIso (Any.Maybe x) (MaybeAny x)
AnyMaybeIso = MkGenIso
  AnyToMaybe
  MaybeToAny
  AnyToMaybeToAny
  MaybeToAnyToMaybe
public export
bwdMaybeAnyF: {0 x, y : Container} -> {mor : x =%> y} ->
              (v : Maybe x.req) ->
              Any y.res (map mor.fwd v) ->
              Any x.res v
bwdMaybeAnyF Nothing x = absurd x
bwdMaybeAnyF (Just v) w = Aye (mor.bwd v w.unwrap)

namespace Any
  public export
  map : x =%> y -> Any.Maybe x =%> Any.Maybe y
  map mor = (map mor.fwd) <! bwdMaybeAnyF

public export
maybeAnyPure : (x : Container) -> x =%> Any.Maybe x
maybeAnyPure x = Just <! (\_, v => v.unwrap)

public export
maybeJoin : Maybe (Maybe x) -> Maybe x
maybeJoin (Just (Just v)) = Just v
maybeJoin _ = Nothing

public export
maybeJoinBwd : (x : Maybe (Maybe a)) -> Any f (Maybe.maybeJoin x) -> Any (Any f) x
maybeJoinBwd (Just (Just v)) (Aye y) = Aye (Aye y)

public export
maybeAnyJoin : (x : Container) -> Any.Maybe (Any.Maybe x) =%> Any.Maybe x
maybeAnyJoin _ =
    maybeJoin <! maybeJoinBwd
public export
MaybeAll : Container -> Container
MaybeAll = (MaybeCont ▶)
namespace Maybe
  public export
  data All : (x -> Type) -> Maybe x -> Type where
    Nay : All pred Nothing
    Yay : {v : x} -> pred v -> All pred (Just v)

public export
obtain : All p (Just a) -> p a
obtain (Yay x) = x
0
Couldbe : (a -> Type) -> Maybe a -> Type
Couldbe p Nothing = ()
Couldbe p (Just x) = p x

-- This to ensure it's an isomoprhism with the `All` data
ToMaybe : {0 m : Maybe a} -> {0 p : a -> Type} -> All p m -> Couldbe p m
ToMaybe Nay = ()
ToMaybe (Yay x) = x

fromMaybe : {m : Maybe a} -> {0 p : a -> Type} -> Couldbe p m -> All p m
fromMaybe {m = Nothing} x = Nay
fromMaybe {m = (Just y)} x = Yay x
namespace All
  public export
  Maybe : Container -> Container
  Maybe c = (!>) (Maybe c.req) (All c.res)
toIdrisBwd : (v : MaybeType x.req) ->
             All x.res (toIdris v) -> (val : IsTrue v.ex1) -> x.res (v.ex2 val)
toIdrisBwd (MkEx False v2) x val = absurd val
toIdrisBwd (MkEx True v2) x TT = obtain x

public export
MaybeToAll : MaybeAll x =%> All.Maybe x
MaybeToAll =
    toIdris <! toIdrisBwd

fromIdrisBwd : (v : Maybe x.req) -> ((val : IsTrue ((fromIdris v).ex1)) -> x.res ((fromIdris v).ex2 val)) -> All x.res v
fromIdrisBwd Nothing f = Nay
fromIdrisBwd (Just y) f = Yay (f TT)

public export
AllToMaybe : All.Maybe x =%> MaybeAll x
AllToMaybe =
    fromIdris <! fromIdrisBwd

AllMaybeIso : {x : Container} ->
    MaybeToAll {x} ⨾ AllToMaybe {x} <%≡%> identity {a = MaybeAll x}
AllMaybeIso = MkDepLensEq
    fwdEq
    bwdEq
    where
      fwdEq : (v : MaybeType x.req) -> fromIdris (toIdris v) = v
      fwdEq (MkEx True p) = cong (MkEx True) (funExt $ \TT => Refl)
      fwdEq (MkEx False p) = cong (MkEx False) (allUninhabited _ _)

      0 bwdEq : (v : MaybeType x.req) ->
              (y : ((val : IsTrue ((fromIdris (toIdris v)).ex1)) ->
                   x .res ((fromIdris (toIdris v)).ex2 val))) ->
          let 0 p1 : (MaybeAll x).res v
              p1 = (MaybeToAll {x} ⨾ AllToMaybe {x}).bwd v y
              0 p2 : (MaybeAll x).res v
              p2 = (identity {a = MaybeAll x}).bwd v (replace {p = (MaybeAll x).res} (fwdEq v) y)
          in p1 === p2
      bwdEq (MkEx True v) y = funExtDep $ \TT => Refl
      bwdEq (MkEx False v) y = funExtDep $ \x => absurd x

MaybeAllIdristimesIso : {x : Container} ->
    AllToMaybe {x} ⨾ MaybeToAll {x} <%≡%> identity {a = All.Maybe x}
MaybeAllIdristimesIso = MkDepLensEq
    fwdEq
    bwdEq
    where
      fwdEq : (v : Maybe (x .req)) -> toIdris (fromIdris v) = v
      fwdEq Nothing = Refl
      fwdEq (Just y) = Refl
      bwdEq : (v : Maybe (x .req)) ->
              (y : All (x .res) (toIdris (fromIdris v))) ->
              let 0 p1 : (All.Maybe x).res v
                  p1 = (AllToMaybe {x} ⨾ MaybeToAll {x}).bwd v y
                  0 p2 : (All.Maybe x).res v
                  p2 = (identity {a = All.Maybe x}).bwd v (replace {p = (All.Maybe x).res} (fwdEq v) y)
              in p1 === p2
      bwdEq Nothing Nay = Refl
      bwdEq (Just z) (Yay y) = Refl

MaybeAllContIso : ContIso (MaybeAll x) (All.Maybe x)
MaybeAllContIso = MkGenIso
    MaybeToAll
    AllToMaybe
    AllMaybeIso
    MaybeAllIdristimesIso
public export
maybeAllPure : (x : Container) -> x =%> All.Maybe x
maybeAllPure _ = Just <! (\x, y => obtain y)

public export
maybeAllJoinBwd : (x : Maybe (Maybe a)) -> All f (Maybe.maybeJoin x) -> All (All f) x
maybeAllJoinBwd (Just (Just v)) (Yay y) = Yay (Yay y)
maybeAllJoinBwd (Just Nothing) b = Yay Nay
maybeAllJoinBwd Nothing b = Nay

public export
maybeAllJoin : (x : Container) -> All.Maybe (All.Maybe x) =%> All.Maybe x
maybeAllJoin _ =
    maybeJoin <!
    maybeAllJoinBwd

public export
bwdMaybeAllF: {0 x, y : Container} -> {mor : x =%> y} -> (v : Maybe x.req) ->
              All y.res (map mor.fwd v) -> All x.res v
bwdMaybeAllF Nothing Nay = Nay
bwdMaybeAllF (Just v) (Yay z) = Yay (mor.bwd v z)

public export
MaybeAllIdrisFunctor : a =%> b -> All.Maybe a =%> All.Maybe b
MaybeAllIdrisFunctor x =
    (map x.fwd) <! bwdMaybeAllF
