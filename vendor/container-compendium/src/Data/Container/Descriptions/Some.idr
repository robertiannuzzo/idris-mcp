module Data.Container.Descriptions.Some

import Data.Container
import Data.Container.Category
import Data.Container.Descriptions.List
import Data.Container.Morphism
import Data.Container.Morphism.Eq

import Data.Category.Functor

import Data.Fin
import Data.Iso
import Data.Some
import Data.Product
import Data.Coproduct
import Data.List.Quantifiers
import Data.String

import Syntax.PreorderReasoning

import Proofs.Congruence
import Proofs.Extensionality

import System.File

%hide Prelude.(&&)
SomeC : Container -> Container
SomeC c = (!>) (List c.message) (Some c.response)
splitFile : String -> List String
splitFile = lines

rebuild : (input : String) -> Some (const Nat) (lines input) -> String
rebuild input x = unlines (map (renderError (lines input)) (absents x))
  where
  absents : Some p xs -> List (Fin (List.length xs))
  absents Empty = []
  absents (Take x xs) = map FS (absents xs)
  absents (Drop xs) = FZ :: map FS (absents xs)
  renderError : (ls : List String) -> Fin (length ls) -> String
  renderError ls idx = "Error at line \{show $ finToNat idx}: \{index' ls idx}"
lineError : (String :- String) =%> ((ls : List String) !> Some (const Nat) ls)
lineError = splitFile <! rebuild
runParser : Costate (String :- Maybe Nat)
runParser = costate parsePositive

main : IO ()
main = do
  fileContent <- readFile "file"
  run (renderError)
fromSomeBack : {0 a : Container} -> (xs : List a.shp) ->
               All (\x => () + a.pos x.π2) (listMap (\arg => () && arg) xs) ->
               Some a.pos xs
fromSomeBack [] [] = Empty
fromSomeBack (x :: xs) (+> y :: ys) = Take y (fromSomeBack xs ys)
fromSomeBack (x :: xs) (<+ y :: ys) = Drop (fromSomeBack xs ys)

fromSome : SomeC a =%> ListAllIdris (CUnit * a)
fromSome = MkMorphism (listMap (() &&)) fromSomeBack

toSomeBack : {0 a : Container} -> (xs : List (() * a .shp)) -> Some (a .pos) (listMap π2 xs) -> All (\x => () + a .pos (x .π2)) xs
toSomeBack [] Empty = []
toSomeBack (x :: xs) (Take y z) = +> y :: toSomeBack xs z
toSomeBack (x :: xs) (Drop y) = <+ () :: toSomeBack xs y

toSome : ListAllIdris (CUnit * a) =%> SomeC a
toSome = MkMorphism (listMap π2) toSomeBack

mapProductComposeInverse : (v : List a) -> listMap π2 (listMap (() &&) v) = v
mapProductComposeInverse v = Calc $
    |~ listMap π2 (listMap (() &&) v)
    ~~ listMap (π2 . (() &&)) v ..<(allCompFwd π2 (() &&) v)
    ~~ listMap id v             ...(cong (\x => listMap x v) Refl)
    ~~ v                        ...(listMapId v)

takeInj1 : Take x y = Take x' y' -> x = x'
takeInj1 Refl = Refl

-- %unbound_implicits off
-- fromToSomeBackward :
--     {0 a : Container} ->
--     (x1 : List (a .shp)) ->
--     (x2 : Some (a .pos) (listMap π2 (listMap (\arg => () && arg) x1))) ->
--     fromSomeBack {a} x1 (toSomeBack {a} (listMap (\arg => () && arg) x1) x2) === replace {p = Some a.pos} (mapProductComposeInverse x1) x2
-- fromToSomeBackward [] Empty = Refl
-- fromToSomeBackward (x :: xs) (Take y z) = cong (rewrite sym $ mapProductComposeInverse (x :: xs) in Take y) ?bdb
-- fromToSomeBackward (x :: xs) (Drop y) = ?fromToSomeBackward_rhs_3
-- fromToSomeBackward (x :: xs) Empty = ?fromToSomeBackward_rhs_4
--
-- 0 fromToSome : {a : Container} -> (fromSome {a} |> toSome {a}) `DepLensEq` identity
-- fromToSome = MkDepLensEq mapProductComposeInverse ?ahudihu -- fromToSomeBackward
--
-- toFromSome : {a : Container} -> toSome {a} |> fromSome {a} `DepLensEq` identity
-- toFromSome = MkDepLensEq ?fromToSome_rhs_02 ?fromToSome_rhs_123
AllM : {x : Type} -> (x -> Type) -> List x -> Type
AllM f = All (Maybe . f)

someToAll : {0 a : Type} -> {0 p : a -> Type} -> {ls : List a} -> Some p ls -> AllM p ls
someToAll {ls = []} Empty = []
someToAll {ls = (y :: xs)} (Take x z) = Just x :: someToAll z
someToAll {ls = (y :: xs)} (Drop x) = Nothing :: someToAll x

allToSome : {0 a : Type} -> {0 p : a -> Type} -> {ls : List a} -> AllM p ls -> Some p ls
allToSome {ls = []} x = Empty
allToSome {ls = (y :: xs)} (Nothing :: z) = Drop (allToSome z)
allToSome {ls = (y :: xs)} ((Just x) :: z) = Take x (allToSome z)

someAllSome : {ls : List a} -> (x : Some p ls) -> allToSome (someToAll x) === x
someAllSome {ls = []} Empty = Refl
someAllSome {ls = (y :: xs)} (Take x z) = cong (Take x) (someAllSome z)
someAllSome {ls = (y :: xs)} (Drop x) = cong Drop (someAllSome x)

allSomeAll : {ls : List a} -> (x : AllM p ls) -> someToAll (allToSome x) === x
allSomeAll {ls = []} [] = Refl
allSomeAll {ls = (y :: xs)} (Nothing :: z) = cong (Nothing ::) (allSomeAll z)
allSomeAll {ls = (y :: xs)} ((Just x) :: z) = cong (Just x ::) (allSomeAll z)

0
AllMSomeIso : Iso (AllM p ls) (Some p ls)
AllMSomeIso = MkIso allToSome someToAll someAllSome allSomeAll
AllMaybe : Container -> Container
AllMaybe c = (x : List c.shp) !> AllM c.pos x

SomeToAllMaybe : SomeC c =%> AllMaybe c
SomeToAllMaybe = MkMorphism id (\ls => allToSome)

AllMaybeToSome : AllMaybe c =%> SomeC c
AllMaybeToSome = MkMorphism id (\ls => someToAll)

SomeAllSome : {0 c : Container} -> SomeToAllMaybe {c} |> AllMaybeToSome {c}
              `DepLensEq` identity {a = SomeC c}
SomeAllSome = MkDepLensEq (\_ => Refl) (\x, y => someAllSome y)

AllSomeAll : {0 c : Container} -> AllMaybeToSome {c} |> SomeToAllMaybe {c}
             `DepLensEq` identity {a = AllMaybe c}
AllSomeAll = MkDepLensEq (\_ => Refl) (\x => allSomeAll)

AllMaybeSomeIso : {0 c : Container} -> ContIso (AllMaybe c) (SomeC c)
AllMaybeSomeIso = MkGenIso
    AllMaybeToSome
    SomeToAllMaybe
    AllSomeAll
    SomeAllSome
AllMaybeLift : Container -> Container
AllMaybeLift c = ListAllIdris (Lift Maybe c)

LiftSame : AllMaybeLift c === AllMaybe c
LiftSame = Refl
SomeIsFunctor : Functor Cont Cont
SomeIsFunctor = ?SomeIsFunctor_rhs
SomeIsComonad : Monad Cont.op Cont.op
