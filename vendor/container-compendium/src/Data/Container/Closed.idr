module Data.Container.Closed

import public Data.Container.Closed.Definition
import public Data.Container.Definition
import public Data.Container.Apply.Definition
import Data.Container.Extension
import Data.Container.Morphism.Definition
import Data.Container.Product
import Data.Container.Tensor.Definition
import Data.Container.Coproduct.Definition
-- import Data.Container.Maybe.Desc
import Data.Container.Maybe.Functor
import Data.Container.List.Desc
import Data.Container.List.Functor

import Data.List1
import public Data.Sigma
import Data.Coproduct
import Data.Product
import Data.Iso
import Data.Maybe.Any
import Data.Maybe.All
import Data.List.Quantifiers

import Proofs

import Optics.Prism
import Data.DPair
import Data.Maybe

%hide Prelude.(&&)
public export
toClosed : a =%> b -> a =&> b
toClosed mor = !!
  \x => mor.fwd x  ## (\y => mor.bwd x y)

public export
fromClosed : a =&> b -> a =%> b
fromClosed (!! g) =
  (\x => (g x).π1) <!
  (\x, y => (g x).π2 y)

public export
closedIso : a =&> b ≅ (a =%> b)
closedIso = MkIso
  fromClosed
  toClosed
  (\(x <! y) => Refl)
  (\(!! fn) => cong (!!) (funExtDep $ \nx => sigmaProjId _))
namespace Any
  namespace List

    mapSucc :
       (x2 : b.response x1 -> a.response x) ->
       (ys' : Any b.response ys -> Quantifiers.Any.Any a.response xs) ->
       Any b.response (x1 :: ys) -> Any a.response (x :: xs)
    mapSucc x2 ys' (Here y) = Here (x2 y)
    mapSucc x2 ys' (There y) = There (ys' y)

    map' : {0 a, b : Container} -> a =&> b ->
           (xs : List a.request) -> Σ (ys : List b.request) | Any b.response ys -> Any a.response xs
    map' _ [] = [] ## absurd
    map' m (x :: xs) = let (x1 ## x2) = m.fn x
                           (ys ## ys') = map' m xs
                        in x1 :: ys ## mapSucc x2 ys'

    public export
    map : a =&> b -> Any.List a =&> Any.List b
    map m = !! (map' m)

  namespace Maybe
    public export
    (>=>) : a =&> Any.Maybe b -> b =&> Any.Maybe c -> a =&> Any.Maybe c

    public export
    map : a =&> b -> Any.Maybe a =&> Any.Maybe b
    map x = !! \case Nothing => Nothing ## absurd
                     (Just y) => let r = x.fn y in Just r.π1 ## \case (Aye v) => Aye (r.π2 v)

    export
    or : (m1, m2 : a =&> Any.Maybe b) -> a =&> Any.Maybe b
    or m1 m2 = !! \x => case m1.fn x of
                             Nothing ## _ => m2.fn x
                             (Just v) ## k => Just v ## k

    export
    tryAll : List (a =&> Any.Maybe b) -> a =&> Any.Maybe b
    tryAll xs = foldl or (!! \x => Nothing ## absurd) xs

namespace All
  namespace List
    public export
    map : a =&> b -> All.List a =&> All.List b

  namespace Maybe
    public export
    map : a =&> b -> All.Maybe a =&> All.Maybe b
    map x = !! \case Nothing => Nothing ## const Nay
                     (Just y) => let r = x.fn y in Just r.π1 ## \case (Yay v) => Yay (r.π2 v)

public export
State : Container -> Type
State a = I =&> a

public export
(.getVal) : State a -> a.request
(.getVal) m = π1 (m.fn ())

public export
state : a.request -> State a
state x = !! const (x ## const ())

public export
Costate : Container -> Type
Costate a = a =&> I

public export
runCostate : Costate a -> (x : a.request) -> a.response x
runCostate m x = (m.fn x).π2 ()

public export
costate : ((x : a.request) -> a.response x) -> Costate a
costate f = !! \x => () ## const (f x)

export
comult : Monad f => f • a =&> f • (f • a)
comult = !! \x => x ## join

export
counit : Monad f => f • a =&> a
counit = !! \x => x ## pure

export
fapplyMap : Functor f => a =&> b -> f • a =&> f • b
fapplyMap (!! fn) = !! \x => let x ## y = fn x in x ## map y

export
pureRight : Monad f => f • a =&> b -> f • a =&> f • b
pureRight m = comult |&> fapplyMap m {f}

export
anyPure : a =&> Any.List a
anyPure = !! \x => [x] ## \(Here y) => y

export
distrAnyMaybe : {0 a : Container} ->
                {ls : List a.request} ->
                Any.Any (Maybe . a.response) ls ->
                Maybe (Any.Any a.response ls)
distrAnyMaybe (Here x) = map Here x
distrAnyMaybe (There x) = map There (distrAnyMaybe x)

distrAllMaybe : {0 a : Container} ->
                {0 ls : List a.request} ->
                All.All (Maybe . a.response) ls ->
                Maybe (All.All a.response ls)
distrAllMaybe [] = Just []
distrAllMaybe (x :: y) = (::) <$> x <*> distrAllMaybe y

maybeListAnyDistrib : Maybe • Any.List a =&> Any.List (Maybe • a)
maybeListAnyDistrib = !! \x => x ## distrAnyMaybe

maybeListAllDistrib : Maybe • All.List a =&> All.List (Maybe • a)
maybeListAllDistrib = !! \x => x ## distrAllMaybe

replicateAll : b -> (ls : List a) ->  All.All (\_ => b) ls
replicateAll v [] = []
replicateAll v (x :: xs) = v :: replicateAll v xs

AllListCostate : All.List I =&> I
AllListCostate = !! \xx => () ## (\_ => replicateAll () xx)

anyChoice : {0 a : Container} -> ((x : a.request) -> Maybe (a.response x)) -> (xs : List a.request) -> Maybe (Any a.response xs)
anyChoice f [] = Nothing
anyChoice f (x :: xs) =
  map Here (f x) <|> map There (anyChoice f xs)

-- Given a `Maybe • a` costate, pick the first success.
AnyChoice : Costate (Maybe • a) -> Costate (Maybe • Any.List a)
AnyChoice m = costate (\x => anyChoice (\y => (m.fn y).π2 ()) x)

export
Transitive Container (=&>) where
  transitive = (|&>)

export
Reflexive Container (=&>) where
  reflexive = identity _

export
Preorder Container (=&>) where
