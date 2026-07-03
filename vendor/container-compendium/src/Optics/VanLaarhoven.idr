module Optics.VanLaarhoven

import Data.Container
import Data.Container.Kleene
import Data.Container.Descriptions.List
import Data.Container.Morphism
import Data.Container.Closed as C
import Data.Container.Maybe.Definition
import Data.Container.List.Functor
import Data.Category
import Data.Category.Endofunctor
import Data.Category.Functor
import Data.Category.Set
import Control.Monad.Identity
import Data.Coproduct
import Data.Product
import Data.Vect
import Data.Iso
import Data.Maybe.Any
import Data.Maybe.All
import Data.List.Equality

import Proofs

interface Functor f => Pointed (0 f : Type -> Type) where
  point : a -> f a
  presFn : (fn : a -> b) -> (x : a) -> map fn (point x) === point (fn x)

data CoStore : (b, a : Type) -> Type where
  Skip : a -> CoStore b a
  Cont : b -> (b -> a) -> CoStore b a

Functor (CoStore b) where
  map f (Skip x) = Skip (f x)
  map f (Cont x g) = Cont x (f . g)

Pointed (CoStore b) where
  point x = Skip x
  presFn fn x = Refl

Store : Type -> Type -> Type
Store b a = b * (b -> a)

[StoreFunc] Functor (Store b) where
  map f (x && k) = (x && f . k)
StoreFunctor : Type -> Endo Set
StoreFunctor b = MkFunctor
  (Store b)
  (\x, y, m, z => z.π1 && m . z.π2)
  (\_ => funExt $ \z => prodUniq _)
  (\x, y, z, f, g => funExt $ \w => Refl)
0 RefF : ((Type -> Type) -> Type) -> Type -> Type -> Type
RefF constraint a b = (0 f : Type -> Type) -> constraint f -> (b -> f b) -> (a -> f a)
namespace VLH
  public export
  0 Lens : Type -> Type -> Type
  Lens = RefF Functor
  public export
  0 Lens' : Type -> Type -> Type
  Lens' a b = (f : Endo Set) ->  (b -> f.mapObj b) -> a -> f.mapObj a
  public export
  0 Affine : Type -> Type -> Type
  Affine = RefF Pointed

  public export
  0 Traversal : Type -> Type -> Type
  Traversal = RefF Applicative
namespace Direct
  public export
  Lens : (a, b : Type) -> Type
  Lens a b = a -> (b * (b -> a))

  public export
  Affine : (a, b : Type) -> Type
  Affine a b = a -> CoStore b a

  public export
  Traversal : (a, b : Type) -> Type
  Traversal a b = a -> Σ (n : Nat) | (Vect n b * (Vect n b -> a))
namespace Lens
  directToVLH : {a, b : _} -> Direct.Lens a b -> VLH.Lens' a b
  directToVLH ls fn c x = fn.mapHom ? ? (ls x).π2 (c (ls x).π1)

  vlhToDirect : {a, b : _} -> VLH.Lens' a b -> Direct.Lens a b
  vlhToDirect f x = f (StoreFunctor b) (\bv => bv && id) x

  0 toFrom : (lens : Direct.Lens a b) -> vlhToDirect (directToVLH lens) ≡ lens
  toFrom lens = funExt $ \x => prodUniq _

  -- use yoneda
  0 fromTo : (lens : VLH.Lens' a b) -> directToVLH (vlhToDirect lens) ≡ lens
  fromTo ls = funExtDep $ \fn => funExt $ \mn => funExt $ \x =>
              ?ido

  lensIso : {a, b : _} -> Direct.Lens a b ≅ VLH.Lens' a b
  lensIso = MkIso
    directToVLH
    vlhToDirect
    fromTo
    toFrom
namespace Affine
  directToVLH : {a, b : _} -> Direct.Affine a b -> VLH.Affine a b
  directToVLH ls fn c f y = case ls y of
      (Skip z) => point z
      (Cont z z2) => map z2 (f z)

  vlhToDirect : {a, b : _} -> VLH.Affine a b -> Direct.Affine a b
  vlhToDirect f x = f (CoStore b) %search (\y => point y) x

  0 toFrom : (lens : Direct.Affine a b) -> (x : a) ->
             vlhToDirect (directToVLH lens) x ≡ lens x
  toFrom lens x with (lens x)
    toFrom lens x | (Skip y) = Refl
    toFrom lens x | (Cont y f) = let
        ff = VanLaarhoven.presFn {f = CoStore b} f
        in ?udia_rhsa_1

  -- use yoneda
  0 fromTo : (lens : VLH.Affine a b) -> directToVLH (vlhToDirect lens) ≡ lens
  fromTo ls = ?Yonedahui

  lensIso : {a, b : _} -> Direct.Affine a b ≅ VLH.Affine a b
  lensIso = MkIso
    directToVLH
    vlhToDirect
    fromTo
    (\x => funExt (toFrom x))
namespace Traversal
  directToVLH : {a, b : _} -> Direct.Traversal a b -> VLH.Traversal a b
  directToVLH ls fn c x = ?aha

  vlhToDirect : {a, b : _} -> VLH.Traversal a b -> Direct.Traversal a b
  vlhToDirect f x = ?hui

  0 toFrom : (lens : Direct.Traversal a b) -> vlhToDirect (directToVLH lens) ≡ lens
  toFrom lens = ?udia

  -- use yoneda
  0 fromTo : (lens : VLH.Traversal a b) -> directToVLH (vlhToDirect lens) ≡ lens
  fromTo ls = ?Yonedahui

  lensIso : {a, b : _} -> Direct.Traversal a b ≅ VLH.Traversal a b
  lensIso = MkIso
    directToVLH
    vlhToDirect
    fromTo
    toFrom
FromM : (Container -> Container) -> Type -> Type -> Type
FromM c a b = a -> Ex (c (b :- b)) a

namespace Dependent
  public export
  Lens, Affine, Traversal : (a, b : Type) -> Type
  Lens = FromM id
  Affine = FromM Any.Maybe
  Traversal = FromM All.List
StoreComonadIso : (b * (b -> a)) ≅ Ex (b :- b) a
StoreComonadIso = MkIso
  ?StoreComonadIso_rhs_0
  ?StoreComonadIso_rhs_1
  ?StoreComonadIso_rhs_2
  ?StoreComonadIso_rhs_3
namespace Affine
  toEx : a + (b * (b -> a)) -> Ex (All.Maybe (b :- b)) a
  toEx (<+ x) = MkEx Nothing (\_ => x)
  toEx (+> x) = MkEx (Just x.π1) (\y => x.π2 y.unwrap)

  fromEx : Ex (All.Maybe (b :- b)) a -> a + (b * (b -> a))
  fromEx (MkEx Nothing ex2) = <+ (ex2 Nay)
  fromEx (MkEx (Just ex1) ex2) = +> (ex1 && ex2 . Yay)

  0 fromToEx : (x : Ex (All.Maybe (b :- b)) a) -> toEx (fromEx x) = x
  fromToEx (MkEx Nothing ex2) = exEqToEqRw $ MkExEqRw Refl (\Nay => Refl)
  fromToEx (MkEx (Just ex1) ex2) = exEqToEqRw $ MkExEqRw Refl (\(Yay w) => Refl)

  toFromEx : (x : a + (b * (b -> a))) -> fromEx (toEx x) = x
  toFromEx (<+ x) = Refl
  toFromEx (+> x) = cong (+>) (prodUniq _)

  AffineMaybeIso : (a + b * (b -> a)) ≅ Ex (All.Maybe (b :- b)) a
  AffineMaybeIso = MkIso
    toEx
    fromEx
    fromToEx
    toFromEx
namespace Traversal
  Tr : (a, b : Type) -> Type
  Tr a b = Σ (n : Nat) | Vect n b * (Vect n b -> a)

  vectToList : Vect n a -> List a
  vectToList [] = []
  vectToList (x :: xs) = x :: vectToList xs

  AllToListVect : {xs : Vect len b} -> All (\_ => b) (vectToList xs) -> Vect len b
  AllToListVect {xs = [] } [] = []
  AllToListVect {xs = x :: xs } (y :: ys) = y :: AllToListVect ys

  toEx : Tr a b -> Ex (All.List (b :- b)) a
  toEx (len ## (ls && ks)) = MkEx (vectToList ls) (ks . AllToListVect)

  listAllToVect :
    (x1 : List b) ->
    Vect (length x1) b
  listAllToVect [] = []
  listAllToVect (x :: xs) = x :: listAllToVect xs

  vectToAll :
    (x1 : List b) ->
    Vect (length x1) b -> All (\x => b) x1
  vectToAll [] x1 = []
  vectToAll (_ :: _) (x :: xs) = x :: vectToAll _ xs

  fromEx : Ex (All.List (b :- b)) a -> Tr a b
  fromEx (MkEx x1 x2) = length x1 ## (listAllToVect x1 && x2 . vectToAll x1)

  vectReverse : (xs : List a) -> vectToList (listAllToVect xs) ≡ xs
  vectReverse [] = Refl
  vectReverse (x :: xs) = cong (x ::) (vectReverse xs)

  transportConsAll :
    {b : Type} -> {p : b -> Type} ->
    {x : b} -> {v : p x} -> {ls, ks : List b} ->
    {vs : Quantifiers.All.All p ls} ->
    {ys : Quantifiers.All.All p ks} ->
    {prf : ls === ks} ->
    transport
      (All p)
      (cong (Prelude.(::) x) prf) (v :: vs)
    ≡ v :: transport (Quantifiers.All.All p) prf vs
  transportConsAll {prf = Refl} = trans
    (applyTransport ? ?)
    (congDep (All.(::) v) (sym $ applyTransport ? ?))

  vectReverse² :
    (x1 : List b) ->
    (v : All (\x => b) (vectToList (listAllToVect x1))) ->
    (vectToAll x1 (listAllToVect x1))
    `ListAllEq` (replace {p = (All (\x => b))} (vectReverse x1) v)
  vectReverse² x1 v = ?vectReverse²_rhs

--   vectReverse¹ : {b : Type} ->
--     (x1 : List b) ->
--     (x : All (\x => b) (vectToList (listAllToVect x1)))->
--     vectToAll x1 (AllToListVect x) === x

  0 fromToEx : (x : Ex (All.List (b :- b)) a) -> toEx (fromEx x) = x
  fromToEx (MkEx x1 x2) = exEqToEq $ MkExEq (vectReverse x1)
     (\x => ?adh)

  0 toFromEx : (x : Tr a b) -> fromEx (toEx x) `SigEq` x
  toFromEx (Z ## ([] && x3)) = MkSigEq Refl (eqToIxEq $ cong ([] &&) (funExt $ \[] => Refl))
  toFromEx (S x ## (x1 :: x2 && x3)) = let
    MkSigEq e1 e2 = assert_total $ toFromEx (x ## (x2 && (x3 . (x1 ::))))
    in MkSigEq (cong S e1) ?toFromEx_rhs

  TraversalListIso : Tr a b ≅ Ex (All.List (b :- b)) a
  TraversalListIso = MkIso
    toEx
    fromEx
    fromToEx
    (\x => sigEqToEq $ toFromEx x)
  data StarSimple a = Done a | More a (a -> StarFw a)
  
namespace Lens
  directToDependent : {a, b : _} -> Direct.Lens a b -> Dependent.Lens a b
  directToDependent ls x = uncurry MkEx (ls x)

  dependentToDirect : {a, b : _} -> Dependent.Lens a b -> Direct.Lens a b
  dependentToDirect f x = (f x).ex1 && (f x).ex2

  0 toFrom' : (lens : Direct.Lens a b) -> dependentToDirect (directToDependent lens) ≡ lens
  toFrom' lens = funExt $ \x => ?udia

  -- use yoneda
  0 fromTo' : (lens : Dependent.Lens a b) -> directToDependent (dependentToDirect lens) ≡ lens
  fromTo' ls = ?Yonedahui

  lensIso' : {a, b : _} -> Direct.Lens a b ≅ Dependent.Lens a b
  lensIso' = MkIso
    directToDependent
    dependentToDirect
    fromTo'
    toFrom'
namespace Affine
  directToDependent : {a, b : _} -> Direct.Affine a b -> Dependent.Affine a b
  directToDependent ls = ?aha

  dependentToDirect : {a, b : _} -> Dependent.Affine a b -> Direct.Affine a b
  dependentToDirect f x = ?hui

  0 toFrom' : (lens : Direct.Affine a b) -> dependentToDirect (directToDependent lens) ≡ lens
  toFrom' lens = ?udia

  -- use yoneda
  0 fromTo' : (lens : Dependent.Affine a b) -> directToDependent (dependentToDirect lens) ≡ lens
  fromTo' ls = ?Yonedahuil

  lensIso' : {a, b : _} -> Direct.Affine a b ≅ Dependent.Affine a b
  lensIso' = MkIso
    directToDependent
    dependentToDirect
    fromTo'
    toFrom'
namespace Traversal
  directToDependent : {a, b : _} -> Direct.Traversal a b -> Dependent.Traversal a b
  directToDependent ls = ?aha2

  dependentToDirect : {a, b : _} -> Dependent.Traversal a b -> Direct.Traversal a b
  dependentToDirect f x = ?hui2j

  0 toFrom' : (lens : Direct.Traversal a b) -> dependentToDirect (directToDependent lens) ≡ lens
  toFrom' lens = ?udiak

  -- use yoneda
  0 fromTo' : (lens : Dependent.Traversal a b) -> directToDependent (dependentToDirect lens) ≡ lens
  fromTo' ls = ?Yonedahuik

  lensIso' : {a, b : _} -> Direct.Traversal a b ≅ Dependent.Traversal a b
  lensIso' = MkIso
    directToDependent
    dependentToDirect
    fromTo'
    toFrom'
0 MonadicTraversal : Type -> Type -> Type
MonadicTraversal = RefF Monad
{-
0
StoreF : Type -> Type -> Type
StoreF b a = forall f. Functor f => (b -> f b) -> f a

record CartStore (0 b : Type) (a : Type) where
  constructor MkCartStore
  n : Nat
  ls : Vect n b
  ks : Vect n b -> a

Functor (CartStore b) where
  map f (MkCartStore n x k) = MkCartStore n x (f . k)

Applicative (CartStore b) where
  pure x = MkCartStore Z [] (const x)
  (<*>) (MkCartStore n1 x1 k1) (MkCartStore n2 x2 k2)
      = MkCartStore (n1 + n2) (x1 ++ x2) (\xs => k1 (take n1 xs) (k2 (drop n1 xs)))

record CartStore' (b, a : Type) where
  constructor MkCartStore'
  ls : List b
  ks : All (\_ => b) ls -> a

0
CartStoreF : Type -> Type -> Type
CartStoreF b a = (f : _) -> (app : Applicative f) -> (b -> f b) -> f a

record CompStore (b, a : Type) where
  constructor MkCompStore
  ls : StarShp (b :- b)
  ks : StarPos (b :- b) ls -> a

Functor (CompStore b) where
  map f (MkCompStore x k) = MkCompStore x (f . k)

Applicative (CompStore b) where
  pure x = MkCompStore Done (const x)
  (<*>) (MkCompStore x1 k1) (MkCompStore x2 k2) = ?whole
--       = MkCompStore (n1 + n2) (x1 ++ x2) (\xs => k1 (take n1 xs) (k2 (drop n1 xs)))

compJoin : CompStore b (CompStore b a) -> CompStore b a
compJoin (MkCompStore ls ks) = ?compJoin_rhs_0

Monad (CompStore b) where
  join = compJoin

0
CompStoreF : Type -> Type -> Type
CompStoreF b a = forall f. Monad f => (b -> f b) -> f a

0
Lens : Type -> Type -> Type
Lens b a = a -> Store b a

0
LensF : Type -> Type -> Type
LensF  b a = a -> StoreF b a

0
TravF : Type -> Type -> Type
TravF b a = a -> CartStoreF b a

0
MonF : Type -> Type -> Type
MonF b a = a -> CompStoreF b a
0 LensFamily : (a, b, c, d : Type) -> Type
LensFamily a b c d =
  forall f. Functor f =>
  (c -> f d) -> a -> f b

lensFToDLens : LensF b a -> a :- a =&> (b :- b)
lensFToDLens f = !! \x => let gg = f x {f = Store b} @{StoreFunc} (\z => (z && id)) in gg.π1 ## gg.π2

DLensToF : a :- a =&> (b :- b) -> LensF b a
DLensToF (!! k) y g = let kk = k y in map (\q => kk.π2 q) (g kk.π1)
0 Traversal : (a, b, c, d : Type) -> Type
Traversal a b c d =
  forall f. (app : Applicative f) =>
  (c -> f d) -> a -> f b

VectToList : Vect n a -> List a
VectToList [] = []
VectToList (x :: xs) = x :: VectToList xs

AllToListVect : {xs : Vect len b} -> All (\_ => b) (VectToList xs) -> Vect len b
AllToListVect {xs} _ = xs

traversalToDLens : TravF b a -> a :- a =&> All.List (b :- b)
traversalToDLens trav = !! \x => let
    MkCartStore len xs ks = trav x (CartStore b) %search pure
  in VectToList xs ## ks . AllToListVect {xs}


list2ConstAll : (xs : List a) -> All (\_ => a) xs
list2ConstAll [] = []
list2ConstAll (x :: xs) = x :: list2ConstAll xs

dlensToTraversal : a :- a =&> All.List (b :- b) -> TravF b a
dlensToTraversal (k) y func app g = case k.fn y of
  ([] ## p2) => pure (p2 [])
  ((x :: xs) ## p2) => let gv = g x
                           pp = p2 <$> ((::) <$> gv <*> pure (list2ConstAll xs))
                           rr : func _ = dlensToTraversal k <$> pp
                           -- ss : func (Applicative func -> (b -> func b) -> func a) = rr <*> pure func
                           -- failure due to lack of parametricity
                        in pp
interface Functor f => Pointed f where
  point : a -> f a

0 AffineTraversal : (a, b, c, d : Type) -> Type
AffineTraversal a b c d =
  forall f. Pointed f =>
  (c -> f d) -> a -> f b
0 MonadicTraversal : (a, b, s, t : Type) -> Type
MonadicTraversal a b s t =
  (0 f : Type -> Type) -> (m : Monad f) =>
  (a -> f s) -> t -> f b

atob :
  StarShp (a :- a) ->
  StarShp (b :- b)
atob Done = Done
atob (More x f) = More ?db ?atob_rhs_1

MonadicToDLens : forall a, b. MonF b a -> (a :- a) =&> Star (b :- b)
MonadicToDLens tr = !! \x => let
    cs : CompStore b a
    cs = tr {f = CompStore b} x pure
    in cs.ls ## cs.ks

DLensToMonadoc : a :- a =&> Star (b :- b) -> MonF b a
DLensToMonadoc (!! k) x g =
    elimSig {d = \_ => f a} (k x) $ \x1, x2, p1, p2 =>
        elimStar {d = \_ => f a} x1
            ((\pq => pure $ x2 $ rewrite pq in StarU))
            (\p1, p2, pq => (g p1) >>= \gv =>
                let newX = (x2 (rewrite pq in StarM gv (mapStarToPos (p2 gv))))
                in ?huia
            )

            {-
0
DLensMonadDLens : (dlens : a :- a =&> Star (b :- b)) ->
                  (x : a) ->
                  (MonadicToDLens (DLensToMonadoc dlens)).fn x `SigEqS` dlens.fn x
DLensMonadDLens (!! fn) x with (fn x)
  DLensMonadDLens (!! fn) x | (Done ## p2) = MkSigEqS Refl (funExt $ \StarU => ?aa_rhsb_02)
  DLensMonadDLens (!! fn) x | (More p p1 ## p2) = MkSigEqS
      ?bdbd
      ?aa_rhsb_0


    {-
0 DVLH : (a, b : Container) -> Type
DVLH a b =
  (0 f : Type -> Type) -> Functor f ->
  ((x : a.req) -> f (a.res x)) -> ((x : b.req) -> f (b.res x))
compose : DVLH a b -> DVLH b c -> DVLH a c
compose g1 g2 f c x = g2 f c (g1 f c x)
identity : DVLH a a
identity f c = id

VLHCat : Category Container
VLHCat = MkCategory
   DVLH
   (\cont => identity)
   compose
   (\_, _, lens => funExtDep0 $ \v1 => funExt $ \v2 => funExt $ \v3 => Refl)
   (\_, _, lens => funExtDep0 $ \v1 => funExt $ \v2 => funExt $ \v3 => Refl)
   (\_, _, _, _, f, g, h => funExtDep0 $ \v1 => funExt $ \v2 => funExt $ \v3 => Refl)
