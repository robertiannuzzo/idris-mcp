module Data.Container.Morphism.Kleene

import Data.Container.Definition
import Data.Container.Apply.Definition
import Data.Container.Sequence.Definition
import Data.Container.Kleene
import Data.Container.Coproduct
import Data.Container.Extension
import Data.Container.Morphism.Definition
import Data.Container.Morphism.Context
import Data.Product
import Data.Coproduct
import Data.Sigma
public export
mapStarFw : (a =%> b) -> StarFw a -> StarFw b
mapStarFw x Done = Done
mapStarFw x (More p1 p2) =
  More (x.fwd p1) (\y => assert_total $ mapStarFw x (p2 (x.bwd p1 y)))

public export
mapStarUntil : (Maybe • a =%> b) -> StarFw a -> StarFw b
mapStarUntil m Done = Done
mapStarUntil m (More p1 p2) =
  More (m.fwd p1) (\y => case m.bwd p1 y of
         Just x => assert_total $ mapStarUntil m (p2 x)
       ; Nothing => Done)

public export
mapStarBw : (mor : a =%> b) -> (x : StarFw a) -> StarBw b (mapStarFw mor x) -> StarBw a x
mapStarBw y Done z = StarU
mapStarBw y (More p1 p2) (StarM z1 z2) =
  StarM (y.bwd p1 z1) (mapStarBw y (p2 (y.bwd p1 z1)) z2)

public export
map_kleene : a =%> b -> Star a =%> Star b
map_kleene mor = mapStarFw mor <! mapStarBw mor

join_star : forall a. StarFw (Star a) -> StarFw a

join_star Done = Done
join_star (More Done p2) = Done
join_star (More (More p1 p2) p3) = More p1 p2

public export
single : a.req -> StarFw a
single x = More x (\_ => Done)

public export
pure : a =%> Star a
pure =
    (single {a}) <!
    (\x, (StarM y1 y2) => y1)

public export
unit_kleene : Star I =%> I
unit_kleene = const () <! bwd
  where
    bwd : (x : StarFw I) -> Unit -> StarBw I x
    bwd Done y = StarU
    bwd (More () p2) () = StarM () (bwd (p2 ()) ())

export
Show a.req => Show (StarFw a) where
  show Done = "done"
  show (More x f) = "more: " ++ show x

namespace Tensor
  -- λ x : Container -> μy . I + x ⊗ y
  data TensorShp : Container -> Type where
    Done : TensorShp c
    More : c.req * TensorShp c -> TensorShp c

  TensorPos : (c : Container) -> TensorShp c -> Type
  TensorPos c Done = Unit
  TensorPos c (More (head && tail)) = (c.res head) * (TensorPos c tail)

  Tensor : Container -> Container
  Tensor c = (!>) (TensorShp c) (TensorPos c)

-- Absord one layed of composition into a Kleene star
public export
absorb : a ▷ Star a =%> Star a
absorb = (\(MkEx x y) => More x y) <! \(MkEx x y), (StarM z w) => z ## w

-- Decompose one layer of the kleene star into either the unit, or more computation
export
decomposeStar : Star a =%> I + (a ▷ Star a)
decomposeStar = peel <! peelBack
  where
    peel : StarFw a -> () + Ex a (StarFw a)
    peel Done = <+ ()
    peel (More x f) = +> MkEx x f

    peelBack : (x : StarFw a) -> (I + (a ▷ Star a)).res (peel x) -> StarBw a x
    peelBack Done y = StarU
    peelBack (More x f) y = StarM y.π1 y.π2

export
decomposeStar' : Star a =%> I + Star a
decomposeStar' = decomposeStar |%> identity I ~+~ absorb

splitFwd : ((I + a) ▷ b).req -> b.req + Ex a b.req
splitFwd (MkEx (<+ x) ex2) = <+ ex2 ()
splitFwd (MkEx (+> x) ex2) = +> MkEx x ex2

splitBwd : (x : ((I + a) ▷ b).req) -> (b + (a ▷ b)).res (splitFwd {a} {b} x) ->
           ((I + a) ▷ b).res x
splitBwd (MkEx (<+ x) ex2) y = () ## y
splitBwd (MkEx (+> x) ex2) y = y

splitA : (I + a) ▷ b =%> b + (a ▷ b)
splitA = splitFwd
    <! splitBwd


rec : (x : StarFw I) -> StarBw I x
rec Done = StarU
rec (More x f) = StarM () (rec (f ()))

export
allUnits : Star I =%> I
allUnits = const () <! \x, y => rec x


export
commuteMaybeStar : Maybe • Star a =%> Star (Maybe • a)
commuteMaybeStar = commuteShp <! commutePos
  where
    commuteShp : StarFw a -> StarFw ((x : a.req) !> Maybe (a .res x))
    commuteShp Done = Done
    commuteShp (More x f) = More x $ maybe Done (commuteShp . f)

    commutePos : (x : StarFw a) -> (Star (Maybe • a)).res (commuteShp x) -> Maybe (StarBw a x)
    commutePos Done StarU = Just StarU
    commutePos (More x f) (StarM Nothing StarU) = Nothing
    commutePos (More x f) (StarM (Just y) z) = map (StarM y) (commutePos (f y) z)

export
commuteEitherStar : Either e • Star a =%> Star (Either e • a)
commuteEitherStar = commuteShp <! commutePos
  where
    commuteShp : StarFw a -> StarFw ((x : a.req) !> Either e (a .res x))
    commuteShp Done = Done
    commuteShp (More x f) = More x $ either (const Done) (commuteShp . f)

    commutePos : (x : StarFw a) -> (Star (Either e • a)).res (commuteShp x) -> Either e (StarBw a x)
    commutePos Done StarU = Right StarU
    commutePos (More x f) (StarM (Left e) StarU) = Left e
    commutePos (More x f) (StarM (Right y) z) = map (StarM y) (commutePos (f y) z)

{-
covering
recc : a =%> Star a -> (x : StarFw a) -> StarBw a x
recc m Done = StarU
recc (m1 <! m2) (More x f) =
  let rec1 = recc (m1 <! m2) (m1 x)
      xv = m2 x rec1
      rec2 = recc (m1 <! m2) (f xv)
  in StarM xv rec2

covering export
loop : a =%> Star a -> Costate (Star a)
loop m = const () <! \x, _ => recc m x

{-
namespace UniversalComp
  -- λ x : Container -> μy . I + x ▶ y
  data StarFw : Container -> Type where
    Done : StarFw c
    More : Ex c (StarFw c) -> StarFw c

  StarBw : (c : Container) -> StarFw c -> Type
  StarBw c Done = Unit
  StarBw c (More (x1 ## x2)) = (x : c.res x1) -> StarBw c (x2 x)

  Star : Container -> Container
  Star c = (!>) (StarFw c) (StarBw c)

covering
data StarFwBuilder :
    (act : Container -> Type -> Type) ->
    Container -> Type where
  Done : StarFwBuilder act c
  More : {act : Container -> Type -> Type} ->
         {rest : StarFwBuilder act c} ->
         (act c (StarFwBuilder act c)) -> StarFwBuilder act c


{-
StarBuilder : (act : Container -> Type -> Type) ->
              (bwd : (c : Container) -> {x : Type} -> Act c x) -> Container -> Container
StarBuilder act c = (!>) (StarFwBuilder act c) StarBwBuilder
  where
    StarBwBuilder : StarFwBuilder act c -> Type
    StarBwBuilder arg = ?hol
