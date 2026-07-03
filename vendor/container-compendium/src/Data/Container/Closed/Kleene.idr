module Data.Container.Closed.Kleene

import Data.Container.Definition
import Data.Container.Lift
import Data.Container.Sequence.Definition
import Data.Container.Kleene
import Data.Container.Closed.Coproduct
import Data.Container.Extension
import Data.Container.Closed as C
import Data.Container.Morphism.Kleene as K
import Data.Product
import Data.Coproduct
import Data.Sigma
import Debug.Trace

public export
mapStarFw : (a =&> b) -> StarFw a -> StarFw b
mapStarFw m = K.mapStarFw (fromClosed m)

public export
mapStarUntil : (Maybe • a =&> b) -> StarFw a -> StarFw b
mapStarUntil m = K.mapStarUntil (fromClosed m)

public export
mapStarBw : (mor : a =&> b) -> (x : StarFw a) -> StarBw b (mapStarFw mor x) -> StarBw a x
mapStarBw m = K.mapStarBw (fromClosed m)

public export
map_kleene : a =&> b -> Star a =&> Star b
map_kleene mor = !! \x => mapStarFw mor x ## mapStarBw mor x

join_star : forall a. StarFw (Star a) -> StarFw a

join_star Done = Done
join_star (More Done p2) = Done
join_star (More (More p1 p2) p3) = More p1 p2


public export
pure : a =&> Star a
pure = !! \x => single x ## (\(StarM y _) => y)

public export
unit_kleene : Star I =&> I
unit_kleene = !! \x => () ## const (bwd x)
  where
    bwd : (x : StarFw I) -> StarBw I x
    bwd Done = StarU
    bwd (More () p2) = StarM () (bwd (p2 ()))

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
absorb : a ▷ Star a =&> Star a
absorb = ?adi -- (\(MkEx x y) => More x y) <! \(MkEx x y), (StarM z w) => z ## w

covering
recc : a =&> Star a -> (x : StarFw a) -> StarBw a x
-- recc m Done = StarU
-- recc (m1 <! m2) (More x f) =
--   let rec1 = recc (m1 <! m2) (m1 x)
--       xv = m2 x rec1
--       rec2 = recc (m1 <! m2) (f xv)
--   in StarM xv rec2

covering export
loop : a =&> Star a -> Costate (Star a)
-- loop m = const () <! \x, _ => recc m x

{-
-- Decompose one layer of the kleene star into either the unit, or more computation
export
decomposeStar : Star a =&> I + (a ▷ Star a)
decomposeStar = ?add
  where
    peel : StarFw a -> () + Ex a (StarFw a)
    peel Done = <+ ()
    peel (More x f) = +> MkEx x f

    peelBack : (x : StarFw a) -> (I + (a ▷ Star a)).res (peel x) -> StarBw a x
    peelBack Done y = StarU
    peelBack (More x f) y = StarM y.π1 y.π2

export
decomposeStar' : Star a =&> I + Star a
decomposeStar' = Closed.Kleene.decomposeStar |&> C.identity I ~+~ Closed.Kleene.absorb

splitFwd : ((I + a) ▷ b).req -> b.req + Ex a b.req
splitFwd (MkEx (<+ x) ex2) = <+ ex2 ()
splitFwd (MkEx (+> x) ex2) = +> MkEx x ex2

splitBwd : (x : ((I + a) ▷ b).req) -> (b + (a ▷ b)).res (splitFwd {a} {b} x) ->
           ((I + a) ▷ b).res x
splitBwd (MkEx (<+ x) ex2) y = () ## y
splitBwd (MkEx (+> x) ex2) y = y

splitA : (I + a) ▷ b =&> b + (a ▷ b)
-- splitA = splitFwd <! splitBwd

-- run the kleen star until there is no more input
export %inline
traceValMsg : Show a => String -> a -> a
traceValMsg msg = traceValBy ((msg ++) . show)

Trace : Show a.req => a =&> a
-- Trace = id <! \x, y => trace """
--                        fwd input: \{show x}
--                        """ y

rec : (x : StarFw I) -> StarBw I x
rec Done = StarU
rec (More x f) = StarM () (rec (f ()))

export
allUnits : Star I =&> I
allUnits = !! \x => () ## const (rec x)

export
commuteMaybeStar : Maybe • Star a =&> Star (Maybe • a)
-- commuteMaybeStar = commuteShp <! commutePos
--   where
--     commuteShp : StarFw a -> StarFw ((x : a.req) !> Maybe (a .res x))
--     commuteShp Done = Done
--     commuteShp (More x f) = More x $ maybe Done (commuteShp . f)
--
--     commutePos : (x : StarFw a) -> (Star (Maybe • a)).res (commuteShp x) -> Maybe (StarBw a x)
--     commutePos Done StarU = Just StarU
--     commutePos (More x f) (StarM Nothing StarU) = Nothing
--     commutePos (More x f) (StarM (Just y) z) = map (StarM y) (commutePos (f y) z)

export
commuteEitherStar : Either e • Star a =&> Star (Either e • a)
-- commuteEitherStar = commuteShp <! commutePos
--   where
--     commuteShp : StarFw a -> StarFw ((x : a.req) !> Either e (a .res x))
--     commuteShp Done = Done
--     commuteShp (More x f) = More x $ either (const Done) (commuteShp . f)
--
--     commutePos : (x : StarFw a) -> (Star (Either e • a)).res (commuteShp x) -> Either e (StarBw a x)
--     commutePos Done StarU = Right StarU
--     commutePos (More x f) (StarM (Left e) StarU) = Left e
--     commutePos (More x f) (StarM (Right y) z) = map (StarM y) (commutePos (f y) z)

