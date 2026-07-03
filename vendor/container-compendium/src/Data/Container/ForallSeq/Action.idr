module Data.Container.ForallSeq.Action

import Data.Container
import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.Cartesian.Sequence.Monoidal
import Data.Container.Cartesian.Sequence.Bifunctor
import Data.Container.Extension
import Data.Container.ForallSeq.Bifunctor
import Data.Container.Morphism
import Data.Container.Morphism.Eq
import Data.Container.Sequence.Definition
import Data.Container.Sequence.Bifunctor
import Data.Container.Sequence.Monoidal

import Data.Category.Action
import Data.Category.Bifunctor
import Data.Category.Monoid
import Data.Category.NaturalTransformation

import Data.Sigma
import Data.Product
import Data.Iso

import Proofs
import Proofs.Transport

%hide Container.Sequence.Monoidal.SequenceMonoidal
---------------------------------------------------------------------------------------------
-- ▶ is an action on Cont with ▷ as a monoidal category on Cont#
---------------------------------------------------------------------------------------------
-- Morphism from ((c1 ⊗ c2) ▶ c2) to (c1 ▶ (c2 ▶ c3))
-- The other way around does not hold.
actionAssocProdL : (c1, c2, c3 : Container) -> ((c1 ⊗ c2) ▶ c3) =%> (c1 ▶ (c2 ▶ c3))
actionAssocProdL (a !> ap) (b !> bp) (c !> cp) =
   (\v => MkEx v.ex1.π1 (\y => MkEx v.ex1.π2 (curry v.ex2 y))) <!
   (\(MkEx (v1 && v2) v'), w, (z1 && z2) => w z1 z2)

-- morphism from x ▶ (y ▶ z) to (x ▷ y) ▶ z
-- the other way around does not hold

actor : x ▶ (y ▶ z) =%> (x ▷ y) ▶ z
actor =
  (\v => MkEx (MkEx v.ex1 (ex1 . v.ex2)) (\k => (v.ex2 k.π1).ex2 k.π2)) <!
  (\x, x', y, z => x' (y ## z))


triMapEx :
   (m1 : x =#> x') ->
   (m2 : y =#> y') ->
   (m3 : z =%> z') ->
   Ex x (Ex y (z .req)) -> Ex x' (Ex y' (z' .req))
triMapEx (MkCartDepLens f1 b1) (MkCartDepLens f2 b2) (f3 <! b3) (MkEx e1 e2)
  = MkEx
      (f1 e1)
      (\c1 => MkEx
          (f2 (ex1 (e2 (to (b1 e1) c1))))
          (\c2 => f3 (ex2 (e2 (to (b1 e1) c1)) (to (b2 (ex1 (e2 (to (b1 e1) c1)))) c2))))

triMapBwd :
   (m1 : x =#> x') ->
   (m2 : y =#> y') ->
   (m3 : z =%> z') ->
   (vx : Ex x (Ex y z.req)) ->
   ((val : x'.res ((triMapEx m1 m2 m3 vx).ex1)) ->
        (v2 : y'.res (((triMapEx m1 m2 m3 vx).ex2 val).ex1)) ->
        z'.res (((triMapEx m1 m2 m3 vx).ex2 val).ex2 v2)) ->
   (v3 : x.res vx.ex1) -> (v4 : y.res ((vx.ex2 v3).ex1)) -> z .res ((vx.ex2 v3).ex2 v4)
triMapBwd (MkCartDepLens f1 b1) (MkCartDepLens f2 b2) (f3 <! b3) (MkEx e1 e2)
  f v3 v4 =
  let 0 iso1 = (b1 e1).toFrom v3
      0 iso2 = (b2 (ex1 (e2 v3))).toFrom v4
      fn : (v2 : y' .res (f2 ((e2 ((b1 e1) .to ((b1 e1) .from v3))) .ex1))) ->
           z'.res (f3 ((e2 ((b1 e1).to ((b1 e1).from v3))).ex2 ((b2 ((e2 ((b1 e1).to ((b1 e1).from v3))).ex1)).to v2)))
      fn = f (from (b1 e1) v3)
      fn' : (v2 : y' .res (f2 ((e2 v3).ex1))) ->
           z'.res (f3 ((e2 v3).ex2 ((b2 ((e2 v3).ex1)).to v2)))
      fn' = rewrite sym iso1 in fn
      gn : z'.res (f3 ((e2 v3).ex2 ((b2 ((e2 v3).ex1)).to ((b2 ((e2 v3).ex1)).from v4))))
      gn = fn' (from (b2 (ex1 (e2 v3))) v4)
      gn' : z'.res (f3 ((e2 v3).ex2 v4))
      gn' = replace {p = z'.res . f3 . ex2 (e2 v3)} iso2 gn
  in b3 ((e2 v3).ex2 v4) gn'

-- z'.res (f3 (ex2 (e2 (to (b1 e1) val)) (to (b2 (ex1 (e2 (to (b1 e1) val)))) v2)))
-- map morphisms for the trifunctor _ ▶ (_ ▶ _)
mapMorTriAction :
    {x, x', y, y', z, z' : Container} ->
    (m1 : x =#> x') ->
    (m2 : y =#> y') ->
    (m3 : z =%> z') ->
    x ▶ (y ▶ z) =%> x' ▶ (y' ▶ z')
mapMorTriAction m1 m2 m3 =
  (triMapEx m1 m2 m3) <!
  (triMapBwd m1 m2 m3)

%ambiguity_depth 4
mapMorUnivAction : (x, x' : Container) -> (m1 : x =#> x') ->
              (y, y' : Container) -> (m2 : y =#> y') ->
              (z, z' : Container) -> (m3 : z =%> z') ->
              (x ▷ y) ▶ z =%> (x' ▷ y') ▶ z'
mapMorUnivAction x x' m1 y y' m2 z z' m3 =
  fwd <! bwd
  where
    fwd : ((x ▷ y) ▶ z).req -> ((x' ▷ y') ▶ z').req
    fwd x = MkEx (MkEx (m1.cfwd x.ex1.ex1)
                       (\vx => m2.cfwd (x.ex1.ex2 $ (m1.cbwd x.ex1.ex1).to vx)))
                 (\vx => m3.fwd $ x.ex2 ((m1.cbwd x.ex1.ex1).to vx.π1
                      ## (m2.cbwd $ x.ex1.ex2 $ (m1.cbwd x.ex1.ex1).to vx.π1).to vx.π2))

    bwd : (v : ((x ▷ y) ▶ z).req) ->
          ((x' ▷ y') ▶ z').res (fwd v) ->
          ((x ▷ y) ▶ z).res v
    bwd (MkEx (MkEx p1 p2) a2) f (v1 ## v2) =
      let
          0 tb = (m1.cbwd p1).toFrom v1
          0 tq = (m2.cbwd (p2 v1)).toFrom v2
          arr : y' .res (m2.cfwd (p2 ((m1.cbwd p1) .to ((m1.cbwd p1) .from v1))))
          arr = replace {p = \arg => y' .res (m2.cfwd (p2 arg))}
                   (sym tb) ((m2.cbwd (p2 v1)).from v2)
          fn = f ((m1.cbwd p1).from v1 ## arr)
          leftSide : y .res (p2 ((m1.cbwd p1) .to ((m1.cbwd p1) .from v1)))
          leftSide = to (m2.cbwd (p2 ((m1.cbwd p1) .to ((m1.cbwd p1) .from v1)))) arr
          rightSide : y .res (p2 ((m1.cbwd p1) .to ((m1.cbwd p1) .from v1)))
          rightSide = replace {p = \arg => y.res (p2 arg)} (sym tb) v2
          0 prf2 : leftSide === rightSide
          prf2 = rewrite tb in tq

       in m3.bwd (a2 (v1 ## v2))
           (replace {p = \arg => z' .res (m3 .fwd (a2 arg))} (cong2Dep' (##) tb prf2) fn)

-- x |> (y |> z) -> x' |> (y' |> z')
--      |                 |
--      v                 v
-- (x ▷ y) |> z  -> (x' ▷ y') |> z'
UnivActionCommutes : (0 x, x' : Container) -> (m1 : x =#> x') ->
           (0 y, y' : Container) -> (m2 : y =#> y') ->
           (0 z, z' : Container) -> (m3 : z =%> z') ->
           let 0 φ_xyz : x ▶ (y ▶ z) =%> (x ▷ y) ▶ z
               φ_xyz = actor
               0 φ_xyz' : x' ▶ (y' ▶ z') =%> (x' ▷ y') ▶ z'
               φ_xyz' = actor
               0 m : x ▶ (y ▶ z) =%> x' ▶ (y' ▶ z')
               m = mapMorTriAction m1 m2 m3
               0 m' : (x ▷ y) ▶ z =%> (x' ▷ y') ▶ z'
               m' = mapMorUnivAction x x' m1 y y' m2 z z' m3
           in m |%> φ_xyz' <%≡%> φ_xyz |%> m'
UnivActionCommutes x x' (MkCartDepLens f1 b1) y y' (MkCartDepLens f2 b2) z z' (f3 <! b3)
  = MkDepLensEq
  (\(MkEx x1 x2) => Refl)
  (\(MkEx x1 x2) => \vn => funExtDep $ \vx => funExtDep $ \vy => Refl)

contNatPrfOp : (a, b, c : Container) -> (x ▷ y) ▶ z =%> x ▶ (y ▶ z)
contNatPrfOp a b c =
  (\v => MkEx v.ex1.ex1 (\l => MkEx (v.ex1.ex2 l) (\j => v.ex2 (l ## j)))) <!
  (\aa, bb, (c1 ## c2) => bb c1 c2 )


public export
ForallActor :
  let 0 f1, f2 : (ContCart × (ContCart × Cont)) ->> Cont
      f1 = pair (idF ContCart) ForallSeqBifunctor ⨾⨾ ForallSeqBifunctor
      f2 = assocR {a = ContCart, b = ContCart, c = Cont}
        ⨾⨾ pair SequenceBifunctor (idF Cont) ⨾⨾ ForallSeqBifunctor
   in f1 =>> f2
-- ForallActor = MkNT
--   (\_ => actor)
--   (\x, y, (m1 && (m2 && m3)) => depLensEqToEq $ MkDepLensEq
--     (\_ => ?nhhh)
--     (\(MkEx v1 v2), w => funExtDep $ \z =>
--       funExtDep $ \q =>
--         let val = (m1 .cbwd v1) .from z
--             zToFrom = (m1 .cbwd v1).toFrom z
--             val2 = (m2 .cbwd ((v2 z) .ex1)) .from q
--             adjustedVal2 = replace
--               {p = y.π2.π1.response . m2.cfwd .
--                    (\x : ((x .π1).response v1) => (v2 x).ex1)}
--               (sym zToFrom) val2
--             wal = w ((m1 .cbwd v1) .from z ## adjustedVal2)
--             gfg = cong2Deppp (m3.bwd)
--                     { a = ((v2 z) .ex2 q)}
--                     ?aa ?bb
--             m3bwd = m3.bwd ((v2 z).ex2 q) ?arg
--             -- goal : m3.bwd ((v2 z).ex2 q)
--             --               (w ((m1.cbwd v1).from z ## (m2.cbwd ((v2 z) .ex1)) .from q))
--         in ?end
--               -- sigEqToEq $ MkSigEq ?aa ?bb
--     )
--   )

public export
unitL2 : a =%> I ▶ a
unitL2 = (\x => MkEx () (\_ => x)) <! (\x, f => f ())

public export
ForallUnitor : idF Cont =>> Bifunctor.applyL {a = ContCart} I ForallSeqBifunctor
ForallUnitor = MkNT
    (\a => unitL2)
    (\x, y, m => depLensEqToEq $ MkDepLensEq
        (\_ => Refl)
        (\v, y => Refl)
    )
public export
ForallLaxAction : LaxAction ContCart Cont Cart.SequenceMonoidal
ForallLaxAction = MkLaxAction
    { laction = ForallSeqBifunctor
    , lactor = ?actorType
    , lunitor = ?unitorType
    }
