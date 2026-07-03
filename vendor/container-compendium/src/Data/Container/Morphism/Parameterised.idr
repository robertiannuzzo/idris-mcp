module Data.Container.Morphism.Parameterised

import Data.Container
import Data.Product
import Data.Coproduct
import Data.Alg
import Data.Category
import Data.Boundary

import Data.Container
import Data.Container.Morphism

import Control.Monad.Reader
import Control.Monad.Identity
import Control.Monad.State
||| A dependent parameterised lens defined as the para-construction on dependent lenses
public export
record DPara (l, p, r : Container) where
  constructor MkDPara
  lens : p ⊗ l =%> r
||| A type-alias for non-dependent parameterised lenses
public export
Para : Boundary -> Boundary -> Boundary -> Type
Para (MkB x s) (MkB p q) (MkB y r) = DPara (x :- s) (p :- q) (y :- r)
||| Composition of parameterised lenses
public export
(|>) : DPara l p x -> DPara x q r -> DPara l (p ⊗ q) r
(|>) y z = MkDPara $ MkMorphism
  (z.lens.fwd . mapSnd y.lens.fwd . assocL . mapFst swap)
  (\x, w => let
                b = z.lens.bwd (x.π1.π2 && y.lens.fwd (x.π1.π1 && x.π2)) w
                a = y.lens.bwd (x.π1.π1 && x.π2) b.π2
            in (a.π1 && b.π1) && a.π2)
public export
cornerRight : DPara CUnit p p
cornerRight = MkDPara $ MkMorphism π1 (\_, x => x && ())
public export
(.get) : DPara l p x -> p.shp * l.shp -> x.shp
(.get) y = y.lens.fwd

(.set) : (o : DPara l p r) -> (a : p.shp * l.shp) -> (b : r.pos (o.lens.fwd a)) -> p.pos a.π1 * l.pos a.π2
(.set) y x = y.lens.bwd x
read : DPara l p x -> l.shp -> Reader p.shp x.shp
read l x = MkReaderT (\y => pure $ l.lens.fwd (y && x))

interface DState (st : Container) (x : Type) where
  constructor MkDState
  runDState : (s : st.shp) -> st.pos s * x

state : (DPara (Const l) (Const p) (Const r)) -> l -> r -> State p l
state l xl xr = ST (\xn => pure $ toPair $ l.lens.bwd (xn && xl) xr )
export
reparam : a =%> b -> DPara l b r -> DPara l a r
reparam x y = MkDPara (parallel x (identity {a = l}) |> y.lens)
export
comb : l =%> x -> p =%> q -> y =%> r -> DPara x q y -> DPara l p r
comb left top right para = MkDPara $ parallel top left |> para.lens |> right
export
reparam' : a =%> b -> DPara l b r -> DPara l a r
reparam' p = comb identity p identity
export
preCompose : a =%> b -> DPara b p c -> DPara a p c
preCompose p = comb p identity identity

export
postCompose : DPara a p b -> b =%> c -> DPara a p c
postCompose l p = comb identity identity p l
export
paraLeft : a =%> b -> DPara l p r -> DPara (a ⊗ l) p (b ⊗ r)
paraLeft x y = MkDPara (MkMorphism (assocL . mapFst swap . assocR)
                          (\_ => assocL . mapFst swap . assocR) |> parallel x y.lens)

export
paraRight : DPara l p r -> a =%> b -> DPara (l ⊗ a) p (r ⊗ b)
paraRight x y = MkDPara (MkMorphism assocR (\_ => assocL) |> parallel x.lens y)
public export
parallel : DPara l p r -> DPara x q y -> DPara (l ⊗ x) (p ⊗ q) (r ⊗ y)
parallel p1 p2 = MkDPara $ let p = parallel p1.lens p2.lens in MkMorphism shuffle (\((a && a') && (c && c')) => shuffle) |> p
public export
choice : DPara l p r -> DPara x q y -> DPara (l + x) (p * q) (r + y)
choice z w = MkDPara $ MkMorphism fwd bwd
  where
    fwd : (p.shp * q.shp) * (l.shp + x.shp) -> r.shp + y.shp
    fwd (x && (<+ v)) = <+ z.lens.fwd (x.π1 && v)
    fwd (x && (+> v)) = +> w.lens.fwd (x.π2 && v)

    bwd : (arg : (p .shp * q .shp) * (l .shp + x .shp)) -> choice r.pos y.pos (fwd arg) ->
          (p.pos arg.π1.π1 + q.pos arg.π1.π2) * choice l.pos x.pos arg.π2
    bwd (p1 && (<+ v)) x = let val : p .pos (p1 .π1) * l.pos v
                               val = z.lens.bwd (p1.π1 && v) x
                            in <+ val.π1 && val.π2
    bwd (p1 && (+> v)) y = let val : q.pos p1.π2 * x.pos v
                               val = w.lens.bwd (p1.π2 && v) y
                            in +> val.π1 && val.π2
idPrfLeft : (f : a =%> b) -> f |> Morphism.identity {a=b} = f
idPrfLeft {f = (MkMorphism get set)} = Refl

idPrfRight : (f : a =%> b) -> Morphism.identity {a} |> f = f
idPrfRight {f = (MkMorphism get set)} = Refl

parameters {l, r : Container}
  Repar : (p ** DPara l p r) -> (p ** DPara l p r) -> Type
  Repar x y = x.fst =%> y.fst

  comp : {a, b, c : (p ** DPara l p r)} -> Repar a b -> Repar b c -> Repar a c
  comp = (|>)

  prfAssoc2 : {a, b, c, d : (p ** DPara l p r)}  ->
              (f : Repar a b) -> (g : Repar b c) -> (h : Repar c d) ->
              (comp {a} {b} {c=d} f (comp {a=b} {b=c} {c=d} g h)) === (comp {a} {b=c} {c=d} (comp {a} {b} {c} f g) h)
  prfAssoc2 (MkMorphism fget fset) (MkMorphism gget gset) (MkMorphism hget hset) = Refl

  DParaCat : Category (p ** DPara l p r)
  DParaCat = MkCategory
    Repar
    (\_ => identity)
    (|>)
    idPrfLeft
    idPrfRight
    prfAssoc2

-- Move those two away, probably somewhere close to `Action`?
interface Semigroup a => Combine a (0 b : a -> Type) where
   combine : (x1, x2 : a) ->
             (y : b (x1 <+> x2)) ->
             b x1 * b x2

||| Precomposing a choice with the `x + x = 2 * x` isomorphism
chooseBool : DPara ((!>) l s) p r ->
             DPara ((!>) l s) q y ->
             DPara ((!>) (l * Bool) (s . π1)) (p * q) (r + y)
chooseBool l1 l2 = MkMorphism (\x => if x.π2 then <+ x.π1 else +> x.π1)
                              (\case (x && True) => id
                                     (x && False) => id) `preCompose` (l1 `choice` l2)

public export
ReadOnly : Container -> Container
ReadOnly (a !> b) = a :- ()
