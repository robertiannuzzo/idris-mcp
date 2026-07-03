module Data.Container.Cartesian.Sequence.Bifunctor

import Data.Category.Bifunctor
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Iso
import Data.Container
import Data.Product
import Data.Container.Extension

import Proofs
import Proofs.Transport

import Syntax.PreorderReasoning

%unbound_implicits off

public export
mapForward : {0 a, a' , b, b' : Container}
    -> (m1 : a =#> a')
    -> (m2 : b =#> b')
    -> Ex a b.req
    -> Ex a' b'.req
mapForward m1 m2 x =
    MkEx (m1.cfwd x.ex1) (m2.cfwd . x.ex2 . (m1.cbwd x.ex1).to)
-- public export
0
prf2 :  {0 a : Type} ->
        (p1, p2 :  a) ->
        (prf1 :  p1 === p2) ->
        (F, G : a -> Type) ->
        (iso2 : (yy : a) -> F yy ≅ G yy)  ->
        (\vx => transport F prf1 vx) . (iso2 p1).from
        === ((iso2 p2).from . (\vx => transport G prf1 vx))
prf2 p1 p1 Refl f g iso2 =  funExt $ \zxx =>
  Calc $
    |~ transport f Refl ((iso2 p1) .from zxx)
    ~~ ((iso2 p1) .from zxx)
      ...(applyRefl ? ? )
    ~~ (iso2 p1) .from (transport g Refl zxx)
      ..<(cong ((iso2 p1).from ) (applyRefl ? ?))

precompSame : forall a, b, c. (h : b -> c) -> (f, g : a -> b) -> f === g -> h . f === h . g
precompSame h f f Refl = Refl

0 transportSquare :
              (0 t1, t2 : Type) ->
              (0 F : t1 -> Type) ->

              (0 tto : t2 -> t1) ->
              (x1 : t2) ->
              (x2 : F (tto x1)) ->

              (0 hn : t2 -> t2) ->

              (0 fn, gn : F (tto x1) -> F (tto x1)) ->
              (0 same : fn === gn) ->

              (0 xxx : Prelude.id === hn ) ->

              transport F
                    (app (precompSame tto Prelude.id hn xxx) x1)
                    (fn x2)
              === transport (F . tto)
                    (app xxx x1)
                    (gn x2)
transportSquare t1 t2 f tto x1 x2 Prelude.id fn gn same Refl = trans (applyRefl ? ?) (app same x2 `trans` applyRefl' ? ?)

0 prf1 : (0 a, a', b, b' : Container) ->
    (m1 : a =#> a') ->
    (m2 : b =#> b') ->
    (x : (a ▷ b).req) ->
    (z : a.response x.ex1) ->
      (\xv => transport (b'.response . m2.cfwd . x.ex2) (sym ((m1.cbwd x.ex1).toFrom z)) xv) . (m2.cbwd (x.ex2 z)).from ===
      ((m2.cbwd (x.ex2 ((m1.cbwd x.ex1).to ((m1.cbwd x.ex1).from z)))).from) .
        (\xv => transport (b.response . x.ex2) (sym ((m1.cbwd x.ex1).toFrom z)) xv)
prf1 a a' b b' m1 m2 x z
  = let
        iso1 : a'.response (m1.cfwd x.ex1) ≅ a.response x.ex1
        iso1 = m1.cbwd x.ex1

        p1, p2 :  a.response x.ex1
        p1 = z
        p2 = iso1.to (iso1.from z)

        prf :  p1 === p2
        prf = (sym ((m1 .cbwd x.ex1).toFrom z))

        F, G : a.response x.ex1 -> Type
        F fx = b'.response (m2.cfwd (x.ex2 fx))
        G fx = b.response (x.ex2 fx)

        iso2 : (yy : a .response (x .ex1)) -> F yy ≅ G yy
        iso2 y = m2.cbwd (x.ex2 y)

    in Calc $
    |~ (\vx => transport F prf vx)
      . ((iso2 p1)).from
    ~~ (((iso2 p2)).from
      . (\vx => transport G prf vx))
      ...(prf2 {a = a.response x.ex1} p1 p2 prf F G iso2)

0
fcompAssoc : forall a, b, c, d.
             (f : a -> b) ->
             (g : b -> c) ->
             (h : c -> d) ->
             h . (g . f) === (h . g) . f

-- fcompAssoc f g h = Refl
--  (0 tto : (?_ -> c1 .response x1)) ->
--  (x1 : ?_) ->
--  (x2 : c3' .response (gp2 .cfwd (fp2 .cfwd (x2 (tto x1))))) ->
--  (0 hn : (?_ -> ?_)) ->
--  (0 fn : (c3' .response (gp2 .cfwd (fp2 .cfwd (x2 (tto x1)))) ->
--  c3' .response (gp2 .cfwd (fp2 .cfwd (x2 (tto x1)))))) ->
--  (0 gn : (c3' .response (gp2 .cfwd (fp2 .cfwd (x2 (tto x1)))) ->
--  c3' .response (gp2 .cfwd (fp2 .cfwd (x2 (tto x1)))))) ->
--  (0 _ : fn = gn) ->
--  (0 xxx : id = hn) ->
--  transport (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 x)))) ??? (fn x2) =
--  transport (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 (tto x))))) (app xxx x1) (gn x2)
-- ------------------------------
-- transport (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 x)))) ??? ((gp2 .cbwd (fp2 .cfwd (x2 y1))) .from ((fp2 .cbwd (x2 y1)) .from y2)) =
-- transport (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 ((fp1 .cbwd x1) .to x))))) (sym ((gp1 .cbwd (fp1 .cfwd x1)) .toFrom ((fp1 .cbwd x1) .from y1))) ((gp2 .cbwd (fp2 .cfwd (x2 ((fp1 .cbwd x1) .to ((fp1 .cbwd x1) .from y1))))) .from (transport (\x => c2' .response (fp2 .cfwd (x2 x))) (sym ((fp1 .cbwd x1) .toFrom y1)) ((fp2 .cbwd (x2 y1)) .from y2)))

0
(.toFromId) : forall left, right. (iso : left ≅ right) -> iso.to . iso.from === Prelude.id
(.toFromId) iso = funExt iso.toFrom

public export
mapBackward : (0 a, a', b, b' : Container) ->
    (m1 : a =#> a') -> (m2 : b =#> b') ->
    (x : (a ▷ b).req) ->
    ((a' ▷ b').res (mapForward m1 m2 x))
    ≅ ((a ▷ b).res x)
mapBackward a a' b b' m1 m2 x = MkIso
    (\y => (m1.cbwd x.ex1).to y.π1
        ## (m2.cbwd $ x.ex2 ((m1.cbwd x.ex1).to y.π1)).to y.π2)
    (\y => (m1.cbwd x.ex1).from y.π1 ## transport (b'.res . m2.cfwd . x.ex2) (sym ((m1.cbwd x.ex1).toFrom y.π1)) ((m2.cbwd (x.ex2 y.π1)).from y.π2))
    (\z => sigEqToEqS $ MkSigEqS
             ((m1.cbwd x.ex1).toFrom z.π1)
             (app (Calc $
               |~ (m2.cbwd (x.ex2 ((m1.cbwd x.ex1).to ((m1.cbwd x.ex1).from z.π1)))).to
                . (\xv => transport (b'.response . m2.cfwd . x.ex2) (sym ((m1.cbwd x.ex1).toFrom z.π1)) xv )
                . (m2.cbwd (x.ex2 z.π1)).from
               ~~ (m2.cbwd (x.ex2 ((m1.cbwd x.ex1).to ((m1.cbwd x.ex1).from z.π1)))).to
                . (((m2.cbwd (x.ex2 ((m1.cbwd x.ex1).to ((m1.cbwd x.ex1).from z.π1)))).from)
                 . (\xv => transport (b.response . x.ex2) (sym ((m1.cbwd x.ex1).toFrom z.π1)) xv))
                   ...(congDep ((m2.cbwd (x.ex2 ((m1.cbwd x.ex1).to ((m1.cbwd x.ex1).from z.π1)))).to .)
                                 ((prf1 a a' b b' m1 m2 x z.π1)))
               ~~ ((m2.cbwd (x.ex2 ((m1.cbwd x.ex1).to ((m1.cbwd x.ex1).from z.π1)))).to
                 . ((m2.cbwd (x.ex2 ((m1.cbwd x.ex1).to ((m1.cbwd x.ex1).from z.π1)))).from))
                . (\xv => transport (b.response . x.ex2) (sym ((m1.cbwd x.ex1).toFrom z.π1)) xv)
                   ...(fcompAssoc (\xv => transport (b.response . x.ex2) (sym ((m1.cbwd x.ex1).toFrom z.π1)) xv)
                                  ((m2.cbwd (x.ex2 ((m1.cbwd x.ex1).to ((m1.cbwd x.ex1).from z.π1)))).from)
                                  (m2.cbwd (x.ex2 ((m1.cbwd x.ex1).to ((m1.cbwd x.ex1).from z.π1)))).to)
               ~~ (\xv => transport (b.response . x.ex2) (sym ((m1.cbwd x.ex1).toFrom z.π1)) xv)
                   ...(
                     cong (. (\xv => transport (b.response . x.ex2) (sym ((m1.cbwd x.ex1).toFrom z.π1)) xv))
                          ((m2.cbwd (x.ex2 ((m1.cbwd x.ex1).to ((m1.cbwd x.ex1).from z.π1)))).toFromId)
                       )
                ) z.π2
            )
    )
    (\w => sigEqToEqS $ MkSigEqS
            ((m1.cbwd x.ex1).fromTo w.π1)
            (let
              0 t1 : Type
              t1 = a.res x.ex1
              0 t2 : Type
              t2 = a'.response (m1.cfwd x.ex1)

              0 F : t1 -> Type
              F = b'.res . m2.cfwd . x.ex2
              0 F' : t1 -> Type
              F' = b.res . x.ex2

              x1 : t2
              x1 = w.π1
              x2 : F ((m1.cbwd x.ex1).to x1)
              x2 = w.π2

              0 iso1 : t2 ≅ t1
              iso1 = m1.cbwd x.ex1

              0 tto : t2 -> t1
              tto = iso1.to

              0 iso2 : F (tto x1) ≅ F' (tto x1)
              iso2 = m2.cbwd (x.ex2 (tto w.π1))

              ttt := transportSquare t1 t2 F iso1.to x1 x2
                  (iso1.from . iso1.to)
                  (iso2.from . iso2.to)
                  Prelude.id
                  (funExt iso2.fromTo)
                  (sym $ funExt iso1.fromTo)
              in Calc $
              |~ transport F
                    (sym (iso1.toFrom (tto x1)))
                    ((iso2.from . iso2.to) x2)
              ~~ transport F
                    ?
                    ((iso2.from . iso2.to) x2)
                ...(transpUIP ? ?)
              ~~ transport (F . tto)
                    ?
                    (x2)
                ...(ttt)
              ~~ transport (F . tto)
                    (sym (iso1.fromTo x1))
                    (x2)
              ...(transpUIP ? ?)
            )
    )
export
(~▷#~) :
    {0 a, a', b, b': Container} ->
    (a =#> a') -> (b =#> b') ->
    a ▷ b =#> a' ▷ b'
(~▷#~) m1 m2 = MkCartDepLens
    (mapForward m1 m2)
    (mapBackward a a' b b' m1 m2)
public export
0 circBifunctorPreservesIdentity :
  (v : Container * Container) ->
  (identity v.π1) ~▷#~ (identity v.π2)
  `CartDepLensEq` identity (uncurry (▷) v)
circBifunctorPreservesIdentity v = MkCartDepLensEq
   (\xs => congDep (MkEx (xs .ex1)) (funExt $ \vn => cong xs.ex2 (idTo vn)) `trans` exUniq xs)
   (\_ => MkIsoEq sigmaProjId (\xx => sigEqToEqS $ MkSigEqS Refl (applyRefl2 ? ?)))
public export
-- transport
--   (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 x))))
--   (sym (trans (cong ((fp1 .cbwd x1) .to) ((gp1 .cbwd (fp1 .cfwd x1)) .toFrom ((fp1 .cbwd x1) .from y1))) ((fp1 .cbwd x1) .toFrom y1)))
--   ((gp2 .cbwd (fp2 .cfwd (x2 y1))) .from ((fp2 .cbwd (x2 y1)) .from y2))
-- transport
--   (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 ((fp1 .cbwd x1) .to ((gp1 .cbwd (fp1 .cfwd x1)) .to x))))))
--   Refl
--   (transport
--     (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 ((fp1 .cbwd x1) .to x)))))
--     (sym ((gp1 .cbwd (fp1 .cfwd x1)) .toFrom ((fp1 .cbwd x1) .from y1)))
--     ((gp2 .cbwd (fp2 .cfwd (x2 ((fp1 .cbwd x1) .to ((fp1 .cbwd x1) .from y1))))) .from (transport (\x => c2' .response (fp2 .cfwd (x2 x))) (sym ((fp1 .cbwd x1) .toFrom y1)) ((fp2 .cbwd (x2 y1)) .from y2))))

0 circBifunctorPreservesComposition :
    (c1, c2, c3 : Container * Container) ->
    (f : (c1.π1 =#> c2.π1) * (c1.π2 =#> c2.π2)) ->
    (g : (c2.π1 =#> c3.π1) * (c2.π2 =#> c3.π2)) ->
    (f.π1 |#> g.π1) ~▷#~ (f.π2 |#> g.π2) ≡
       (f.π1 ~▷#~ f.π2 |#> g.π1 ~▷#~ g.π2)
circBifunctorPreservesComposition (c1 && c1') (c2 && c2') (c3 && c3')
    (fp1 && fp2) (gp1 && gp2) = cartEqToEq $ MkCartDepLensEq
    (\x => Refl)
    (\(MkEx x1 x2) => MkIsoEq
        (\y => Refl)
        (\(y1 ## y2) => sigEqToEqS $ MkSigEqS
            Refl
            (believe_me ()){-(let
              iso1 : c3 .response (gp1 .cfwd (fp1 .cfwd x1)) ≅ c2 .response (fp1 .cfwd x1)
              iso1 = (gp1.cbwd (fp1.cfwd x1))
              iso2 : c2 .response (fp1 .cfwd x1) ≅ c1 .response x1
              iso2 = (fp1 .cbwd x1)
              iso3 : c2' .response (fp2 .cfwd (x2 y1)) ≅ c1' .response (x2 y1)
              iso3 = fp2.cbwd (x2 y1)
              iso4 : c3' .response (gp2 .cfwd (fp2 .cfwd (x2 y1))) ≅ c2' .response (fp2 .cfwd (x2 y1))
              iso4 = gp2 .cbwd (fp2 .cfwd (x2 y1))
              iso4' : c3'.response (gp2.cfwd (fp2 .cfwd (x2 ((fp1 .cbwd x1) .to ((fp1 .cbwd x1) .from y1))))) ≅ c2' .response (fp2 .cfwd (x2 ((fp1 .cbwd x1) .to ((fp1 .cbwd x1) .from y1))))
              iso4' = gp2 .cbwd (fp2 .cfwd (x2 (iso2 .to (iso2 .from y1))))
              -- transcomp := transportComposeUIP  (\x => c3'.response (gp2.cfwd (fp2.cfwd (x2 (iso2.to ((gp1.cbwd (fp1.cfwd x1)).to x))))))
              --                   (iso4'.from (transport (c2'.response . fp2.cfwd . x2) (sym (iso2 .toFrom y1)) ((fp2.cbwd (x2 y1)).from y2)))
              --                   { prf1 = Refl
              --                   , prf2 = (sym ((gp1 .cbwd (fp1 .cfwd x1)) .toFrom (iso2 .from y1)))
              --                   , prf3 = (sym ((gp1 .cbwd (fp1 .cfwd x1)) .toFrom (iso2 .from y1)))}
              Transp2 : c3'.response (gp2.cfwd (fp2.cfwd (x2 ((fp1.cbwd x1).to ((gp1.cbwd (fp1.cfwd x1)).to ((gp1.cbwd (fp1.cfwd x1)).from ((fp1.cbwd x1).from y1)))))))
              Transp1 := transport
                    (\x => c3'.response (gp2 .cfwd (fp2 .cfwd (x2 (iso2 .to (x))))))
                    Refl
                    (transport
                        (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 (iso2 .to x)))))
                        (sym ((gp1 .cbwd (fp1 .cfwd x1)) .toFrom (iso2 .from y1)))
                        (iso4'.from (transport (c2'.response . fp2.cfwd . x2) (sym (iso2 .toFrom y1)) ((fp2.cbwd (x2 y1)).from y2))))
              Transp2 = transport
                        (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 (iso2 .to x)))))
                        (sym ((gp1 .cbwd (fp1 .cfwd x1)) .toFrom (iso2 .from y1)))
                        (iso4'.from (transport (c2'.response . fp2.cfwd . x2) (sym (iso2 .toFrom y1)) ((fp2.cbwd (x2 y1)).from y2)))
              transpIso := transportSquare ? ? (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 x))))
              ccto := ((fp1.cbwd x1).to)
              in Calc $
              |~ transport
                    (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 x))))
                    (sym (trans (cong iso2.to (iso1.toFrom (iso2.from y1))) (iso2.toFrom y1)))
                    (iso4.from (iso3.from y2))
              ~~ transport
                    (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 (iso2 .to x)))))
                    (sym ((gp1 .cbwd (fp1 .cfwd x1)) .toFrom (iso2 .from y1)))
                    (iso4'.from (transport (c2'.response . fp2.cfwd . x2) (sym (iso2 .toFrom y1)) ((fp2.cbwd (x2 y1)).from y2)))
                ...(?lol)
              ~~ transport
                    (\x => c3'.response (gp2 .cfwd (fp2 .cfwd (x2 (iso2 .to ((gp1 .cbwd (fp1 .cfwd x1)) .to x))))))
                    Refl
                    (transport
                        (\x => c3' .response (gp2 .cfwd (fp2 .cfwd (x2 (iso2 .to x)))))
                        (sym ((gp1 .cbwd (fp1 .cfwd x1)) .toFrom (iso2 .from y1)))
                        (iso4'.from (transport (c2'.response . fp2.cfwd . x2) (sym (iso2 .toFrom y1)) ((fp2.cbwd (x2 y1)).from y2))))
                ...(?quee)
                )-}
        )
    )
namespace Cart
  public export
  SequenceBifunctor : Bifunctor ContCart ContCart ContCart
  SequenceBifunctor = MkFunctor
    (Product.uncurry (▷))
    (\x, y, m => m.π1 ~▷#~ m.π2)
    (\x => cartEqToEq (circBifunctorPreservesIdentity x))
    circBifunctorPreservesComposition
