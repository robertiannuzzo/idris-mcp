module Data.Container.List.Monoid

import Data.Category.Monoid
import Data.Category.Functor
import Data.Category.Product
import Data.Category.NaturalTransformation

import Data.Container
import Data.Container.Extension
import Data.Container.Sequence.Definition
import Data.Container.Sequence.Monoidal as Cont
import Data.Container.Category
import Data.Container.Cartesian
import Data.Container.Cartesian.Category
import Data.Container.Cartesian.ForallSeq.Monoidal
import Data.Container.Cartesian.Sequence.Bifunctor
import Data.Container.Cartesian.Sequence.Monoidal as Cart
import Data.Container.Sequence.Monoidal as Cont
import Data.Container.Tensor.Definition
import Data.Container.List.Desc
import Data.Coproduct
import Data.Fin
import Data.Iso
import Data.Product
import Data.Sigma

import Pipeline.Equality
neutral : One =%> ListCont
neutral = (const Z) <! (\_ => absurd)

export
splitFin : (m, n : Nat) ->  Fin (m + n) -> Fin m + Fin n
splitFin 0 n z = +> z
splitFin (S k) n FZ = <+ FZ
splitFin (S k) n (FS x) = mapFst FS (splitFin k n x)

mult : ListCont * ListCont =%> ListCont
mult = (uncurry (+)) <! (\x, y => splitFin x.π1 x.π2 y)


splitLeft :
    (v1 : Nat) ->
    (w : Fin v1) ->
    (splitFin v1 0 (replace {p = Fin} (sym $ plusZeroRightNeutral v1) w)) = (<+) w
splitLeft 0 w = absurd w
splitLeft (S k) FZ = Refl
splitLeft (S k) (FS x) = rewrite splitLeft k x in Refl

0
lemmaSplitAssoc :
   (a, b, c : Nat) ->
   (y : Fin ((a + b) + c)) -> let
     0 y' : Fin (a + (b + c))
     y' = replace {p = Fin} (sym $ plusAssociative a b c) y

     0 xx, yy  : (Fin a + Fin b) + Fin c
     xx = bimap (\y => splitFin a b y) id (splitFin (plus a b) c y)
     yy = assocL (bimap id (\y => splitFin b c y) (splitFin a (plus b c) y'))
     in xx === yy
lemmaSplitAssoc 0 0 c y = Refl
lemmaSplitAssoc 0 (S k) c FZ = Refl
lemmaSplitAssoc 0 (S k) c (FS x) with (splitFin k c x)
  lemmaSplitAssoc 0 (S k) c (FS x) | (<+ y) = Refl
  lemmaSplitAssoc 0 (S k) c (FS x) | (+> y) = Refl
lemmaSplitAssoc (S k) b c FZ = Refl
lemmaSplitAssoc (S k) b c (FS x) =
  let 0 steps : CongPipeline ? ?

-- Large proof steps
-- steps = [ bimap (splitFin (S k) b) id . bimap FS id . splitFin (plus k b) c
--         , bimap (splitFin (S k) b . FS) id          . splitFin (plus k b) c
--         , bimap (bimap FS id . splitFin k b) id     . splitFin (plus k b) c
--         , bimap (bimap FS id) id . bimap (splitFin k b) id     . splitFin (plus k b) c
--         , bimap (bimap FS id) id . assocL . bimap id (splitFin b c) . splitFin k (plus b c) . \x => replace {p = Fin} (sym $ plusAssociative k b c) x
--         , assocL . bimap FS (bimap id id) . bimap id (splitFin b c) . splitFin k (plus b c) . \x => replace {p = Fin} (sym $ plusAssociative k b c) x
--         , assocL . bimap FS id            . bimap id (splitFin b c) . splitFin k (plus b c) . \x => replace {p = Fin} (sym $ plusAssociative k b c) x
--         , assocL . bimap id (splitFin b c) . bimap FS id            . splitFin k (plus b c) . \x => replace {p = Fin} (sym $ plusAssociative k b c) x]
      steps = Cong (. splitFin (plus k b) c)
                 [ bimap (splitFin (S k) b) id . bimap FS id
                 , bimap (splitFin (S k) b . FS) id]
           >| Cong (\f => bimap f id . splitFin (plus k b) c)
                 [ (splitFin (S k) b . FS)
                 , (bimap FS id . splitFin k b) ]
           >| Cong (. splitFin (plus k b) c)
                 [ bimap (bimap FS id . splitFin k b)            id
                 , bimap (bimap FS id) id . bimap (splitFin k b) id]
           >| Cong (bimap (bimap FS id) id .)
                 [ bimap (splitFin k b) id . splitFin (plus k b) c
                 , assocL . bimap id (splitFin b c) . splitFin k (plus b c) . \x => replace {p = Fin} (sym $ plusAssociative k b c) x]
           >| Cong (. splitFin k (plus b c) . \x => replace {p = Fin} (sym $ plusAssociative k b c) x)
                 (Cong (. bimap id (splitFin b c))
                     ( bimap (bimap FS id) id . assocL
                     :: AddNest (\x => assocL . bimap FS x)
                        [bimap id id
                        , id] Nil
                     )
                  >| AddNest (assocL .)
                       [ bimap FS id             . bimap id (splitFin b c)
                       , bimap id (splitFin b c) . bimap FS id
                       ] Nil
                 )
           >| Nil
  in app (runProof steps
         (funExt (\case (<+ x) => Refl
                        (+> x) => Refl)
         :: Refl
         :: Refl
         :: Refl
         :: funExt (\case (+> x) => Refl
                          (<+ x) => Refl)
         :: Refl
         :: funExt (lemmaSplitAssoc k b c)
         :: Refl
         :: funExt assocLBimap
         :: funExt bimapId
         :: Refl
         :: funExt bimapSquare
         :: Nil
         )) x
ListMonoidCartesian : MonoidObject {o = Container} {cat = Cont} CartesianMonoidal
ListMonoidCartesian = MkMonObj
  ListCont
  neutral
  mult
  Refl
  (depLensEqToEq $ MkDepLensEq
      (\v => plusZeroRightNeutral v.π1)
      (\(v1 && v2), w =>
          rewrite splitLeft v1 (replace {p = Fin} (plusZeroRightNeutral v1) w)
          in Refl
      )
  )
  (depLensEqToEq $ MkDepLensEq
      (\((a && b) && c) => sym $ plusAssociative a b c)
      (\((a && b) && c), y => lemmaSplitAssoc a b c y)
  )

zeroUniq : (z : Fin 1) -> FZ === z
zeroUniq FZ = Refl

namespace Cartesian

  -- singleton list
  public export
  neutral : I =#> ListCont
  neutral = (const 1) <#!
            (\_ => MkIso
                 (\_ => ())
                 (\_ => FZ)
                 (\_ => unitUniq _)
                 (\_ => zeroUniq _)
             )

  public export
  sumAll : (n : Nat) -> (table : Fin n -> Nat) -> Nat
  sumAll 0 table = Z
  sumAll (S k) table = table FZ + (sumAll k (table . FS))


  -- the world if `with` worked
  undoJoinHelp :
    (k : Nat) ->
    (ex2 : Fin (S k) -> Nat) ->
    (evaled : Nat) ->
    (evaledIsEx2 : evaled === ex2 FZ) ->
    ((evaled === Z) -> (Fin (sumAll k (\x => ex2 (FS x))) -> Σ (Fin (S k)) (\y => Fin (ex2 y))))  ->
    ((n : Nat) -> evaled === S n -> Fin (plus (S n) (sumAll k (\x => ex2 (FS x)))) -> Σ (Fin (S k)) (\y => Fin (ex2 y))) ->
    Fin (plus (ex2 FZ) (sumAll k (\x => ex2 (FS x)))) ->
    Σ (Fin (S k)) (\y => Fin (ex2 y))
  undoJoinHelp k ex2 0 pr h1 h2 arg = h1 Refl (replace {p = Fin} (rewrite sym pr in Refl) arg)
  undoJoinHelp k ex2 (S j) pr h1 h2 arg = h2 j Refl (replace {p = Fin} (rewrite sym pr in Refl) arg)

  undoJoin : (x : Ex ListCont Nat) ->
             Fin (sumAll x.ex1 x.ex2) -> Σ (Fin x.ex1) (\y => Fin (x.ex2 y))
  undoJoin (MkEx 0 ex2) = absurd
  undoJoin (MkEx (S k) ex2) = undoJoinHelp k ex2 (ex2 FZ) Refl
    (\ev, y => let ff : Σ (Fin k) (\y => Fin (ex2 (FS y)))
                   ff = assert_total (undoJoin (MkEx k (ex2 . FS)) y)
                 in FS ff.π1 ## ff.π2)
    (\j, ev, y => choice {c = Σ (Fin (S k)) (\y => Fin (ex2 y))}
             (\xx => Fin.FZ ## replace {p = Fin} (sym ev) xx)
             (\xx => let gg : Σ (Fin k) (\y => Fin (ex2 (FS y)))
                         gg = assert_total (undoJoin (MkEx k (ex2 . FS))) xx
                      in FS gg.π1 ## gg.π2)
              (splitFin (S j)  (sumAll k (\x => ex2 (FS x))) y)
    )



  redoJoin : (x : Ex ListCont Nat) ->
             Σ (Fin (x .ex1)) (\y => Fin (x .ex2 y)) -> Fin (sumAll (x .ex1) (x .ex2))
  redoJoin (MkEx 0 ex2) y = absurd y.π1
  redoJoin (MkEx (S k) ex2) (FZ ## y2)
      = replace {p = Fin} (plusCommutative _ _)
      $ shift (sumAll k (\x => ex2 (FS x))) y2
  redoJoin (MkEx (S k) ex2) (FS y1 ## y2)
      = shift (ex2 FZ)
      $ assert_total (redoJoin (MkEx k (ex2 . FS)) (y1 ## y2))

  0 undoRedo :
      (x : Ex ListCont Nat) ->
      (u : Σ (Fin (x .ex1)) (\y => Fin (x .ex2 y))) ->
      (undoJoin x (redoJoin x u)) .π1 === u .π1
  undoRedo (MkEx 0 ex2) u = absurd u.π1
  undoRedo (MkEx (S k) ex2) (u1 ## u2) with (ex2 FZ) proof px
    undoRedo (MkEx (S k) ex2) (FZ ## u2) | 0     with (sumAll k (\x => ex2 (FS x)))
      undoRedo (MkEx (S k) ex2) (FZ ## u2) | 0     | 0 = absurd (replace {p = Fin} px u2)
      undoRedo (MkEx (S k) ex2) (FZ ## u2) | 0     | (S j) = absurd (replace {p = Fin} px u2)
    undoRedo (MkEx (S k) ex2) ((FS x) ## u2) | 0
      = rewrite px
      in cong FS (assert_total $ undoRedo (MkEx k (ex2 . FS)) (x ## u2))
    undoRedo (MkEx (S k) ex2) (FZ ## u2) | (S j) with (sumAll k (\x => ex2 (FS x)))
      undoRedo (MkEx (S k) ex2) (FZ ## u2) | (S j) | 0 with (ex2 FZ) proof py
        undoRedo (MkEx (S k) ex2) (FZ ## u2) | (S j) | 0 | 0 = absurd u2
        undoRedo (MkEx (S k) ex2) (FZ ## FZ) | (S j) | 0 | (S i) = Refl
        undoRedo (MkEx (S k) ex2) (FZ ## (FS x)) | (S j) | 0 | (S i) with (splitFin j 0 (replace {p = Fin} (believe_me ()) x))
          undoRedo (MkEx (S k) ex2) (FZ ## (FS x)) | (S j) | 0 | (S i) | (<+ y) = Refl
          undoRedo (MkEx (S k) ex2) (FZ ## (FS x)) | (S j) | 0 | (S i) | (+> y) = absurd y
      undoRedo (MkEx (S k) ex2) (FZ ## u2) | (S j) | (S i) with (replace {p=Fin} (px) u2) proof pu
        undoRedo (MkEx (S k) ex2) (FZ ## u2) | (S j) | (S i) | FZ = ?mwaui_0_rhs0_2_rhs2_1_rhs1_0
        undoRedo (MkEx (S k) ex2) (FZ ## u2) | (S j) | (S i) | (FS x) = ?mwaui_0_rhs0_2_rhs2_1_rhs1_1
    undoRedo (MkEx (S k) ex2) ((FS x) ## u2) | (S j) = ?mwaui_0_rhs0_3

  multBwd : (x : Ex ListCont Nat) ->
            (Fin (sumAll x.ex1 x.ex2))
            ≅ (Σ (Fin x.ex1) (\y => Fin (x.ex2 y)))
  multBwd x = MkIso
      (undoJoin x)
      (redoJoin x)
      (\u => sigEqToEq $ MkSigEq
          (undoRedo x u)
          ?multBwd_rhs_2
      )
      ?multBwd_rhs_3

  -- flatten nested lists
  public export
  mult : (ListCont ▷ ListCont) =#> ListCont
  mult = (\x => sumAll x.ex1 x.ex2) <#! multBwd

  public export
  ListMonoid : MonoidObject {o = Container} {cat = ContCart} SequenceMonoidal
  ListMonoid = MkMonObj
      ListCont
      neutral
      mult
      (cartEqToEq $ MkCartDepLensEq
          (\xs => ?bbb)
          (\xs => ?ListMonoidForallSeq_rhs_3)
      )
      (cartEqToEq $ MkCartDepLensEq ?bbb2?ListMonoidForallSeq_rhs_34)
      (cartEqToEq $ MkCartDepLensEq ?bbb1 ?ListMonoidForallSeq_rhs_35)

namespace Cont


  public export
  ListMonoid : MonoidObject {o = Container} {cat = Cont} Cont.SequenceMonoidal
  ListMonoid = MkMonObj
      ListCont
      (toLens _ _ Cartesian.neutral)
      (toLens _ _ Cartesian.mult)
      (depLensEqToEq $ MkDepLensEq ?bbb ?ListMonoidForallSeq_rhs_3)
      (depLensEqToEq $ MkDepLensEq ?bbb2?ListMonoidForallSeq_rhs_34)
      (depLensEqToEq $ MkDepLensEq ?bbb1 ?ListMonoidForallSeq_rhs_35)
