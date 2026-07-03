module Interactive.Sequent

import Data.Container
import Data.Container.Closed
import Data.Container.Closed.Eq
import Data.Container.Closed.Sequence
import Data.Container.Tensor.Definition
import Data.Container.Closed.Tensor.Bifunctor
import Data.Container.Closed.List.Functor
import Data.Container.Closed.List.Monoid
import Data.Container.Displayed
import Data.Container.Closed.Maybe.Functor
import Data.Container.List.Functor
import Data.Container.List.Desc
import Data.Container.Coproduct
import Data.Container.Descriptions.List
import Data.Container.Descriptions.Maybe
import Data.Container.Kleene
import Data.Container.Maybe.Definition

import Data.Fin
import Data.DPair
import Data.List
import Data.List.Any
import Data.List.Elem
import Data.List.Quantifiers
import Data.Sigma
import Data.Product
import Data.List1
import Data.Maybe.Any
import Data.Nat.Views
import Data.SnocList
import Data.Vect
import Decidable.Equality

import Syntax.PreorderReasoning.Generic

%hide Prelude.Ops.infixr.(&&)
%hide Prelude.Ops.infixl.(*)
private infixl 8 @@
private infixr 9 ~~>
private infix 5 |-
private infixl 8 *
private infixl 8 &&

private prefix 10 ¬
private infixl 8 ∧
private infixl 7 ∨

data Cover : (x, y, xy : List a) -> Type where
  Empty : Cover [] [] []
  PickL : Cover a b ab -> Cover (x :: a) b (x :: ab)
  PickR : Cover a b ab -> Cover a (x :: b) (x :: ab)

CoverRight : {xs : List a} -> Cover [] xs xs
CoverRight {xs = []} = Empty
CoverRight {xs = (x :: xs)} = PickR (CoverRight {xs})

CoverLeft : {xs : List a} -> Cover xs [] xs
CoverLeft {xs = []} = Empty
CoverLeft {xs = (x :: xs)} = PickL CoverLeft
data Ty = Atom Nat -- atoms are distinguished by a natural number
        | (¬)  Ty
        | (~~>) Ty Ty
        | (∧) Ty Ty
        | (∨) Ty Ty
record Sequent where
  constructor (|-)
  antecedent : List Ty
  consequent : List Ty
data LK : Sequent -> Type where
  --
  -- ----------
  --  a |- a
  Axiom  : LK ([a] |- [a])
  --   Γ |- a, Δ
  -- -------------
  --  Γ , ¬a |- Δ
  NegL   : LK (g |- a::d) -> LK (¬ a :: g |- d)

  --  Γ , a |- Δ
  -- -------------
  --  Γ |- ¬a , Δ
  NegR   : LK (a :: g |- d) -> LK (g |- ¬ a :: d)
  -- We write "+" to indicate that either
  -- of those premisses must hold
  --    Γ , a |- Δ "+" Δ Γ , b |- Δ
  -- -----------------------------
  --         Γ, a ∧ b |- Δ
  AndL  : LK (b :: g |- d) + LK (a :: g |- d) ->
          LK ((a ∧ b) :: g |- d)

  -- Γ |- a , Δ    Γ |- b , Δ
  -- ------------------------
  --      Γ |- a ∧ b , Δ
  AndR   : LK (g |- a :: d) -> LK (g |- b :: d) -> LK (g |- (a ∧ b) :: d)
  -- Γ , a |- Δ    Γ , b |- Δ
  -- ------------------------
  --      Γ , a ∨ b |- Δ
  OrL    : LK (a :: g |- d) -> LK (b :: g |- d) ->
           LK ((a ∨ b) :: g |- d)

  --  Γ |- a , Δ  "+"  Γ |- b , Δ
  -- ----------------------------
  --      Γ  |- a ∨ b , Δ
  OrR    : LK (g |- b :: d) + LK (g |- a :: d) ->
           LK (g |- (a ∨ b) :: d)
  --  Γ |- a , Δ      Σ , b |- Π
  -- --------------------------
  --  Σ , Γ , a -> b |- Δ , Π
  ImpL   : {Γ, Π, Δ, Σ, ΓΣ, ΔΠ : _} ->
           Cover Γ Σ  ΓΣ  -> Cover Δ Π ΔΠ ->
           LK (Γ |- a :: Δ) -> LK (b :: Σ |- Π) ->
           LK (((a ~~> b) :: ΓΣ) |- ΔΠ)

  --  Γ , a |- b , Δ
  -- ----------------
  --  Γ |- a -> b , Δ
  ImpR   : LK (a :: g |- b::d) -> LK (g |- (a~~>b)::d)
covering
Show (LK t) where
  show _ = "proven"
  -- show (NegL x) = "NegL " ++ show x
  -- show (NegR x) = "NegR " ++ show x
  -- show (AndL x) = "AndL " ++ show x
  -- show (AndR x y) = "AndR(" ++ show x ++ ", " ++ show y ++ ")"
  -- show (OrL x y) = "OrL(" ++ show x ++ ", " ++ show y ++ ")"
  -- show (OrR x) = "OrR " ++ show x
  -- show (ImpL x y z w) = "ImpL(" ++ show z ++ ", " ++ show w ++ ")"
  -- show (ImpR x) = "ImpR " ++ show x
checkProof : LK ([] |- [¬ (¬ a) ~~> a])
checkProof = ImpR (NegL (NegR Axiom))
Seq : Container
Seq = (s : Sequent) !> LK s
interface HemiDecidable (0 a : Type) where
  hdec : (x, y : a) -> Maybe (x === y)

hemEq : (a, b : Ty) -> Maybe (a === b)
hemEq (Atom a) (Atom b) with (decEq a b)
  hemEq (Atom a) (Atom a) | Yes Refl = Just Refl
  hemEq (Atom a) (Atom b) | No c = Nothing
hemEq (¬ x) (¬ y) = Prelude.map (\x => cong (¬) x) (hemEq x y)
hemEq (x ~~> y) (z ~~> w) = do
  Refl <- hemEq x z
  Refl <- hemEq y w
  pure Refl
hemEq _ _ = Nothing

HemiDecidable Ty where
  hdec = hemEq
applyAxiom : Seq =&> Any.Maybe I
applyAxiom = !! \case
  ([a] |- [c]) => case hemEq a c of
                      Just Refl => Just () ## (const Axiom)
                      Nothing => Nothing ## absurd
  _ => Nothing ## absurd
applyNegL : Seq =&> Any.Maybe Seq
applyNegL = !! \case
    (¬ a :: g |- d) => Just (g |- a :: d) ## (NegL . .unwrap)
    _ => Nothing ## absurd

applyNegR : Seq =&> Any.Maybe Seq
applyNegR = !! \case
    (g |- ¬ a :: d) => Just (a :: g |- d) ## (NegR . .unwrap)
    _ => Nothing ## absurd
applyAndL : Seq =&> Any.Maybe (Seq * Seq)
applyAndL = !! \case
    ((a ∧ b) :: g |- d) => Just ((b :: g |- d) && (a :: g |- d)) ## (AndL . .unwrap)
    _ => Nothing ## absurd

applyAndR : Seq =&> Any.Maybe (Seq ⊗ Seq)
applyAndR = !! \case
  (g |- (a ∧ b) :: d) => Just ((g |- a :: d) && (g |- b :: d)) ## (uncurry AndR . .unwrap)
  _ => Nothing ## absurd
applyOrL : Seq =&> Any.Maybe (Seq ⊗ Seq)
applyOrL = !! \case
  ((a ∨ b) :: g |- d) => Just ((a :: g |- d) && (b :: g |- d)) ## (uncurry OrL . .unwrap)
  _ => Nothing ## absurd

applyOrR : Seq =&> Any.Maybe (Seq * Seq)
applyOrR = !! \case
  (g |- (a ∨ b) :: d) => Just ((g |- b :: d) && (g |- a :: d)) ## (OrR . .unwrap)
  _ => Nothing ## absurd
applyImpR : Seq =&> Any.Maybe Seq
applyImpR = !! \case
    (g |- a ~~> b :: d) => Just (a :: g |- b :: d) ## (ImpR . .unwrap)
    _ => Nothing ## absurd
Cover' : Container
Cover' = (xy : List Ty) !> Σ (x : List Ty) | Σ (y : List Ty) | Cover x y xy
matchImpL : Seq =&> Any.Maybe ((Cover' ⊗ Cover') ▷ (Seq ⊗ Seq))
matchImpL = !! \case
    (a ~~> b :: g |- d) =>
      Just (MkEx (g && d)
          (\((gamma ## sigma ## gs) && (delta ## pi ## dp)) =>
                (gamma |- a :: delta) &&
                (b :: sigma |- pi)))
      ## (\xy =>
            let (((gamma ## sigma ## gs) && (delta ## pi ## dp)) ## xy) = xy.unwrap
            in ImpL gs dp xy.π1 xy.π2)
    _ => Nothing ## absurd
data Selector : List a -> Type where
  Nil : Selector []
  (::) : Bool -> Selector xs -> Selector (x :: xs)
createSingleCover : {0 a : Type} -> (xy : List a) -> Selector xy ->
    Σ (x : List a) | Σ (y : List a) | Cover x y (toList xy)
createSingleCover [] [] = [] ## [] ## Empty
createSingleCover (x :: xy) (False :: xs)  =
  let ls ## ks ## rs = createSingleCover xy xs
  in (x :: ls) ## ks ## PickL rs
createSingleCover (x :: xy) (True :: xs)  =
  let ls ## ks ## rs = createSingleCover xy xs
  in ls ## (x :: ks) ## PickR rs
coverBound : List a -> Nat
coverBound [] = 1
coverBound (x :: xs) = 2 * coverBound xs

createSelector :
   (cov : List Ty) ->
   (ix : Fin (coverBound cov)) ->
   Selector cov
createSelector [] ix = []
createSelector (x :: xs) ix =
  case splitFinPlus ((coverBound xs)) ((coverBound xs) + 0) ix of
       +> fn => True  :: createSelector xs (replace {p = Fin} (plusZeroRightNeutral ?) fn)
       <+ fn => False :: createSelector xs fn
SolveCover : Cover' =&> ListCont
SolveCover = !! \cov =>
    (coverBound cov)
    ## (\ix => createSingleCover cov (createSelector cov ix) )
covering
toSeq : ((Cover' ⊗ Cover') ▷ (Seq ⊗ Seq))
    =&> Any.List (Seq ⊗ Seq)
toSeq =  CalcWith {leq = (=&>)} $
  |~ (Cover' ⊗ Cover') ▷ (Seq ⊗ Seq)
  <~ (ListCont ⊗ ListCont) ▷ (Seq ⊗ Seq)
      ...((SolveCover ~⊗~ SolveCover) ~▷~ identity (Seq ⊗ Seq))
  <~ ListCont ▷ (Seq ⊗ Seq)
      ...(mult ~▷~ identity (Seq ⊗ Seq))
  <~ Any.List (Seq ⊗ Seq)
      ...(fromAny {a = Seq ⊗ Seq})
covering
applyImpL : Seq =&> Any.Maybe (Any.List (Seq ⊗ Seq))
applyImpL = matchImpL |&> Any.Maybe.map toSeq
SubSeq : Container
SubSeq = Any.List (All.List Seq)
seqToSub : Seq =&> SubSeq
seqToSub = !! \x => (pure (pure x)) ## All.head . .extract

endToSub : I =&> SubSeq
endToSub = !! \x => (pure []) ## const ()

pairToSub : Seq * Seq =&> SubSeq
pairToSub = !! \x =>  [[x.π1], [x.π2]] ## bimap All.head All.head . .extract2

tensorToAll : Seq ⊗ Seq =&> All.List Seq
tensorToAll = !! \x => ([x.π1, x.π2]) ## (\xx => All.head xx && head (tail xx))

tensorToSub : Seq ⊗ Seq =&> SubSeq
tensorToSub = tensorToAll |&> anyPure

anyToTactic : Any.List (Seq ⊗ Seq) =&> SubSeq
anyToTactic = Any.List.map tensorToAll
covering
seqTactics : List (Seq =&> Any.Maybe SubSeq)
seqTactics = [applyAxiom |&> Any.Maybe.map endToSub,
              applyNegL  |&> Any.Maybe.map seqToSub,
              applyNegR  |&> Any.Maybe.map seqToSub,
              applyAndL  |&> Any.Maybe.map pairToSub,
              applyAndR  |&> Any.Maybe.map tensorToSub,
              applyOrL   |&> Any.Maybe.map tensorToSub,
              applyOrR   |&> Any.Maybe.map pairToSub,
              applyImpL  |&> Any.Maybe.map anyToTactic,
              applyImpR  |&> Any.Maybe.map seqToSub]
covering
runAll : Seq =&> Any.Maybe SubSeq
runAll = tryAll {a = Seq, b = SubSeq} seqTactics
-- map all values through an applicative functor
allMap' : {0 a : Type} -> {0 b : a -> Type} -> Applicative m =>
         (f : (x : a) -> m (b x)) -> (xs : List a) -> m (All b xs)
allMap' f [] = pure []
allMap' f (x :: xs) = [| f x :: allMap' f xs |]

-- apply all values and join them using an alternative functor
anyMap' : {0 a : Type} -> {0 b : a -> Type} -> Alternative m =>
         (f : (x : a) -> m (b x)) -> (xs : List a) -> m (Any b xs)
anyMap' f [] = empty
anyMap' f (x :: xs) = map (Here {p = b, xs}) (f x)
                  <|> map (There {p = b, x}) (anyMap' f xs)

-- given a lens `a => Maybe (Any (List a))` generate a costate
-- `Maybe • a => I` by recursively applying the lens to all
-- sub-problems generated until none are left.
covering
loopTactics : (tactics : a =&> Any.Maybe (Any.List (All.List a))) ->
             (x : a.message) -> Maybe (a.response x)
loopTactics m x = case m.fn x of
  (Just py ## p2) =>
    map (p2 . Aye) $ anyMap' (allMap' (loopTactics m)) py
  (Nothing ## p2) => Nothing -- could not generate a sub-problem
covering
runProver : (x : Seq .message) ->  Maybe (Seq .response x)
runProver = loopTactics {a = Seq} runAll
doubleNeg : Sequent
doubleNeg = [] |- [(¬ (¬ (Atom 0))) ~~> Atom 0]

excluded : Sequent
excluded = [] |- [Atom 0 ~~> Atom 0 ∨ ¬ Atom 0]
