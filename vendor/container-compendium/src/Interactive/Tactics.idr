module Interactive.Tactics

import Data.Container
import Data.Container.Category
import Data.Category.Functor
import Data.Container.Descriptions.Maybe
import Data.Container.Maybe.Functor
import Data.Container.Maybe.Definition
import Data.Container.Closed
import Data.Container.Closed.Definition
import Data.Container.Closed.Maybe.Functor
import Data.Container.Closed.Maybe.Monad
import Data.Container.Closed.Tensor
import Data.Container.Closed.Tensor.Bifunctor
import Data.Container.Closed.Tensor.Monoidal
import Data.Container.Tensor.Definition
import Data.Product
import Data.Sigma
import Data.Maybe
import Data.Maybe.Any
import Proofs.Sigma

import Decidable.Equality

%hide Prelude.(&&)

%default total
data Term : Type where
  Zero : Term
  Succ : Term -> Term
  (+) : Term -> Term -> Term
data Eq : Term -> Term -> Type where
  Refl : Eq t t
  Trans : Eq r s -> Eq s t -> Eq r t
  Cong : Eq t s -> Eq (Succ t) (Succ s)
  CPlus : Eq t s -> Eq x y -> Eq (t + x) (s + y)
  Sym : Eq t s -> Eq s t
  Assoc : Eq t1 t2 -> Eq r1 r2 -> Eq s1 s2 ->
          Eq ( t1 + (r1  + s1))
             ((t2 +  r2) + s2)
EqProblem : Container
EqProblem = (t : Term * Term) !> uncurry Eq t
sym : EqProblem =&> EqProblem
sym = !! \x => swap x ## Sym
eq : (t, s : Term) -> Maybe (t === s)
eq Zero Zero = Just Refl
eq (Succ x) (Succ y) = map (\w => cong Succ w) (eq x y)
eq (x + y) (a + b) = do Refl <- eq x a
                        Refl <- eq y b
                        Just Refl
eq _ _ = Nothing
refl : EqProblem =&> Any.Maybe I
refl = !! \x => case eq x.π1 x.π2 of
                     Nothing => Nothing ## absurd
                     Just p => Just () ## (\_ => rewrite p in Refl)
trans : (term : Term) -> EqProblem =&> (EqProblem ⊗ EqProblem)
trans term = !! \x => ((x.π1 && term) && (term && x.π2)) ## uncurry Trans
assoc : EqProblem =&> Any.Maybe (EqProblem ⊗ (EqProblem ⊗ EqProblem))
assoc = !! \case ((a + (b + c)) && ((a' + b') + c')) =>
                     Just ((a && a') && (b && b') && (c && c')) ##
                       \(Aye (x1 && x2 && x3)) => Assoc x1 x2 x3
                 _ => Nothing ## absurd
combineUnits : Any.Maybe I ⊗ Any.Maybe I =&> Any.Maybe I
combineUnits = Any.strengthL {a = I, b = Any.Maybe I}
    |&> Any.mapMaybe {a = I ⊗ Any.Maybe I, b = Any.Maybe I} unitL
    |&> Any.join {a = I}

tripleRight : a ⊗ a =&> a -> a ⊗ (a ⊗ a) =&> a
tripleRight m = Data.Container.Closed.Tensor.Bifunctor.(~⊗~) (Data.Container.Closed.Definition.identity a) m |&> m
assocCompose : EqProblem =&> (Any.Maybe I)
assocCompose
    = sym
    |&> assoc
    |&> Closed.Maybe.Functor.Any.mapMaybe
            ((refl ~⊗~ (refl ~⊗~ refl))
                |&> tripleRight combineUnits)
    |&> Any.join {a = I}
