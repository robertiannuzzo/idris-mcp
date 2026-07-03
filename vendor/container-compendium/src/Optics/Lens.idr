module Optics.Lens

import Data.Category.Ops
import Data.Boundary
import Data.Product
import Data.Coproduct
import Data.Vect
import Data.Sigma

%hide Prelude.Monoid
%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)
public export
record Lens (a, b : Boundary) where
  constructor MkLens
  get : a.π1 -> b.π1
  set : a.π1 -> b.π2 -> a.π2
||| Lens composition
export
(|>) : Lens a b -> Lens b c -> Lens a c
(|>) l1 l2 = MkLens (l2.get . l1.get)
  (\x => l1.set x . l2.set (l1.get x))
||| Parallel composition
export
parallel : Lens a b -> Lens x y -> Lens (cartesian a x) (cartesian b y)
parallel l1 l2 = MkLens (bimap l1.get l2.get) (\x => bimap (l1.set (fst x)) (l2.set (snd x)))
public export
idLens : Lens x x
idLens = MkLens id (const id)
-- type aliases
Year = String
Month = String
Day = String

record Date where
  constructor MkDate
  year : Year
  month : Month
  day : Day

year' : Dup Date `Lens` Dup Year
year' = MkLens year (\date, newYear => MkDate newYear date.month date.day)

record User where
  constructor MkUser
  firstName : String
  lastName : String
  birthday : Date

birthday' : Dup User `Lens` Dup Date
birthday' = MkLens birthday (\user, newBd => MkUser user.firstName user.lastName newBd)

johnWrong : User
johnWrong = MkUser "John" "Appleseed" (MkDate "2001" "01" "12")

johnCorrect : User
johnCorrect = MkUser "John" "Appleseed" (MkDate "2000" "01" "12")

userBirthYear : Dup User `Lens` Dup Year
userBirthYear = birthday' |> year'

-- because the next function uses lowercase identifiers in the type we need to use this setting
%unbound_implicits off
-- test that updating the birth year works:
testBirthYear : johnCorrect === userBirthYear.set johnWrong "2000"
testBirthYear = Refl
%unbound_implicits on
(+) : Boundary -> Boundary -> Boundary
(+) x y = MkB (x.π1 + y.π1) (x.π2 + y.π2)

partial
choose : Lens a b -> Lens x y -> Lens (a + x) (b + y)
choose l1 l2 = MkLens
    (bimap l1.get l2.get)
    (let set1 = l1.set ; set2 = l2.set
    in \case (<+ v1) => \case (+> v2) => ?choose_rhs)
