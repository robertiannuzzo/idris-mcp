module Pipeline.Equality

import Control.Category
import public Data.List.Quantifiers
import Data.Nat

%default total

public export
data CongPipeline : (size : Nat) -> (obj : Type) -> Type where
  Nil : CongPipeline Z o
  (::) : o -> CongPipeline n o -> CongPipeline (S n) o
  AddNest : {0 innerObj, outerObj : Type} ->
            {0 m, n : Nat} ->
            (fd : innerObj -> outerObj) ->
            (ts : CongPipeline (S n) innerObj) ->
            CongPipeline m outerObj ->
            {0 sum : Nat} ->
            (check : S n + m = sum) =>
            CongPipeline sum outerObj
public export
head : {0 n : Nat} -> (ts : CongPipeline (S n) o) -> o
head (x :: y) = x
head (AddNest f ts _) = f (head ts)
public export
last : {0 n : Nat} -> (ts : CongPipeline (S n) o) -> o
last (x :: []) = x
last (x :: n@(y :: z)) = last n
last (x :: (AddNest fd ts y)) = assert_total $ Equality.last (AddNest fd ts y)
last (AddNest f ts []) = f (last ts)
last (AddNest fd ts n@(x :: y)) = last n
last (AddNest fd ts (AddNest x y z)) = assert_total $ last (AddNest x y z)
public export
ToList : {0 n : Nat} -> {0 ty : Type} -> CongPipeline n ty -> List Type

public export
combineRest : {0 ty : Type} -> (end : ty) -> (x : CongPipeline m ty) -> List Type
combineRest end [] = []
combineRest end (Equality.(::) x y) = (end === x) :: ToList (x :: y)
combineRest end (AddNest f y z) =
    (end === head (AddNest f y z)) :: ToList (AddNest f y z)

ToList [] = []
ToList (Equality.(::) x []) = []
ToList (Equality.(::) x (Equality.(::) y z)) = (x === y) :: ToList (y :: z)
ToList (Equality.(::) x (AddNest fd ts y))
    = (x === fd (head ts)) :: ToList ts ++ combineRest (fd (last ts)) y
ToList (AddNest fd ts x) = ToList ts ++ combineRest (fd (last ts)) x
public export
Prove : CongPipeline n ty -> Type
Prove x = HList (ToList x)
export
runProof : (spec : CongPipeline (S n) ty) -> (steps : Prove spec) -> head spec === last spec
runProof (Equality.(::) x []) steps = Refl
runProof (Equality.(::) x (Equality.(::) y z)) (w :: v) = trans w (runProof (y :: z) v)
runProof (Equality.(::) x (AddNest fd ts y)) (s1 :: s2)
  = trans s1 $ runProof (AddNest fd ts y) s2
runProof (AddNest fd ts []) steps with (splitAt ? steps)
  runProof (AddNest fd ts []) steps | (p, _) =
    cong fd (assert_total $ runProof ts p)
runProof (AddNest fd ts (Equality.(::) x y)) steps with (splitAt ? steps)
  runProof (AddNest fd ts (Equality.(::) x y)) steps | (p1, p2 :: p3) =
    let q1 = assert_total $ runProof ts p1
        q2 = assert_total $ runProof (x :: y) p3
    in trans (cong fd q1) (trans p2 q2)
runProof (AddNest fd ts (AddNest f x y)) steps with (splitAt ? steps)
  runProof (AddNest fd ts (AddNest f x y)) steps | (p1, p2 :: p3) =
    let q1 = assert_total $ cong fd (runProof ts p1)
        q2 = assert_total $ runProof (AddNest f x y) p3
    in trans q1 (trans p2 q2)
-- proof plan without nesting
flatPlan : (a, b, c, d : Nat) -> CongPipeline ? Nat
flatPlan a b c d =
  [ a + (b + (c + d))
  , a + (b + (d + c))
  , a + ((d + c) + b)
  , ((d + c) + b) + a
  , (d + (c + b)) + a
  , d + ((c + b) + a)
  , d + (c + (b + a))
  ]

flatSteps : {a, b, c, d : Nat} -> Prove (Equality.flatPlan a b c d)
flatSteps =
  [ cong (a +) (cong (b+) (plusCommutative c d))
  , cong (a +) (plusCommutative ? ?)
  , plusCommutative a ((d + c) + b)
  , cong (+ a) (sym $ plusAssociative d c b)
  , (sym $ plusAssociative d (c + b) a)
  , cong (d + ) (sym $ plusAssociative c b a)
  ]

flatProof : {a, b, c, d : Nat} -> a + (b + (c + d)) = d + (c + (b + a))
flatProof = runProof (flatPlan a b c d) flatSteps
test2 : (a, b, c, d : Nat) -> CongPipeline ? Nat
test2 a b c d =
  Cong (a +)
      (Cong (b +)
          [ c + d       -- commute c and d
          , d + c]      -- commute b and (d + c)
      >| [(d + c) + b]) -- comute a and (d + c) + b
  >| Cong (+ a)
      [ (d + c) + b     -- assoc d c b
      , d + (c + b)]    -- assoc a d (c b)
  >| Cong (d +)
      [ (c + b) + a     -- assoc c b a
      , c + (b + a)]
  >| Nil

test2Impl : {a, b, c, d : Nat} -> Prove (Equality.test2 a b c d)
test2Impl =
  [ plusCommutative {}
  , plusCommutative {}
  , plusCommutative {}
  , sym (plusAssociative {})
  , sym (plusAssociative {})
  , sym (plusAssociative {})
  ]

testRun2 : {a, b, c, d : Nat} -> a + (b + (c + d)) = d + (c + (b + a))
testRun2 = runProof (test2 a b c d) test2Impl
