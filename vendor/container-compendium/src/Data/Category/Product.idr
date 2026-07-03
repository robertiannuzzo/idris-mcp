module Data.Category.Product

import Data.Category
import Data.Category.Functor
import Data.Category.Iso
import public Data.Category.Notation
import Data.Category.Preorder

import Data.Iso
import Data.Iso.Category
import public Data.Product

import Proofs


%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

-- reads as ×
private infixl 5 >:<
public export
record HasProduct {0 o : Type} (cat : Category o) where
  constructor MkProd

  (>:<) : o -> o -> o
  pi1 : {0 a, b : o} -> a >:< b ~> a
  pi2 : {0 a, b : o} -> a >:< b ~> b
  prod : {0 a, b, c: o} ->
         c ~> a ->
         c ~> b ->
         c ~> (a >:< b)
  0 prodLeft : {0 a, b, c : o} -> (f : c ~> a) -> (g : c ~> b) ->
             (|>) {a=c} {b=(a >:< b)} {c=a}
                  (prod {a} {b} {c} f g)
                  (pi1 {a} {b})
                = f
  0 prodRight : {0 a, b, c : o} -> (f : c ~> a) -> (g : c ~> b) ->
              (|>) {a=c} {b=(a >:< b)} {c=b}
                   (prod {a} {b} {c} f g)
                   (pi2 {a} {b})
                 = g

  0 uniq : {0 a, b, c : o} ->
         (f1 : c ~> a) ->
         (f2 : c ~> b) ->
         (p : c ~> a >:< b) ->
         Start (c -< p >- (a >:< b)
                  -< pi1 {a} {b}>- End a) === f1 ->
         Start (c -< p >- (a >:< b)
                  -< pi2 {a} {b} >- End b) === f2 ->
         prod {a} {b} {c} f1 f2 === p
public export
(><) : {auto cat : Category o} -> (prod : HasProduct cat) => o -> o -> o
(><) = (>:<) prod

public export
0 (~><~) : (cat : Category o) => (prod : HasProduct cat) =>
        {a, b, c, d : o} ->
        a ~> b -> c ~> d ->
        a >< c ~> b >< d
(~><~) m1 m2 = prod.prod (prod.pi1 {a, b = c} |> m1) (prod.pi2 {a, b = c} |> m2)
record HasCartesianProduct (cat : Category Type) where
