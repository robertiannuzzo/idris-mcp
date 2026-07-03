module Data.Category.Notation

import public Data.Category

export infixr 4 -<
export infixr 4 >-

%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

mutual
  public export
  data Comp : (cat : Category o) => (a, b : o) -> Type where
    (-<) : (cat : Category o) => (a : o) -> Next a c -> Comp a c
    End : (cat : Category o) => (a : o) -> Comp a a

  public export
  data Next : (cat : Category o) => (a, c : o) -> Type where
    (>-) : (cat : Category o) => {a, b, c : o} -> (f : a ~> b) -> Comp b c -> Next a c

  public export 0
  Start : (cat : Category o) => {a, b : o} -> Comp a b -> a ~> b
  Start (End a) = cat.id a
  Start ((-<) x y {c=k}) = continue y

  public export 0
  continue : (cat : Category o) => {a, b : o} -> Next a b -> a ~> b
  continue ((>-) f (End l) ) = f
  continue ((>-) f x {b=k} ) = f |> Start x

