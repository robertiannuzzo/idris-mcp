module Interactive.Desugaring

import Data.List
import Data.Fin
import Data.Sigma
import Data.Coproduct
import Data.Vect
import Data.Product
import Data.Container
import Data.Container.Morphism
import Data.Container.Tensor.Bifunctor
import Data.Container.Tensor.Monoidal
import Data.Container.Descriptions.Maybe
import Data.Container.Descriptions.List


%default covering

||| Raw syntax with let bindings
namespace Raw
  public export
  data Syntax : Type where
    Variable : String -> Syntax
    Lambda : List String -> Syntax -> Syntax
    Let : String -> Syntax -> Syntax -> Syntax
    App : Syntax -> Syntax -> Syntax


-- name for extracting the arguments from the syntax nodes
record VarArg where
  constructor MkVarArg
  variable : String

record LamArgs  where
  constructor MkLamArgs
  args : List String
  body : Syntax

record LetArgs where
  constructor MkLetArgs
  name : String
  expr : Syntax
  body : Syntax

record AppArgs where
  constructor MkAppArgs
  fn : Syntax
  arg : Syntax

-- Target language, a lambda calculus without let binding
namespace LC
  public export
  data Lam : Type where
    Variable : String -> Lam
    Lambda : List String -> Lam -> Lam
    App : Lam -> Lam -> Lam

-- The syntax containers,
Syn : Container
Syn = Syntax :- Lam

-- Rewriting variables does not produce any more subgoals
rewriteVar : VarArg :- Lam =%> I
-- rewriteVar = mkLens (Variable . variable)

Either' : Type -> Type -> Type
Either' a b = Σ Bool (\x => if x then a else b)


test : Either' String Int
test = ?whut
-- Rewriting lambda generates a subgoal for the lambda body
rewriteLam : LamArgs :- Lam =%> Syn
rewriteLam =
  (\(MkLamArgs name body) => body) <!
  (\(MkLamArgs args body), body' => Lambda args body')

-- Rewriting application generates two subgoals, on for the functio
-- and one for its argument
rewriteApp : AppArgs :- Lam =%> Syn ⊗ Syn
rewriteApp =
  (\(MkAppArgs a b) => a && b) <!
  (\_, x => App x.π1 x.π2)

-- rewriting let generates two subgoals, one for the variable bound
-- and one for the program body
rewriteLet : LetArgs :- Lam =%> Syn ⊗ Syn
rewriteLet =
    (\(MkLetArgs n a b) => a && b) <!
    (\(MkLetArgs n _ _), x => App (Lambda [n] x.π2) x.π1)

-- Prism does case analysis on the input and returns a choice of
-- constructor
-- (Unit, const Void) + c ≅ MaybeCont ▶ c
prism : Syn =%> (VarArg  :- Lam)
              + (LamArgs :- Lam)
              + (AppArgs :- Lam)
              + (LetArgs :- Lam)
prism =
  match <! rebuild
  where
    match : Syntax -> VarArg + LamArgs + AppArgs + LetArgs
    match (Variable str) = <+ <+ <+ MkVarArg str
    match (Lambda strs x) = <+ <+ +> MkLamArgs strs x
    match (Let str x y) = +> MkLetArgs str x y
    match (App x y) = <+ +> MkAppArgs x y

    rebuild : (s : Syntax) ->
       response
           ((VarArg  :- Lam)
          + (LamArgs :- Lam)
          + (AppArgs :- Lam)
          + (LetArgs :- Lam))
          (match s) ->
       Lam
    rebuild (Variable str) x = x
    rebuild (Lambda strs y) x = x
    rebuild (Let str y z) x = x
    rebuild (App y z) x = x


-- could simplify this by using the bifunctor instance (+)
dia4 : a + a + a + a =%> a
dia4 =
    (\case (<+ (<+ (<+ x))) => x
           (<+ (<+ (+> x))) => x
           (<+ (+> x)) => x
           (+> x) => x) <!
    (\case (<+ (<+ (<+ x))) => id
           (<+ (<+ (+> x))) => id
           (<+ (+> x)) => id
           (+> x) => id)

-- rewriting the whole language using recursion
rewriteAll : Syn =%> I
rewriteAll = prism |%> rewriteNest |%> dia4
   where
     rewriteNest : (VarArg  :- Lam)
                 + (LamArgs :- Lam)
                 + (AppArgs :- Lam)
                 + (LetArgs :- Lam) =%> I + I + I + I
     rewriteNest = rewriteVar
                ~+~ (rewriteLam |%> rewriteAll)
                ~+~ (rewriteApp |%> (rewriteAll ~⊗~ rewriteAll) |%> unitL {a = I})
                ~+~ (rewriteLet |%> (rewriteAll ~⊗~ rewriteAll) |%> unitL {a = I})
