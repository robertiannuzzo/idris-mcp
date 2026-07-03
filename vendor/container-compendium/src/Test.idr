
import Data.List1
import Data.List
import Data.Container.Morphism
import Data.Container.Maybe

parser : List a -> Either String (List1 a)
parser [] = ?parser_rhs_0
parser (x :: xs) = ?parser_rhs_1

0 ListQuery : (List a -> Type) -> Container
ListQuery p = (!>) (List a) p


0 NonEmptyPred : {a : Type} -> Container
NonEmptyPred = ListQuery (NonEmpty {a})

parserLens : {a : Type} -> NonEmptyPred {a} =%> ((b : Bool) !> (if b then List1 a else Void))
parserLens = MkMorphism (not . null) (\case [] => absurd
                                            (x :: xs) => \ys => IsNonEmpty)

data AST = Expr Nat | Plus AST AST | Neg AST

data IsValid : List Char -> Type where
  IsPlus : IsValid left -> IsValid right -> IsValid (left ++ ['+'] ++ right)

data IAST : AST -> Type where
  IPlus : IAST (Plus l r)

parseExpr : List Char -> Maybe AST

ASTC : Container
ASTC = (!>) (List Char) IsValid

astParser : ASTC =%> ((b : Maybe AST) !> maybe Void IAST b)
astParser = MkMorphism parseExpr (\input, response => ?astParser_rhs_1)

