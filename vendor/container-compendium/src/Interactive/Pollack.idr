module Interactive.Pollack

%default covering
data Token
  = Let
  | Lambda
  | Dot
  | Str String
  | Num Int
  | LParen
  | RParen
  | Space

data Syntax
  = Abs String Syntax
  | App Syntax Syntax
  | Var String

takeUntilCloses : List Token -> Nat -> List Token -> (List Token, List Token)
takeUntilCloses [] count acc = (reverse acc, [])
takeUntilCloses (LParen :: xs) 0 acc = (reverse acc, xs)
takeUntilCloses (LParen :: xs) (S n) acc = takeUntilCloses xs n (LParen :: acc)
takeUntilCloses (RParen :: xs) n acc = takeUntilCloses xs (S n) (RParen :: acc)
takeUntilCloses (x :: xs) n acc = takeUntilCloses xs n (x :: acc)

parse : List Token -> Maybe Syntax
parse (Lambda :: Space :: Str varName :: Space :: Dot :: Space :: rest) = Abs varName <$> parse rest
parse (Lambda :: Space :: Str varName :: Space :: Dot :: rest) = Abs varName <$> parse rest
parse (Lambda :: Space :: Str varName :: Dot :: Space :: rest) = Abs varName <$> parse rest
parse (Lambda :: Str varName :: Space :: Dot :: Space :: rest) = Abs varName <$> parse rest
parse (Lambda :: Str varName :: Dot :: Space :: rest) = Abs varName <$> parse rest
parse (Lambda :: Str varName :: Space :: Dot :: rest) = Abs varName <$> parse rest
parse (Lambda :: Str varName :: Dot :: rest) = Abs varName <$> parse rest
parse (LParen :: rest)  = case !(parseExpr rest) of
                               (expr, []) => pure expr
                               (fn, arg) => App fn <$> parse rest
  where
    parseExpr : List Token -> Maybe (Syntax, List Token)
    parseExpr xs = let (pre, post) = takeUntilCloses xs 0 []
                   in Just (!(parse pre), post)
parse [Str s]  = Just $ Var s
parse _ = Nothing

print : Syntax -> List Token
print (Abs str x) = Lambda :: Space:: Str str :: Space :: Dot :: Space ::  print x
print (App x y) = print x ++ Space :: print y
print (Var str) = pure $ Str str

check : (t : Syntax) -> parse (print t) === Just t
check (Abs str x) with (check x) | (parse (print x))
  check (Abs str x) | Refl | (Just x) = Refl
check (App x y) with (check x) | ((print x))
  check (App x y) | prg | ([]) = absurd prg
  check (App x y) | prg | ((Lambda :: Space :: Str nm :: Space :: Dot :: Space :: xs)) = ?check_rhs_1_rhs1_4
  check (App x y) | prg | ((_ :: xs)) = ?no
check (Var str) = Refl

testParser : parse [Lambda, Space, (Str "x"), Space, Dot, Space, Str "x"] === Just (Abs "x" (Var "x"))
testParser = Refl

