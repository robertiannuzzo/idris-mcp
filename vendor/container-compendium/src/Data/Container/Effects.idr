module Data.Container.Effects

import Data.Category.Endofunctor
import Data.Category.Set

import Data.Container.Lift
import Data.Container.Apply.Definition
import Data.Container.Definition
import Data.Container.Morphism
import Data.Container.Morphism.Context
import Data.Container.Tensor.Bifunctor
import Data.Container.Tensor.Monoidal
import Data.Container.Sequence.Bifunctor
import Data.Container.Sequence.Monoidal
import Data.Container.List.Functor

import Data.List.Quantifiers

import Data.Vect

import System
import System.File
import System.Utils

import Syntax.PreorderReasoning.Generic

import Control.Monad.Either
import Control.Monad.Trans

readChars : List Char -> IO (List Char)
readChars acc = do
  end <- fEOF stdin
  if end
    then pure acc
    else do
      c <- getChar
      assert_total $ readChars (c :: acc)

readLines : IO (String)
readLines = reverse <$> pack <$> readChars []
-- an effectful program can be seen as a costate lens with an IO lift
-- since it's isomorphic to a function (m : program.message) -> IO (program.response m)
exampleEffectfulLens : Costate (IO • program)
covering
readPrint : String :- IO () =%> IO (Either FileError String) :- String
readPrint = readFile <! const (putStrLn {io = IO})
PrintLn : Container
PrintLn = String :- Unit
GetArgs : Container
GetArgs = Unit :- List String
record WriteFileOp where
  constructor MkWrite
  filename : String
  content : String

WriteFile : Container
WriteFile = (WriteFileOp :- Unit)
STDIN : Container
STDIN = Unit :- String
Tee : I =%> (GetArgs ⊗ STDIN) ▷ (PrintLn ⊗ All.List WriteFile)
Tee = state  (MkEx (() && ())
    $ \case ((_ :: files) && content) => content && map (\file => MkWrite file content) files
            (_ && content) => content && [])
FSIO : Type -> Type
FSIO = EitherT FileError IO

handleSTDIN : Costate (FSIO • STDIN)
handleSTDIN = costate $ const (lift readLines)

handlePrintLn : Costate (FSIO • PrintLn)
handlePrintLn = costate $ lift . putStrLn

parseN : (n : Nat) -> List a -> Maybe (Vect n a)
parseN Z [] = Just []
parseN (S n) (x :: xs) = (x ::) <$> parseN n xs
parseN _ _ = Nothing

handleGetArgs : Costate (FSIO • GetArgs)
handleGetArgs = costate $ \_ => getArgs

handleWriteFile : Costate (FSIO • WriteFile)
handleWriteFile = costate $ \(MkWrite name content) => MkEitherT $ writeFile name content
run : {m : Type -> Type} ->
      {a, b, c : Container} -> Monad m =>
      Costate (m • b) -> Costate (m • c) -> a =%> (b ▷ c) -> Costate (m • a)
run handleB handleC lens =
  CalcWith {leq = (=%>), x = m • a, y = I} $
    |~ m • a
    <~ m • (b ▷ c)
      ...(fmap {m} lens) -- map our lens into one with effects
    <~ m • (b ▷ m • c)
      ...(δ)             -- distribute the effect
    <~ m • (b ▷ I)
      ...(fmap {m} (identity b ~▷~ handleC)) -- handle the nested effect
    <~ m • b
      ...(fmap {m} (unitR1 {a = b}))         -- remove the extra unit
    <~ I
      ...(handleB)                           -- handle the remaining effect
export
pushTensor : Monad m => {0 b : Container} ->
    m • (All.List b) =%> All.List (m • b)
pushTensor = (\x => x) <! pushBwd
  where
    pushBwd :
      (xs : List b.request) ->
      All.All (m . b.response) xs ->
      m (All.All b.response xs)
    pushBwd [] x = pure []
    pushBwd (y :: ys) (x :: xs) = do
      x' <- x
      xs' <- pushBwd ys xs
      pure (x' :: xs')
covering
main : IO ()
main = eitherT
  printLn  -- print errors
  pure  -- handle values in IO  normally
  $ runCostate teeProgram () -- run the `() -> IO ()` program
  where

  -- handling the command line input and stdin input
  handleInputs : Costate (FSIO • (GetArgs ⊗ STDIN))
  handleInputs = CalcWith $
    |~ FSIO • (GetArgs ⊗ STDIN)
    <~ (FSIO • GetArgs) ⊗ (FSIO • STDIN)
    ...(distribTensor {m = FSIO, a = GetArgs, b = STDIN})
    <~ I ⊗ I
    ...(handleGetArgs ~⊗~ handleSTDIN)
    <~ I
    ...(unitR {a = I})

  -- Handling the printing and the writing at once
  handleFile : Costate (FSIO • (PrintLn ⊗ All.List WriteFile))
  handleFile = CalcWith {leq = (=%>)} $
    |~ FSIO • (PrintLn ⊗ All.List WriteFile)
    <~ FSIO • PrintLn ⊗ FSIO • All.List WriteFile
    ...(distribTensor {m = FSIO, a = PrintLn, b = All.List WriteFile})
    -- distribute the effect across ⊗
    <~ FSIO • PrintLn ⊗ All.List (FSIO • WriteFile)
    ...(identity (FSIO • PrintLn) ~⊗~ pushTensor {m = FSIO, b = WriteFile})
    <~ I ⊗ All.List I
    ...(handlePrintLn ~⊗~ mapList handleWriteFile)
    -- Handle printing and writing the file concurrently
    <~ I ⊗ I
    ...(identity I ~⊗~ elimI)
    <~ I
    ...(unitR {a = I})

  -- The program after applying all handlers
  teeProgram : Costate (FSIO • I)
  teeProgram =
        (run {a = I, b = (GetArgs ⊗ STDIN), c = PrintLn ⊗ All.List WriteFile}
            handleInputs handleFile Tee)
