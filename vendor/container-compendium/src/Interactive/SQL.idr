module Interactive.SQL

import Derive.Sqlite3
import Control.RIO.Sqlite3
import Control.RIO.App
import Control.RIO
import Data.Sigma

import Data.Container
import Data.Container.Morphism
import Data.Container.Kleene
import Data.Container.Descriptions.Maybe
import Data.Maybe
import Data.Either
import Data.Sum

import Data.String.Parser

import JSON.Derive
import System.File

%language ElabReflection
%default total

%hide Data.List.Alternating.infixr.(<+)
%hide Data.List.Alternating.infixl.(<+)
%hide Data.String.Extra.infixr.(<+)
%hide Data.String.Extra.infixl.(+>)
public export
ID : Type
ID = Integer
-- And a status to indicate if the item is marked as done.
data Status = Done | NotDone

toBool : Status -> Bool
toBool Done = True
toBool NotDone = False

fromBool : Bool -> Status
fromBool True = Done
fromBool False = NotDone
record Todo where
  constructor MkTodo
  id : ID
  content : String
  status : Status
data TodoCommand
  = Create String
  | Delete ID
  | MarkComplete ID
  | RetrieveAll
  
-- The CLI is represented as a container that expects strings as input
-- and returns strings as output.
CLI : Container
CLI = String :- String

-- AppOp is the abstract API of our app, we take in commands, and returns
-- either unit, or tables from queries. Will run in FM.
AppOp : Container
AppOp = (!>) TodoCommand CmdReturn

-- Interface for database commands. Commands only perform side-effects so the
-- results are always Unit
DBCmd : Container
DBCmd = Σ CmdType Cmd :- ()

-- Interface of a database queries. Queries always return tables of a matching type
0 DBQry : Container
DBQry = (x : ValidQuery) !> Table x.ty

----------------------------------------------------------------------------------
-- Containers Morphisms                                                         --
----------------------------------------------------------------------------------

-- The errors that our program will deal with
0 Errs : List Type
Errs = [SqlError]

-- The monad in which we run our program as an endofunctor in Cont
0 FM : Container -> Container
FM x = F (App Errs) x

---------------------------------
-- Running database operations --
---------------------------------

-- Running a command as a costate
CmdCostate : DB => Costate (FM DBCmd)
CmdCostate = costate (\x => cmd {t = x.π1} x.π2)

-- Running a query as a costate
DBQueryCostate : DB => Costate (FM DBQry)
DBQueryCostate = costate runValid

-- Running either a command or a query on a database as a costate
DBCostate : DB => Costate (FM (DBCmd + DBQry))
DBCostate = distrib_plus {f = App Errs, a = DBCmd, b = DBQry}
         |> CmdCostate + DBQueryCostate |> dia

---------------------------------------
-- Interacting with the command line --
---------------------------------------

-- We need a parser to parse command line arguments and translate them into
-- internal Todo commands.
cmdParser : Parser TodoCommand
cmdParser = assert_total $
            string "create" *> spaces *> char '"' *> Create <$> takeWhile (/= '"')
        <|> string "done" *> spaces *> MarkComplete <$> cast <$> natural
        <|> string "delete" *> spaces *> Delete <$> cast <$> natural
        <|> string "print" *> pure RetrieveAll

parseInput' : String -> Maybe TodoCommand
parseInput' str = eitherToMaybe $ map fst $ parse cmdParser str

-- Convert a string-based api into the AppOp interface
-- MaybeA is the error monad where all errors need to be handled
cliParser : CLI =%> MaybeAll AppOp
cliParser = MkMorphism parseInput' printOutput
  where
    printResult : (v : TodoCommand ** CmdReturn v) -> String
    printResult (RetrieveAll ** b)  = prettyTable b
    printResult (MarkComplete id ** y) = "done"
    printResult (Create content ** y) = "done"
    printResult (Delete id ** y)  = "deleted \{show id}"

    printOutput : (x : String) -> (All CmdReturn (parseInput' x)) -> String
    printOutput x y with (parseInput' x)
      printOutput x Nay | Nothing = "could not parse '\{x}'"
      printOutput x (Yay y) | (Just z) = printResult (z ** y)

-- The parser lifted into effectful bidirectional programs
-- Note that the parser itself does not concern itself with effects but
-- we can lift it to make to compatible with effectful programs.
parser : FM CLI =%> FM (MaybeAll AppOp)
parser = f_functor cliParser

---------------------------------------
-- Converting to database operations --
---------------------------------------

-- Converting from internal app commands to database commands
-- Again, notice that this is a pure interface, but the monad on containers
-- will make this compatible with the rest of the infrastructure.
OpToDB : AppOp =%> DBCmd + DBQry
OpToDB = MkMorphism convertCommand convertBack
  where
    convertCommand : TodoCommand -> Σ CmdType Cmd + ValidQuery
    convertCommand (Create str) = <+ (_ ## addTodoItem str)
    convertCommand (Delete i) = <+ (_ ## deleteItem (cast i))
    convertCommand (MarkComplete i) = <+ (_ ## itemMarkDone (cast i))
    convertCommand RetrieveAll = +> MkValidQuery _ %search getAllItems

    convertBack : (x : TodoCommand) -> (DBCmd + DBQry).pos (convertCommand x) ->
                  CmdReturn x
    convertBack (Create str) y = ()
    convertBack (Delete i) y = ()
    convertBack (MarkComplete i) y = ()
    convertBack RetrieveAll y = y

-- Commands translated to database operations lifted into the correct monads
-- We lift our translatin to database operation through both FM and MaybeA
commands : DB => FM (MaybeAll AppOp) =%> MaybeAll (FM (DBCmd + DBQry))
commands = distribMaybeAF {a = AppOp} |> map_MaybeAll (f_functor OpToDB)

-- The application itself as a Costate of FM CLI
-- - First run the parser
-- - Then convert commands into database operations
-- - Then run the database
appCont : DB => Costate (FM CLI)
appCont = parser |> commands  |> map_MaybeAll DBCostate |> maybeAUnit

----------------------------------------------------------------------------------
-- Running the app as a REPL                                                    --
----------------------------------------------------------------------------------

partial
repl : HasIO io => (String -> io String) -> io ()
repl f = do
  line <- getLine
  output <- f line
  putStrLn output
  repl f

-- Running the repl with our String -> String function extracted from the
-- costate `Costate (FM CLI)`
partial
app : DB => App Errs Unit
app = repl (extract appCont)

-- Running the database commands to setup an initial state
partial
runDB : App Errs Unit
runDB = withDB ":memory:" $
        cmd createTodos *> app

-- Running the main app using RIO
partial
main : IO ()
main = runApp [ printLn ] runDB
