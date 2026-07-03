module McpReal

-- =============================================================================
-- MCP (Model Context Protocol) as containers and dependent lenses, take 2 --
-- this time against the REAL container-compendium library (installed as the
-- `container-compendium` package) instead of the self-contained toy
-- Container/Lens from mcp-containers/Mcp.idr.
--
--   Container  = Data.Container.Definition.Container   (record (!>), .request/.response)
--   :-         = Data.Container.Definition.(:-)
--   (=%>)      = Data.Container.Morphism.Definition.(=%>)  (dependent lens / container morphism)
--   identity, (|%>) = Data.Container.Morphism.Definition
--
-- Everything below section 2 is otherwise unchanged from Mcp.idr: same
-- Method/ResultOf/MCP container, same server-as-section, same
-- client-as-Moore-machine-lens, same closed loop and negative demo. The point
-- is to show the design survives contact with the real, independently-typed
-- library rather than being an artifact of a hand-rolled Container/Lens pair.
-- =============================================================================

import Data.Container.Definition
import Data.Container.Morphism.Definition

-- -----------------------------------------------------------------------------
-- 2. MCP data types (shapes from the 2025-06-18 / 2025-11-25 MCP schema)
-- -----------------------------------------------------------------------------

public export
record Tool where
  constructor MkTool
  name        : String
  description : String

public export
record TextContent where
  constructor MkText
  text : String

public export
record ToolResult where
  constructor MkToolResult
  content : List TextContent
  isError : Bool

public export
record ServerInfo where
  constructor MkServerInfo
  name    : String
  version : String

public export
record InitializeResult where
  constructor MkInit
  protocolVersion : String
  serverInfo      : ServerInfo
  toolsCapability : Bool

public export
record ResourceContents where
  constructor MkResource
  uri      : String
  mimeType : String
  text     : String

-- -----------------------------------------------------------------------------
-- 3. The MCP interface as a real container, with DEPENDENT responses
-- -----------------------------------------------------------------------------

public export
data Method : Type where
  Initialize   : (clientName : String) -> Method
  ListTools    : Method
  CallTool     : (name : String) -> (args : List (String, String)) -> Method
  ReadResource : (uri : String) -> Method

public export
ResultOf : Method -> Type
ResultOf (Initialize _)   = InitializeResult
ResultOf ListTools        = List Tool
ResultOf (CallTool _ _)   = ToolResult
ResultOf (ReadResource _) = ResourceContents

public export
MCP : Container
MCP = (m : Method) !> ResultOf m

-- -----------------------------------------------------------------------------
-- 4. The SERVER -- a stateful section (the reactive half)
-- -----------------------------------------------------------------------------

public export
record Registry where
  constructor MkRegistry
  tools     : List Tool
  resources : List (String, String)

assoc : String -> List (String, String) -> Maybe String
assoc _ [] = Nothing
assoc k ((k', v) :: rest) = if k == k' then Just v else assoc k rest

argOr : String -> String -> List (String, String) -> String
argOr key def args = case assoc key args of
                       Just v  => v
                       Nothing => def

runTool : String -> List (String, String) -> ToolResult
runTool "echo"  args = MkToolResult [MkText ("echo: " ++ argOr "q" "(empty)" args)] False
runTool "greet" args = MkToolResult [MkText ("Hello, " ++ argOr "name" "world" args ++ "!")] False
runTool nm      _    = MkToolResult [MkText ("unknown tool: " ++ nm)] True

readRes : List (String, String) -> String -> ResourceContents
readRes store uri = case assoc uri store of
                      Just txt => MkResource uri "text/plain" txt
                      Nothing  => MkResource uri "text/plain" "(resource not found)"

serve : Registry -> (m : Method) -> (ResultOf m, Registry)
serve reg (Initialize _)      = (MkInit "2025-06-18" (MkServerInfo "idris-mcp" "0.1.0") True, reg)
serve reg ListTools           = (reg.tools, reg)
serve reg (CallTool nm args)  = (runTool nm args, reg)
serve reg (ReadResource uri)  = (readRes reg.resources uri, reg)

-- -----------------------------------------------------------------------------
-- 5. The CLIENT -- a Moore machine, now literally a value of the real
--    Data.Container.Morphism.Definition.(=%>) type.
-- -----------------------------------------------------------------------------

public export
data Stage = SInit | SList | SCall | SRead | SHalt

public export
record CS where
  constructor MkCS
  stage : Stage
  notes : List String
  known : List Tool

firstName : List Tool -> String
firstName []        = "<none>"
firstName (t :: _)  = t.name

clientFwd : CS -> Method
clientFwd (MkCS SInit _ _) = Initialize "idris2-agent"
clientFwd (MkCS SList _ _) = ListTools
clientFwd (MkCS SCall _ k) = CallTool (firstName k) [("q", "hi"), ("name", "Idris2")]
clientFwd (MkCS SRead _ _) = ReadResource "mcp://greeting"
clientFwd (MkCS SHalt _ _) = ReadResource "mcp://greeting"

toolText : ToolResult -> String
toolText tr = go tr.content
  where go : List TextContent -> String
        go []        = ""
        go [c]       = c.text
        go (c :: cs) = c.text ++ " " ++ go cs

toolNames : List Tool -> String
toolNames []        = ""
toolNames [t]       = t.name
toolNames (t :: ts) = t.name ++ ", " ++ toolNames ts

clientBwd : (cs : CS) -> ResultOf (clientFwd cs) -> CS
clientBwd (MkCS SInit n k) r = MkCS SList (n ++ ["connected to " ++ r.serverInfo.name]) k
clientBwd (MkCS SList n k) r = MkCS SCall (n ++ ["discovered " ++ show (length r) ++ " tools"]) r
clientBwd (MkCS SCall n k) r = MkCS SRead (n ++ ["tool said: " ++ toolText r]) k
clientBwd (MkCS SRead n k) r = MkCS SHalt (n ++ ["resource: " ++ r.text]) k
clientBwd (MkCS SHalt n k) r = MkCS SHalt n k

||| The client, as a genuine value of the compendium's own container-morphism
||| type -- not a lookalike defined for this file.
client : (CS :- CS) =%> MCP
client = clientFwd <! clientBwd

-- --- NEGATIVE DEMO (uncomment to see the compiler reject it) ------------------
-- clientBwdBad : (cs : CS) -> ResultOf (clientFwd cs) -> CS
-- clientBwdBad (MkCS SList n k) r = MkCS SCall (n ++ [show r.isError]) k
-- Error: List Tool has no field isError -- exactly as in the toy version,
-- but now checked against the real library's (=%>) rather than a hand-rolled
-- stand-in.
-- ------------------------------------------------------------------------------

-- -----------------------------------------------------------------------------
-- 6. The closed loop
-- -----------------------------------------------------------------------------

render : (m : Method) -> ResultOf m -> String
render (Initialize cn) r =
  "initialize(\"" ++ cn ++ "\")  ->  " ++ r.serverInfo.name ++ " v" ++ r.serverInfo.version
    ++ "  [protocol " ++ r.protocolVersion ++ ", tools=" ++ show r.toolsCapability ++ "]"
render ListTools r =
  "tools/list  ->  " ++ show (length r) ++ " tools: " ++ toolNames r
render (CallTool nm _) r =
  "tools/call(\"" ++ nm ++ "\")  ->  " ++ toolText r ++ (if r.isError then "  [isError]" else "")
render (ReadResource uri) r =
  "resources/read(\"" ++ uri ++ "\")  ->  \"" ++ r.text ++ "\"  (" ++ r.mimeType ++ ")"

step : (CS, Registry) -> (String, (CS, Registry))
step (cs, reg) =
  let (res, reg') = serve reg (client.fwd cs)
  in (render (client.fwd cs) res, (client.bwd cs res, reg'))

runN : Nat -> (CS, Registry) -> List String
runN Z     _  = []
runN (S k) st = let (line, st') = step st in line :: runN k st'

-- -----------------------------------------------------------------------------
-- 7. A demo session
-- -----------------------------------------------------------------------------

exampleTools : List Tool
exampleTools =
  [ MkTool "echo"  "Echo the q argument back"
  , MkTool "greet" "Greet the name argument" ]

exampleResources : List (String, String)
exampleResources =
  [ ("mcp://greeting", "Welcome to the Idris2 MCP server.") ]

main : IO ()
main = do
  let reg = MkRegistry exampleTools exampleResources
  let cs0 = MkCS SInit [] []
  putStrLn "=== MCP session, driven through the real container-compendium (=%>) ==="
  traverse_ putStrLn (runN 4 (cs0, reg))
  putStrLn "=== done ==="
