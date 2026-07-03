||| The MCP method/result surface as a real container (Ghani/Abbott/Altenkirch
||| sense), built on the container-compendium library rather than plain JSON
||| records. `Method` is the container's shape; `ResultOf` is its
||| (dependent) response family.
|||
||| Decoding a request becomes "produce a `Method` value" -- if the JSON
||| doesn't determine one, there is no valid position, and the request is
||| rejected before any handler runs. Dispatch and response-encoding are then
||| *exhaustive dependent functions* over `Method`: the compiler checks every
||| method is handled and that each handler's result has the type `ResultOf`
||| says it must -- see `dispatch` and `encodeResult` below.
module MCP.Container

import Data.Maybe
import Language.JSON

import Data.Container.Definition

import MCP.Types
import MCP.Proof

-- Prove/Check dispatch through subprocess calls (the idris2 typechecker,
-- and curl for the LLM), so dispatch can no longer be total/pure -- it's a
-- necessary, expected consequence of adding methods that verify things
-- rather than just returning fixed data.
%default covering

||| The methods this server accepts. Each carries exactly the data a
||| handler needs to decide the response -- this is the container's shape.
public export
data Method : Type where
  Initialize : (protocolVersion : String) -> Method
  ListTools  : Method
  CallTool   : (name : String) -> (arguments : Maybe JSON) -> Method
  ||| Verify a specific, caller-supplied signature+term pair against the
  ||| real Idris2 typechecker. No LLM involved.
  Check      : (signature : String) -> (term : String) -> Method
  ||| Translate an English prompt into a signature+term via an LLM, and
  ||| verify the result the same way `Check` does -- the LLM only ever
  ||| proposes, the typechecker is the sole oracle for what comes back.
  Prove      : (prompt : String) -> Method

||| The response type, indexed by which method was sent. This dependency is
||| what makes an ill-typed method/result pairing unrepresentable.
public export
ResultOf : Method -> Type
ResultOf (Initialize _) = InitializeResult
ResultOf ListTools       = List Tool
ResultOf (CallTool _ _)  = CallToolResult
ResultOf (Check _ _)     = ProofResult
ResultOf (Prove _)       = ProofResult

||| The MCP interface as a container: shapes = Method, positions = ResultOf.
public export
MCP : Container
MCP = (m : Method) !> ResultOf m

||| Every tool this server exposes. Extending this list is the only change
||| needed to add a tool to `tools/list`; `dispatch` below still has to
||| handle it exhaustively.
export
tools : List Tool
tools = [helloTool]
  where
    helloTool : Tool
    helloTool = MkTool "hello" "Say hello. Optional 'name' argument." schema
      where
        schema : JSON
        schema = JObject
          [ ("type", JString "object")
          , ("properties", JObject
              [ ("name", JObject
                  [ ("type", JString "string")
                  , ("description", JString "Name to greet")
                  ])
              ])
          ]

callHello : Maybe JSON -> CallToolResult
callHello args =
  let name = case args >>= lookup "name" of
                  Just (JString n) => n
                  _                => "world"
  in MkCallToolResult [TextContent ("Hello, " ++ name ++ "! (from Idris2 MCP server)")] False

||| The server as a section of the container: an exhaustive function from a
||| method to a value of *that method's own* result type. Forgetting a
||| case, or returning the wrong shape for one, is a compile error.
|||
||| No longer pure -- Check/Prove verify things via a spawned `idris2`
||| subprocess (and Prove calls out to an LLM first), both of which are IO.
export
dispatch : (m : Method) -> IO (ResultOf m)
dispatch (Initialize pv) = pure (MkInitializeResult pv (MkImplementation "idris-mcp-server" "0.1.0"))
dispatch ListTools       = pure tools
dispatch (CallTool "hello" args) = pure (callHello args)
dispatch (CallTool nm _)         = pure (MkCallToolResult [TextContent ("unknown tool: " ++ nm)] True)
dispatch (Check signature term)  = checkTerm signature term
dispatch (Prove prompt)          = proveGoal prompt

||| The dependent inverse of `dispatch`'s result: turn a method's typed
||| result back into wire JSON. Also exhaustive over `Method`.
export
encodeResult : (m : Method) -> ResultOf m -> JSON
encodeResult (Initialize _) r = initializeResultToJSON r
encodeResult ListTools      r = toolsListResultToJSON r
encodeResult (CallTool _ _) r = callToolResultToJSON r
encodeResult (Check _ _)    r = proofResultToJSON r
encodeResult (Prove _)      r = proofResultToJSON r

||| What decoding a request can produce: a well-formed `Method` (a position
||| in the container's shape), or one of two ways it can fail to be one.
||| Kept separate from `Method` itself so "no such method" and "method
||| known, params malformed" get distinct JSON-RPC error codes.
public export
data Decoded : Type where
  Ok          : Method -> Decoded
  UnknownMethod : Decoded
  BadParams   : Decoded

export
decodeRequest : String -> Maybe JSON -> Decoded
decodeRequest "initialize" params =
  Ok (Initialize (fromMaybe mcpProtocolVersion (params >>= lookup "protocolVersion" >>= asString)))
  where
    asString : JSON -> Maybe String
    asString (JString s) = Just s
    asString _            = Nothing
decodeRequest "tools/list" _ = Ok ListTools
decodeRequest "tools/call" params =
  case params >>= lookup "name" of
       Just (JString nm) => Ok (CallTool nm (params >>= lookup "arguments"))
       _                 => BadParams
decodeRequest "check" params =
  case (params >>= lookup "signature", params >>= lookup "term") of
       (Just (JString sig), Just (JString trm)) => Ok (Check sig trm)
       _                                        => BadParams
decodeRequest "prove" params =
  case params >>= lookup "prompt" of
       Just (JString p) => Ok (Prove p)
       _                => BadParams
decodeRequest _ _ = UnknownMethod
