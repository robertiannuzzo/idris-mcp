||| Phase 1 MCP server: same "hello" tool as Phase 0, but request handling
||| now goes through MCP.Container's typed Method/ResultOf container instead
||| of ad hoc per-method JSON parsing. See MCP.Container for the dispatch
||| and encoding logic; this module is just the JSON-RPC/stdio plumbing
||| around it.
module Server

import Language.JSON
import System.File

import JSONRPC
import MCP.Types
import MCP.Container
import MCP.Transport

%default covering

sendResult : RpcId -> JSON -> IO ()
sendResult id result = writeLine stdout (encodeLine (MkResponse id result))

sendError : RpcId -> RpcError -> IO ()
sendError id err = writeLine stdout (encodeLine (MkErrorResp (Just id) err))

handleRequest : RpcId -> String -> Maybe JSON -> IO ()
handleRequest id method params =
  case decodeRequest method params of
       UnknownMethod => sendError id (mkError methodNotFound ("unknown method: " ++ method))
       BadParams     => sendError id (mkError invalidParams (method ++ ": missing or malformed params"))
       Ok m          => do
         result <- dispatch m
         sendResult id (encodeResult m result)

handleMessage : Message -> IO ()
handleMessage (MkRequest id method params) = handleRequest id method params
handleMessage (MkNotification method _)    = logErr ("notification: " ++ method)
handleMessage (MkResponse _ _)             = logErr "unexpected response received by server"
handleMessage (MkErrorResp _ _)            = logErr "unexpected error response received by server"

handleLine : String -> IO ()
handleLine line =
  case decodeLine line of
       Nothing  => logErr ("could not parse message: " ++ line)
       Just msg => handleMessage msg

main : IO ()
main = do
  logErr "idris-mcp-server starting"
  loop stdin handleLine
  logErr "idris-mcp-server exiting (stdin closed)"
