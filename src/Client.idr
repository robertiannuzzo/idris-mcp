||| Phase 0 MCP client: spawns a server as a subprocess and drives the
||| handshake, tools/list, and one tools/call over stdio pipes.
module Client

import Language.JSON
import System
import System.File
import System.File.Process

import JSONRPC
import MCP.Types
import MCP.Transport

%default covering

sendRequest : SubProcess -> RpcId -> String -> Maybe JSON -> IO ()
sendRequest sp id method params = writeLine sp.input (encodeLine (MkRequest id method params))

sendNotification : SubProcess -> String -> Maybe JSON -> IO ()
sendNotification sp method params = writeLine sp.input (encodeLine (MkNotification method params))

||| Read lines from the server until one parses as a JSON-RPC message,
||| skipping anything on stdout that isn't (a misbehaving server writing
||| logs to stdout, say). Dies if the pipe closes first.
readMessage : SubProcess -> IO Message
readMessage sp = do
  Just line <- readLine sp.output
    | Nothing => die "server closed its output before responding"
  case decodeLine line of
       Just msg => pure msg
       Nothing  => do
         logErr ("client: skipping unparseable line: " ++ line)
         readMessage sp

expectResult : Message -> IO JSON
expectResult (MkResponse _ result) = pure result
expectResult (MkErrorResp _ err)   = die ("server returned error: " ++ err.message)
expectResult _                     = die "expected a response, got a request/notification"

clientInfoJSON : JSON
clientInfoJSON = JObject
  [ ("protocolVersion", JString mcpProtocolVersion)
  , ("capabilities", JObject [])
  , ("clientInfo", JObject [ ("name", JString "idris-mcp-client"), ("version", JString "0.1.0") ])
  ]

callToolParamsJSON : String -> List (String, JSON) -> JSON
callToolParamsJSON name args = JObject
  [ ("name", JString name)
  , ("arguments", JObject args)
  ]

main : IO ()
main = do
  args <- getArgs
  let serverCmd = case args of
                       (_ :: path :: _) => path
                       _                => "./build/exec/server"

  Right sp <- popen2 [serverCmd]
    | Left err => die ("failed to spawn server '" ++ serverCmd ++ "': " ++ show err)

  putStrLn ("client: spawned server: " ++ serverCmd)

  sendRequest sp (IdInt 1) "initialize" (Just clientInfoJSON)
  initResult <- readMessage sp >>= expectResult
  putStrLn ("client: initialize -> " ++ show initResult)

  sendNotification sp "notifications/initialized" Nothing

  sendRequest sp (IdInt 2) "tools/list" Nothing
  toolsResult <- readMessage sp >>= expectResult
  putStrLn ("client: tools/list -> " ++ show toolsResult)

  sendRequest sp (IdInt 3) "tools/call" (Just (callToolParamsJSON "hello" [("name", JString "Idris2")]))
  callResult <- readMessage sp >>= expectResult
  putStrLn ("client: tools/call hello -> " ++ show callResult)

  -- Close stdin so the server sees EOF and its read loop exits, then wait for it.
  closeFile sp.input
  exitCode <- popen2Wait sp
  putStrLn ("client: server exited with code " ++ show exitCode)
