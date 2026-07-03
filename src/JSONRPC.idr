||| JSON-RPC 2.0 message envelope: encode/decode, independent of MCP.
||| https://www.jsonrpc.org/specification
module JSONRPC

import Data.List
import Language.JSON

%default total

||| A JSON-RPC id is a string or a number (we don't support fractional ids).
public export
data RpcId : Type where
  IdStr : String -> RpcId
  IdInt : Integer -> RpcId

export
Eq RpcId where
  IdStr a == IdStr b = a == b
  IdInt a == IdInt b = a == b
  _ == _ = False

export
Show RpcId where
  show (IdStr s) = s
  show (IdInt i) = show i

export
idToJSON : RpcId -> JSON
idToJSON (IdStr s) = JString s
idToJSON (IdInt i) = JNumber (cast i)

export
idFromJSON : JSON -> Maybe RpcId
idFromJSON (JString s) = Just (IdStr s)
idFromJSON (JNumber n) = Just (IdInt (cast n))
idFromJSON _ = Nothing

public export
record RpcError where
  constructor MkRpcError
  code    : Int
  message : String
  errData : Maybe JSON

||| Standard JSON-RPC 2.0 error codes.
namespace ErrorCode
  public export
  parseError : Int
  parseError = -32700

  public export
  invalidRequest : Int
  invalidRequest = -32600

  public export
  methodNotFound : Int
  methodNotFound = -32601

  public export
  invalidParams : Int
  invalidParams = -32602

  public export
  internalError : Int
  internalError = -32603

export
mkError : Int -> String -> RpcError
mkError c m = MkRpcError c m Nothing

export
errorToJSON : RpcError -> JSON
errorToJSON e = JObject $
  [ ("code", JNumber (cast e.code))
  , ("message", JString e.message)
  ] ++ maybe [] (\d => [("data", d)]) e.errData

||| One JSON-RPC message: a call expecting a response, a fire-and-forget
||| notification, a successful response, or an error response.
public export
data Message : Type where
  MkRequest      : RpcId -> String -> Maybe JSON -> Message
  MkNotification : String -> Maybe JSON -> Message
  MkResponse     : RpcId -> JSON -> Message
  MkErrorResp    : Maybe RpcId -> RpcError -> Message

export
encode : Message -> JSON
encode (MkRequest id method params) = JObject $
  [ ("jsonrpc", JString "2.0")
  , ("id", idToJSON id)
  , ("method", JString method)
  ] ++ maybe [] (\p => [("params", p)]) params
encode (MkNotification method params) = JObject $
  [ ("jsonrpc", JString "2.0")
  , ("method", JString method)
  ] ++ maybe [] (\p => [("params", p)]) params
encode (MkResponse id result) = JObject
  [ ("jsonrpc", JString "2.0")
  , ("id", idToJSON id)
  , ("result", result)
  ]
encode (MkErrorResp id err) = JObject
  [ ("jsonrpc", JString "2.0")
  , ("id", maybe JNull idToJSON id)
  , ("error", errorToJSON err)
  ]

||| Language.JSON's `Show` always prints `JNumber` with a trailing
||| decimal point (`1` becomes `"1.0"`), since it's backed by `Double`.
||| That's a legal JSON-RPC id, but many hosts compare ids somewhat
||| strictly, so we render whole numbers without the decimal point.
renderNumber : Double -> String
renderNumber d =
  let n = the Integer (cast d)
  in if cast n == d then show n else show d

||| Compact JSON rendering, like `Language.JSON`'s `Show`, but with
||| `renderNumber` for `JNumber`. Exported because anything that sends
||| JSON with whole-number fields to a strict peer needs it -- the
||| Anthropic API, for one, rejects `"max_tokens": 1024.0`.
export
render : JSON -> String
render JNull = "null"
render (JBoolean x) = if x then "true" else "false"
render (JNumber x) = renderNumber x
render (JString x) = show (JString x)
render (JArray xs) = "[" ++ renderValues xs ++ "]"
  where
    renderValues : List JSON -> String
    renderValues [] = ""
    renderValues (x :: xs) = render x ++ if isNil xs then "" else "," ++ renderValues xs
render (JObject xs) = "{" ++ renderProps xs ++ "}"
  where
    renderProp : (String, JSON) -> String
    renderProp (key, value) = show (JString key) ++ ":" ++ render value

    renderProps : List (String, JSON) -> String
    renderProps [] = ""
    renderProps (x :: xs) = renderProp x ++ if isNil xs then "" else "," ++ renderProps xs

||| Serialize a message as a single line with no embedded newlines,
||| as required by the MCP stdio transport.
export
encodeLine : Message -> String
encodeLine = render . encode

decodeError : List (String, JSON) -> Maybe RpcError
decodeError fields = do
  JNumber n  <- lookup "code" (JObject fields)    | _ => Nothing
  JString m  <- lookup "message" (JObject fields) | _ => Nothing
  let d = lookup "data" (JObject fields)
  pure (MkRpcError (cast n) m d)

export
decode : JSON -> Maybe Message
decode (JObject fields) =
  let mid     = lookup "id" (JObject fields)
      mmethod = lookup "method" (JObject fields)
      mparams = lookup "params" (JObject fields)
  in case mmethod of
       Just (JString method) =>
         case mid of
           Just idJson => idFromJSON idJson >>= \id => pure (MkRequest id method mparams)
           Nothing     => pure (MkNotification method mparams)
       _ =>
         case lookup "error" (JObject fields) of
           Just (JObject errFields) => do
             err <- decodeError errFields
             let eid = mid >>= idFromJSON
             pure (MkErrorResp eid err)
           _ => do
             idJson <- mid
             id     <- idFromJSON idJson
             result <- lookup "result" (JObject fields)
             pure (MkResponse id result)
decode _ = Nothing

export
decodeLine : String -> Maybe Message
decodeLine s = parse s >>= decode
