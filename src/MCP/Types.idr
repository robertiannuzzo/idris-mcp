||| Wire-format records for initialize/tools-list/tools-call results, and
||| their JSON encoders. MCP.Container is the typed layer on top: it decides
||| which of these a given method produces (via `ResultOf`) and dispatches
||| to it; this module just knows how to turn each one into JSON.
module MCP.Types

import Language.JSON

%default total

public export
mcpProtocolVersion : String
mcpProtocolVersion = "2025-06-18"

public export
record Implementation where
  constructor MkImplementation
  name    : String
  version : String

export
implementationToJSON : Implementation -> JSON
implementationToJSON impl = JObject
  [ ("name", JString impl.name)
  , ("version", JString impl.version)
  ]

public export
record InitializeResult where
  constructor MkInitializeResult
  protocolVersion : String
  serverInfo      : Implementation

export
initializeResultToJSON : InitializeResult -> JSON
initializeResultToJSON r = JObject
  [ ("protocolVersion", JString r.protocolVersion)
  , ("capabilities", JObject [ ("tools", JObject []) ])
  , ("serverInfo", implementationToJSON r.serverInfo)
  ]

||| A tool's advertised shape. `inputSchema` is a JSON Schema object,
||| kept opaque in Phase 0.
public export
record Tool where
  constructor MkTool
  name        : String
  description : String
  inputSchema : JSON

export
toolToJSON : Tool -> JSON
toolToJSON t = JObject
  [ ("name", JString t.name)
  , ("description", JString t.description)
  , ("inputSchema", t.inputSchema)
  ]

export
toolsListResultToJSON : List Tool -> JSON
toolsListResultToJSON tools = JObject
  [ ("tools", JArray (map toolToJSON tools)) ]

||| A single piece of tool-call output content. Phase 0 only needs text.
public export
data Content : Type where
  TextContent : String -> Content

export
contentToJSON : Content -> JSON
contentToJSON (TextContent s) = JObject
  [ ("type", JString "text")
  , ("text", JString s)
  ]

public export
record CallToolResult where
  constructor MkCallToolResult
  content : List Content
  isError : Bool

export
callToolResultToJSON : CallToolResult -> JSON
callToolResultToJSON r = JObject
  [ ("content", JArray (map contentToJSON r.content))
  , ("isError", JBoolean r.isError)
  ]
