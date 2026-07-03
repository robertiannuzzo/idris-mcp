||| The mechanics behind `check` and `prove`: a subprocess-based typecheck
||| oracle, and an LLM-calling helper used to propose candidates for it to
||| verify.
|||
||| Idris2's elaborator (TT terms, `%search`, etc.) is baked into the `idris2`
||| compiler binary itself -- it isn't a library a separately-compiled,
||| already-running program can call into. So "the typechecker is the
||| oracle" is realized here by spawning the real `idris2` compiler as a
||| subprocess per candidate and trusting only its verdict, the same way
||| Client.idr already spawns Server.idr's binary as a subprocess.
module MCP.Proof

import Data.List
import Data.String
import Language.JSON
import System
import System.Directory
import System.File
import System.File.Process
import System.Escape

%default covering

-- -----------------------------------------------------------------------------
-- Low-level primitives: the typecheck oracle and the LLM caller.
-- -----------------------------------------------------------------------------

||| Wrap a bare signature + term into a checkable module. Both are taken as
||| already-formed Idris2 source fragments (e.g. `plusComm : (n, m : Nat) ->
||| n + m = m + n` and `plusComm n m = ...`). The module name here
||| (`Candidate`) must match `checkModule`'s temp file name exactly --
||| Idris2 requires module name and file name to agree.
export
wrapCandidate : (signature : String) -> (term : String) -> String
wrapCandidate signature term =
  "module Candidate\n\n%default total\n\n" ++ signature ++ "\n" ++ term ++ "\n"

readAllLines : File -> IO String
readAllLines h = go []
  where
    go : List String -> IO String
    go acc = do
      eof <- fEOF h
      if eof
         then pure (fastConcat (reverse acc))
         else do
           Right line <- fGetLine h
             | Left _ => pure (fastConcat (reverse acc))
           go (line :: acc)

||| Write `src` to a fresh temp file and run `idris2 --check` on it.
||| Right () means it typechecks; Left carries the compiler's own diagnostic
||| text verbatim, so a caller (a human, or an LLM in a repair loop) sees
||| exactly what the typechecker said.
|||
||| Two real gotchas this works around: (1) on macOS, `/tmp` is a symlink to
||| `/private/tmp`, and Idris2's source-directory check compares paths
||| literally, so a file addressed via `/tmp/...` gets rejected as "not in
||| the source directory" once it's canonicalized -- `/private/tmp` avoids
||| that. (2) Idris2 requires the file name to match the module name inside
||| it, so each check gets its own directory containing a fixed
||| `Candidate.idr`, and the check runs from *inside* that directory so no
||| ambient `.ipkg` (like this project's own `server.ipkg`) gets picked up
||| and mismatched against it.
export
checkModule : (src : String) -> IO (Either String ())
checkModule src = do
  pid <- getPID
  let dir = "/private/tmp/idris-mcp-check-" ++ show pid
  _ <- createDir dir
  let path = dir ++ "/Candidate.idr"
  Right () <- writeFile path src
    | Left err => pure (Left ("could not write candidate file: " ++ show err))
  let cmd = escapeCmd ["sh", "-c", "cd " ++ escapeArg dir ++ " && idris2 --check Candidate.idr 2>&1"]
  Right h <- popen cmd Read
    | Left err => pure (Left ("could not spawn idris2: " ++ show err))
  out <- readAllLines h
  exitCode <- pclose h
  pure $ if exitCode == 0 then Right () else Left out

||| Call the Anthropic Messages API with a system prompt and one user
||| message, returning the assistant's first text block. Requires
||| ANTHROPIC_API_KEY in the environment -- this is a separate, billed API
||| key, not the Claude Pro/Claude Code subscription.
|||
||| Headers (including the key) go through a curl config file rather than
||| command-line flags, so the key doesn't appear in process listings.
export
callLLM : (systemPrompt : String) -> (userMessage : String) -> IO (Either String String)
callLLM sys user = do
  Just apiKey <- getEnv "ANTHROPIC_API_KEY"
    | Nothing => pure (Left "ANTHROPIC_API_KEY is not set")
  pid <- getPID
  let bodyPath = "/private/tmp/idris-mcp-llm-body-" ++ show pid ++ ".json"
  let cfgPath  = "/private/tmp/idris-mcp-llm-cfg-"  ++ show pid ++ ".curl"
  let body = JObject
        [ ("model", JString "claude-sonnet-5")
        , ("max_tokens", JNumber 1024)
        , ("system", JString sys)
        , ("messages", JArray
            [ JObject [("role", JString "user"), ("content", JString user)] ])
        ]
  Right () <- writeFile bodyPath (show body)
    | Left err => pure (Left ("could not write request body: " ++ show err))
  let cfg = unlines
        [ "silent"
        , "header = \"content-type: application/json\""
        , "header = \"anthropic-version: 2023-06-01\""
        , "header = \"x-api-key: " ++ apiKey ++ "\""
        , "data = @" ++ bodyPath
        , "url = \"https://api.anthropic.com/v1/messages\""
        ]
  Right () <- writeFile cfgPath cfg
    | Left err => pure (Left ("could not write curl config: " ++ show err))
  let cmd = escapeCmd ["curl", "-K", cfgPath]
  Right h <- popen cmd Read
    | Left err => pure (Left ("could not spawn curl: " ++ show err))
  out <- readAllLines h
  _ <- pclose h
  pure $ case parse out of
              Nothing => Left ("could not parse API response as JSON: " ++ out)
              Just json => case extractText json of
                                Nothing  => Left ("unexpected API response shape: " ++ out)
                                Just txt => Right txt
  where
    firstTextBlock : List JSON -> Maybe String
    firstTextBlock [] = Nothing
    firstTextBlock (JObject fields :: rest) =
      case (lookup "type" (JObject fields), lookup "text" (JObject fields)) of
           (Just (JString "text"), Just (JString t)) => Just t
           _ => firstTextBlock rest
    firstTextBlock (_ :: rest) = firstTextBlock rest

    extractText : JSON -> Maybe String
    extractText json = do
      JArray blocks <- lookup "content" json
        | _ => Nothing
      firstTextBlock blocks

-- -----------------------------------------------------------------------------
-- ProofResult, and the two methods built on the primitives above.
-- -----------------------------------------------------------------------------

||| Evidence-carrying outcome of `check`/`prove` -- never a bare Bool, so a
||| caller always gets to see either the accepted term or exactly why
||| nothing was accepted.
|||
||| `Refuted` is reserved for a *specific submitted candidate* failing to
||| typecheck against a goal (what `check` reports on failure) -- it is
||| never emitted by `prove`'s repair loop just because the loop ran out of
||| attempts. Absence of a proof is not evidence of falsity; that's
||| `Unknown`, not `Refuted`. Nothing in this module has a genuine
||| refutation procedure (no decision procedures, no counterexample
||| search), so `Refuted` only ever means "this one candidate is wrong",
||| never "the goal is false".
public export
data ProofResult : Type where
  Checked  : (signature : String) -> (term : String) -> (paraphrase : String) -> ProofResult
  Refuted  : (signature : String) -> (term : String) -> (reason : String) -> ProofResult
  Unknown  : (goal : String) -> (attempts : List (String, String)) -> ProofResult
  ParseErr : (diagnostic : String) -> ProofResult

||| Wire encoding for `ProofResult`. Tagged by `outcome` so a client can
||| dispatch on it without needing to know Idris2's constructor names.
export
proofResultToJSON : ProofResult -> JSON
proofResultToJSON (Checked sig trm para) = JObject
  [ ("outcome", JString "checked")
  , ("signature", JString sig)
  , ("term", JString trm)
  , ("paraphrase", JString para)
  ]
proofResultToJSON (Refuted sig trm reason) = JObject
  [ ("outcome", JString "refuted")
  , ("signature", JString sig)
  , ("term", JString trm)
  , ("reason", JString reason)
  ]
proofResultToJSON (Unknown goal attempts) = JObject
  [ ("outcome", JString "unknown")
  , ("goal", JString goal)
  , ("attempts", JArray (map attemptToJSON attempts))
  ]
  where
    attemptToJSON : (String, String) -> JSON
    attemptToJSON (candidate, err) = JObject
      [ ("candidate", JString candidate), ("error", JString err) ]
proofResultToJSON (ParseErr diagnostic) = JObject
  [ ("outcome", JString "parse_error")
  , ("diagnostic", JString diagnostic)
  ]

||| `check`: verify a specific, caller-supplied signature+term pair. No LLM
||| involved at all -- pure subprocess-oracle path.
export
checkTerm : (signature : String) -> (term : String) -> IO ProofResult
checkTerm signature term = do
  result <- checkModule (wrapCandidate signature term)
  pure $ case result of
              Right () => Checked signature term ""
              Left err => Refuted signature term err

-- NOTE: `prefix` is a reserved keyword in Idris2 (fixity declarations, e.g.
-- `prefix 5 !`), so it can't be used as a parameter name here -- using it
-- broke parsing with an opaque "Couldn't parse declaration" error pointing
-- at the *next* line. Renamed to `pfx` throughout.
stripPrefixLocal : String -> String -> Maybe String
stripPrefixLocal pfx s =
  let p = unpack pfx
      cs = unpack s
  in if isPrefixOf p cs
        then Just (pack (drop (length p) cs))
        else Nothing

||| Parse the LLM's reply into (signature, term, paraphrase). The system
||| prompt asks for exactly three prefixed lines; this just looks for each
||| prefix anywhere in the reply, tolerating extra surrounding text.
parseLLMReply : String -> Maybe (String, String, String)
parseLLMReply text =
  let ls = lines text
  in case (findPrefixed "SIGNATURE:" ls, findPrefixed "TERM:" ls, findPrefixed "PARAPHRASE:" ls) of
          (Just s, Just t, Just p) => Just (s, t, p)
          _ => Nothing
  where
    findPrefixed : String -> List String -> Maybe String
    findPrefixed pfx [] = Nothing
    findPrefixed pfx (l :: ls) =
      case stripPrefixLocal pfx (trim l) of
           Just rest => Just (trim rest)
           Nothing   => findPrefixed pfx ls

||| `prove`: translate an English prompt into a signature+term via the LLM,
||| verify it against the real typechecker, and on failure feed the
||| checker's own diagnostic back to the LLM for another attempt, capped at
||| `maxRetries`. The typechecker is the only thing that ever turns a
||| candidate into `Checked` -- the LLM only ever *proposes*.
export
proveGoal : (prompt : String) -> IO ProofResult
proveGoal prompt = go maxRetries Nothing []
  where
    maxRetries : Nat
    maxRetries = 3

    systemPrompt : String
    systemPrompt = unlines
      [ "You translate an English request for a mathematical lemma into a single"
      , "Idris2 type signature and a term that proves it. Respond with EXACTLY"
      , "three lines, no other text before or after:"
      , "SIGNATURE: <a top-level Idris2 type signature, name the goal 'goal'>"
      , "TERM: <'goal = ' followed by a term or tactic script proving it>"
      , "PARAPHRASE: <one plain English sentence restating what SIGNATURE says>"
      ]

    userMessage : Maybe (String, String, String) -> String
    userMessage Nothing = "Prompt: " ++ prompt
    userMessage (Just (sig, trm, err)) = unlines
      [ "Prompt: " ++ prompt
      , ""
      , "Your previous attempt did not typecheck."
      , "SIGNATURE: " ++ sig
      , "TERM: " ++ trm
      , "Idris2 said:"
      , err
      , ""
      , "Try again -- correct the TERM (or the SIGNATURE, if it was the wrong lemma)."
      ]

    go : Nat -> Maybe (String, String, String) -> List (String, String) -> IO ProofResult
    go Z _ attempts = pure (Unknown prompt attempts)
    go (S k) prior attempts = do
      Right reply <- callLLM systemPrompt (userMessage prior)
        | Left err => pure (ParseErr ("LLM call failed: " ++ err))
      case parseLLMReply reply of
           Nothing => pure (ParseErr ("could not parse LLM reply into SIGNATURE/TERM/PARAPHRASE:\n" ++ reply))
           Just (sig, trm, para) => do
             result <- checkModule (wrapCandidate sig trm)
             case result of
                  Right () => pure (Checked sig trm para)
                  Left err => go k (Just (sig, trm, err)) (attempts ++ [(sig ++ "\n" ++ trm, err)])
