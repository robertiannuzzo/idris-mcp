||| MCP stdio transport: newline-delimited JSON, one message per line.
||| stdout carries protocol messages only; stderr is for diagnostics.
module MCP.Transport

import System.File
import Data.String

||| Read one line from a handle, stripping the trailing newline.
||| Returns Nothing at EOF.
export
covering
readLine : (h : File) -> IO (Maybe String)
readLine h = do
  eof <- fEOF h
  if eof
     then pure Nothing
     else do
       Right line <- fGetLine h
         | Left _ => pure Nothing
       pure (Just (trim line))

||| Write one line to a handle and flush immediately, so the peer sees
||| it without waiting for a buffer to fill.
export
writeLine : (h : File) -> String -> IO ()
writeLine h s = do
  _ <- fPutStrLn h s
  _ <- fflush h
  pure ()

||| Log a diagnostic line to stderr. Never write anything but protocol
||| messages to stdout.
export
logErr : String -> IO ()
logErr s = writeLine stderr s

||| Read lines from `h` until EOF, calling `handle` on each non-blank one.
export
covering
loop : (h : File) -> (String -> IO ()) -> IO ()
loop h handle = do
  Just line <- readLine h
    | Nothing => pure ()
  if line == ""
     then loop h handle
     else handle line *> loop h handle
