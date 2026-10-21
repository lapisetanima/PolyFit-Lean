import PolyFit

/-- Read one JSON request from stdin and write one JSON reply to stdout.
On failure, a human-readable explanation also goes to stderr. -/
def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd                       -- read and parse the JSON from stdin
  let result := PolyFit.parseRequest input >>= PolyFit.respond -- see if JSON parameters make sense. If so, bind parameters to PolyFit.respond
  if let .error e := result then
    IO.eprintln s!"polyfit error {e.code}: {e.message}"
  IO.println (PolyFit.renderReply result).compress            -- build the return JSON (error or no error) and send to stdout
