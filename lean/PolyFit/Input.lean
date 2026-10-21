import Lean.Data.Json
import PolyFit.Types

/-!
# Reading and validating the request

A fit request is `{"points": [[i, j], ...], "n": n, "missing": [m, ...]}`, plus an
optional `"vertices": [[i, j], ...]` (evaluate mode). A describe request is
`{"command": "describe", "points": [[i, j], ...]}`. Checks run in this order, and the
first failure is reported:

1. the JSON's shape and value ranges (error 4),
2. `diam(P) > 0` (error 1),
3. no two cyclically consecutive missing edges, when `n ≥ 3` (error 2).
-/

namespace PolyFit

open Lean (Json)

private def malformed (why : String) : Except FitError α :=
  throw (.malformed why)

/-- Look up a field of a JSON object, reporting a missing field as malformed input. -/
private def field (obj : Json) (key : String) : Except FitError Json :=
  match obj.getObjVal? key with
  | .ok v    => pure v
  | .error _ => malformed s!"missing field \"{key}\""

/-- Read one `[i, j]` pair of integers. -/
def parseIntPair (v : Json) : Except FitError Pt :=
  match v.getArr? with
  | .ok #[a, b] =>
    match a.getInt?, b.getInt? with
    | .ok i, .ok j => pure ⟨i, j⟩
    | _, _ => malformed s!"coordinates must be integers, got {v.compress}"
  | _ => malformed s!"each point must be a pair [i, j], got {v.compress}"

/-- Read one input pixel: an `[i, j]` pair of non-negative integers. -/
def parsePt (v : Json) : Except FitError Pt := do
  let p ← parseIntPair v
  if p.i < 0 || p.j < 0 then malformed s!"negative coordinate in {v.compress}"
  return p

/-- Read evaluate mode's `"vertices"`: exactly `n` integer pairs. Negative coordinates
are allowed, since a polygon's vertices may lie outside the image. -/
def parseVertices (n : Nat) (v : Json) : Except FitError (Array Pt) := do
  let some arr := v.getArr?.toOption | malformed "\"vertices\" must be an array"
  if arr.size != n then malformed s!"\"vertices\" must have n = {n} entries, got {arr.size}"
  arr.mapM parseIntPair

/-- Read the array of points. It must be nonempty. -/
def parsePoints (v : Json) : Except FitError (Array Pt) := do
  let some arr := v.getArr?.toOption | malformed "\"points\" must be an array"
  if arr.isEmpty then malformed "\"points\" must not be empty"
  arr.mapM parsePt

/-- Read the polygon number `n ≥ 1`. -/
def parseN (v : Json) : Except FitError Nat :=
  match v.getNat? with
  | .ok n => if n ≥ 1 then pure n else malformed "n must be at least 1"
  | .error _ => malformed s!"n must be a non-negative integer, got {v.compress}"

/-- Read the missing edges for an `n`-gon with `n ≥ 3`: each must be in `[0, n - 1]`.
The result is sorted and duplicate-free. -/
def parseMissing (n : Nat) (v : Json) : Except FitError (List Nat) := do
  let some arr := v.getArr?.toOption | malformed "\"missing\" must be an array"
  let ms ← arr.toList.mapM fun m =>
    match m.getNat? with
    | .ok k => if k < n then pure k else malformed s!"missing edge {k} is not in [0, {n - 1}]"
    | .error _ => malformed s!"missing edges must be non-negative integers, got {m.compress}"
  return ms.eraseDups.mergeSort

/-- `diam(P) = 0` exactly when every point equals the first one. -/
def zeroDiameter (pts : Array Pt) : Bool :=
  pts.all (· == pts[0]!)

/-- Some missing edge `m` has its cyclic successor `(m + 1) % n` missing too. -/
def hasConsecutive (n : Nat) (missing : List Nat) : Bool :=
  missing.any fun m => missing.contains ((m + 1) % n)

/-- Parse and validate a fit (or evaluate) request. -/
def parseProblem (json : Json) : Except FitError Problem := do
  let points ← parsePoints (← field json "points")
  let n ← parseN (← field json "n")
  -- For a point or a segment the missing edges are ignored entirely.
  let missing ← if n ≤ 2 then pure [] else parseMissing n (← field json "missing")
  -- Evaluate mode, if the optional "vertices" field is present.
  let vertices ← match json.getObjVal? "vertices" with
    | .ok v    => some <$> parseVertices n v
    | .error _ => pure none
  if zeroDiameter points then throw .zeroDiameter
  if hasConsecutive n missing then throw .consecutiveMissing
  return { points, n, missing, vertices }

/-- Parse and validate the points of a `describe` request. -/
def parseDescribe (json : Json) : Except FitError (Array Pt) := do
  let points ← parsePoints (← field json "points")
  if zeroDiameter points then throw .zeroDiameter
  return points

/-- Parse a `reduce_hull` request: the points and `n ≥ 2`. -/
def parseReduceHull (json : Json) : Except FitError Request := do
  let points ← parseDescribe json
  let n ← parseN (← field json "n")
  if n < 2 then malformed "reduce_hull needs n ≥ 2"
  return .reduceHull points n

/-- Parse a `rough_fit` request: a fit problem with `n ≥ 2`, the candidate vertices
(distinct integer pairs, in cyclic order; negative coordinates allowed), and the number
`k ≥ 1` of best polygons to return (default 2). -/
def parseRoughFit (json : Json) : Except FitError Request := do
  let prob ← parseProblem json
  if prob.n < 2 then malformed "rough_fit needs n ≥ 2"
  let some arr := (← field json "candidates").getArr?.toOption | malformed "\"candidates\" must be an array"
  let cands ← arr.mapM parseIntPair
  if cands.toList.eraseDups.length != cands.size then malformed "the candidates must be distinct"
  let k ← match json.getObjVal? "k" with
    | .error _ => pure 2
    | .ok v => match v.getNat? with
      | .ok k => if k ≥ 1 then pure k else malformed "k must be at least 1"
      | .error _ => malformed s!"k must be a positive integer, got {v.compress}"
  return .roughFit prob cands k

/-- Parse a `fine_fit` request: a fit problem and the `n` vertices to start from. -/
def parseFineFit (json : Json) : Except FitError Request := do
  let prob ← parseProblem json
  return .fineFit prob (← parseVertices prob.n (← field json "start"))

/-- Parse and validate a whole request. The optional `"command"` field picks what to do;
without it the request is a fit (or an evaluation, if `"vertices"` is present). -/
def parseRequest (input : String) : Except FitError Request := do
  let json ← match Json.parse input with
    | .ok j    => pure j
    | .error e => malformed s!"invalid JSON: {e}"
  match json.getObjVal? "command" with
  | .error _ => .fit <$> parseProblem json
  | .ok cmd =>
    match cmd.getStr? with
    | .ok "fit"      => .fit <$> parseProblem json
    | .ok "describe" => .describe <$> parseDescribe json
    | .ok "reduce_hull" => parseReduceHull json
    | .ok "rough_fit" => parseRoughFit json
    | .ok "fine_fit" => parseFineFit json
    | .ok other      => malformed s!"unknown command \"{other}\""
    | .error _       => malformed s!"\"command\" must be a string, got {cmd.compress}"

end PolyFit
