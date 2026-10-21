import Lean.Data.Json
import PolyFit.Types

/-!
# Writing the reply

Fit:      `{"error": 0, "objective_function": [a, b], "poly_points": [[i, j], ...]}`,
          where `F² = a / b`.
Describe: `{"error": 0, "com": [[a, b], [c, d]], "diam_sq": N,
            "inner_radius_sq": [a, b], "outer_radius_sq": [a, b], "hull": [[i, j], ...]}`.
Failure:  `{"error": code, "objective_function": null, "poly_points": null}`.

Every fraction `a / b` is sent as the pair `[a, b]` in lowest terms.
-/

namespace PolyFit

open Lean (Json toJson)

/-- A fraction as the JSON pair `[num, den]`. -/
def ratJson (r : Rat) : Json :=
  toJson #[r.num, (r.den : Int)]

/-- Points as `[[i, j], ...]`. -/
def ptsJson (pts : Array Pt) : Json :=
  toJson (pts.map fun p => #[p.i, p.j])

def renderError (e : FitError) : Json :=
  Json.mkObj [("error", toJson e.code), ("objective_function", Json.null), ("poly_points", Json.null)]

def renderFit (fit : Fit) : Json :=
  Json.mkObj [
    ("error", toJson (0 : Nat)),
    ("objective_function", ratJson fit.objectiveSq),
    ("poly_points", ptsJson fit.vertices)]

def renderDescription (d : Description) : Json :=
  Json.mkObj [
    ("error", toJson (0 : Nat)),
    ("com", Json.arr #[ratJson d.com.1, ratJson d.com.2]),
    ("diam_sq", toJson d.diamSq),
    ("inner_radius_sq", ratJson d.innerRadiusSq),
    ("outer_radius_sq", ratJson d.outerRadiusSq),
    ("hull", ptsJson d.hull)]

/-- `{"error": 0, "candidates": [[i, j], ...]}`. -/
def renderCandidates (cands : Array Pt) : Json :=
  Json.mkObj [("error", toJson (0 : Nat)), ("candidates", ptsJson cands)]

/-- `{"error": 0, "rough_fits": [{"poly_points": ..., "objective_function": [a, b]}, ...]}`,
best first. -/
def renderRoughFits (fits : Array (Array Pt × Rat)) : Json :=
  Json.mkObj [
    ("error", toJson (0 : Nat)),
    ("rough_fits", Json.arr (fits.map fun (vs, f2) =>
      Json.mkObj [("poly_points", ptsJson vs), ("objective_function", ratJson f2)]))]

/-- The reply for any request: its JSON on success, the error JSON on failure. -/
def renderReply : Except FitError Json → Json
  | .ok json => json
  | .error e => renderError e

end PolyFit
