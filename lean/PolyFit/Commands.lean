import PolyFit.Hull
import PolyFit.Rough
import PolyFit.Solve
import PolyFit.Output

/-!
# Carrying out a request

Each request is one command; `respond` runs it and builds the JSON reply.
-/

namespace PolyFit

open Lean (Json toJson)

/-- `{"error": 0, "poly_points": ..., "objective_function": [a, b], "moves": m, "certified": b}`. -/
def renderFineFit (r : Polished) : Json :=
  Json.mkObj [
    ("error", toJson (0 : Nat)),
    ("poly_points", ptsJson r.vertices),
    ("objective_function", ratJson r.objectiveSq),
    ("moves", toJson r.moves),
    ("certified", toJson r.certified)]

def respond : Request → Except FitError Json
  | .describe pts => pure (renderDescription (describe pts))
  | .fit prob     => renderFit <$> answer prob
  | .reduceHull pts n => renderCandidates <$> reduceHull pts n
  | .roughFit prob cands k =>
    (fun best => renderRoughFits (best.map fun s => (s.vertices, s.objectiveSq))) <$>
      roughFit prob.points prob.n prob.missing cands k
  | .fineFit prob start => renderFineFit <$> fineFit prob start

end PolyFit
