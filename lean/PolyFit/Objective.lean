import PolyFit.Geometry
import PolyFit.Envelope

/-!
# The objective function, computed exactly

Every quantity is a `Rat` (an exact fraction). See `docs/spec.md` for the definitions.
`diam2` is `diam(P)²`, computed once by the caller and passed in, since the search
evaluates the objective many times for the same `P`. Everything here requires `P`
nonempty with `diam(P) > 0`, which `parseProblem` guarantees.
-/

namespace PolyFit

/-- `Σ_{p ∈ P} f p`. -/
def sumOver (pts : Array Pt) (f : Pt → Rat) : Rat :=
  pts.foldl (init := 0) fun s p => s + f p

/-- `D₁(P, {q})² = (1 / diam(P)²) · mean_{p ∈ P} d(p, q)²`. -/
def d1SqToPoint (pts : Array Pt) (diam2 : Nat) (q : Pt) : Rat :=
  sumOver pts (distSq · q) / (pts.size * diam2 : Nat)

/-- `D₁(P, ℓ)² = (1 / diam(P)²) · mean_{p ∈ P} d₁(p, ℓ)²` for the segment `ℓ = q₀q₁`. -/
def d1SqToSegment (pts : Array Pt) (diam2 : Nat) (q₀ q₁ : Pt) : Rat :=
  sumOver pts (distSqToSegment · q₀ q₁) / (pts.size * diam2 : Nat)

/-- `∫₀¹ d₁(q₀ + t v, P)² dt` with `v = q₁ - q₀`. For each `p`, with `u = q₀ - p`,
`|q₀ + t v - p|² = L² t² + 2 (u · v) t + |u|²`. The `t²` coefficient `L²` is the same
for every `p`, so the minimum over `p` is `L² t²` plus the lower envelope of the lines
`2 (u · v) t + |u|²`, and `∫₀¹ L² t² dt = L² / 3`. -/
def segmentIntegral (pts : Array Pt) (q₀ q₁ : Pt) : Rat :=
  let v := q₁ - q₀
  let lines := pts.map fun p => let u := q₀ - p; (⟨2 * dot u v, dot u u⟩ : Line)
  (dot v v : Rat) / 3 + lowerEnvelopeIntegral lines

/-- `D₂(ℓ, P)² = (1 / L²) ∫₀¹ d₁(q₀ + t v, P)² dt`, with `L² := 1` when `L = 0`
(the safety value used during the search). -/
def d2Sq (pts : Array Pt) (q₀ q₁ : Pt) : Rat :=
  let lenSq := dot (q₁ - q₀) (q₁ - q₀)
  segmentIntegral pts q₀ q₁ / (if lenSq == 0 then 1 else lenSq : Int)

/-- The objective function for `n = 1`: `F(q₀)² = D₁(P, {q₀})²`, the mean of `d(p, q₀)²`
over the points `p ∈ P`, divided by `diam(P)²`. `pts` is `P`, `diam2` is `diam(P)²`, and
`q` is the point `q₀` being scored. -/
def objectivePoint (pts : Array Pt) (diam2 : Nat) (q : Pt) : Rat :=
  d1SqToPoint pts diam2 q

/-- The objective for `n = 2`: `F(q₀, q₁)² = ½ D₁(P, ℓ)² + ½ D₂(ℓ, P)²`. -/
def objectiveSegment (pts : Array Pt) (diam2 : Nat) (q₀ q₁ : Pt) : Rat :=
  (d1SqToSegment pts diam2 q₀ q₁ + d2Sq pts q₀ q₁) / 2

/-! ## Polygons

`F²` is assembled from per-edge pieces that depend only on an edge's two endpoints, so
the rough fit can compute each edge's pieces once and reuse them in every candidate
polygon containing that edge. -/

/-- The pieces of `F²` contributed by one edge `ℓ`: `d₁(p, ℓ)²` for each point `p` (in
the order of `pts`), and `D₂(ℓ, P)²`. -/
structure EdgeTerms where
  distSqs : Array Rat
  d2 : Rat
deriving Inhabited

def edgeTerms (pts : Array Pt) (a b : Pt) : EdgeTerms :=
  ⟨pts.map (distSqToSegment · a b), d2Sq pts a b⟩

/-- `d₁(p, Q)² = min over present edges of d₁(p, ℓ)²` for the point number `idx`. -/
def nearestSq (edges : Array EdgeTerms) (idx : Nat) : Rat :=
  edges.foldl (init := edges[0]!.distSqs[idx]!) fun best e => min best e.distSqs[idx]!

/-- `F²` from the pieces of the present edges (at least one):
`½ D₁(P, Q)² + (1 / (2m)) Σ D₂(ℓ, P)²`, where `m` is the number of present edges. -/
def objectiveFromEdges (numPts diam2 : Nat) (edges : Array EdgeTerms) : Rat :=
  let d1Sq := (List.range numPts).foldl (init := 0) (· + nearestSq edges ·) / (numPts * diam2 : Nat)
  let d2Total := edges.foldl (init := 0) (· + ·.d2)
  d1Sq / 2 + d2Total / (2 * edges.size : Nat)

/-- `objectiveFromEdges`, but giving up (returning `none`) as soon as the value is
certain to be `≥ bound`: first if the `D₂` part alone reaches it, then while the `D₁`
sum is being added up point by point. Every term is `≥ 0`, so a `none` answer means
the true value really is `≥ bound`; a `some` answer is exactly `objectiveFromEdges`.
Used by the rough fit to skip polygons that cannot make the top `k`. -/
def objectiveBelow (numPts diam2 : Nat) (edges : Array EdgeTerms) (bound : Option Rat) :
    Option Rat :=
  let d2Part := edges.foldl (init := (0 : Rat)) (· + ·.d2) / (2 * edges.size : Nat)
  let scale : Rat := (2 * numPts * diam2 : Nat)    -- F² = d1Total / scale + d2Part
  -- F² ≥ bound exactly when d1Total ≥ (bound - d2Part) * scale, computed once here.
  let limit := bound.map fun b => (b - d2Part) * scale
  if limit.any (· ≤ 0) then none
  else (go limit numPts 0 0).map (· / scale + d2Part)
where
  /-- Add `d₁(p, Q)²` for the `left` points numbered from `idx` on to `total`, giving up
  (`none`) as soon as the total reaches `limit`. -/
  go (limit : Option Rat) : Nat → Nat → Rat → Option Rat
    | 0, _, total => some total
    | left + 1, idx, total =>
      let total := total + nearestSq edges idx
      if limit.any (· ≤ total) then none else go limit left (idx + 1) total

/-- The present edges of an `n`-gon with the edges in `missing` absent. A segment
(`n = 2`) has the single edge 0. -/
def presentEdges (n : Nat) (missing : List Nat) : List Nat :=
  if n == 2 then [0] else (List.range n).filter (!missing.contains ·)

/-- The objective for a polygon `qs` (`n = qs.size ≥ 2`) with the edges in `missing`
absent; edge `e` joins `qs[e]` to `qs[(e + 1) % n]`. For `n = 2` this equals
`objectiveSegment`. -/
def objectivePolygon (pts : Array Pt) (diam2 : Nat) (qs : Array Pt) (missing : List Nat) : Rat :=
  let n := qs.size
  let edges := (presentEdges n missing).toArray.map fun e => edgeTerms pts qs[e]! qs[(e + 1) % n]!
  objectiveFromEdges pts.size diam2 edges

end PolyFit
