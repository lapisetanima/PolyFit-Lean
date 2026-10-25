# Polygon fitting: specification and settled decisions

## Setup
- Image of `I` rows and `J` columns. A point is `(i, j)` in **matrix style**: row `i`
  counted **downward from the top**, column `j` rightward (origin at the upper left).
  Pixel `(i, j)` is the integer point `(i, j)`. (Changed back from lower-left on 2026-10-20.)
- "Counterclockwise" always means as seen on screen, i.e. in the plane `(x, y) = (j, −i)`.
  Conveniently, `cross(u, v) = u.i v.j − u.j v.i` in `(i, j)` equals the usual cross
  product in `(x, y)`, so `cross > 0` is a counterclockwise (left) turn on screen.
- Input: points `P` (integer pixels), polygon number `n ≥ 1`, missing edges `M`.
- Output vertices `q_0, …, q_{n-1}` are **integer points**. They are not restricted to the
  image; a bound like `(-I, 2I) × (-J, 2J)` is expected to be provable.
- Edge `ℓ_i` joins `q_i` to `q_{(i+1) mod n}`. For `n = 1` there are no edges; for `n = 2`
  there is one edge. For `n ≤ 2`, `M` is ignored.
- For `n ≥ 3`, `M ⊆ {0, …, n-1}` must contain no two cyclically consecutive entries
  (so `|M| ≤ ⌊n/2⌋`, and at most one edge is missing when `n = 3`).

## Objective
`d` is Euclidean distance and `d_1(p, A) = inf_{q ∈ A} d(p, q)`.

    D_1(P, A)² = (1 / diam(P)²) · mean_{p ∈ P} d_1(p, A)²
    D_2(ℓ, P)² = (1 / L(ℓ)²) · ∫_0^1 d_1(q_0 + t(q_1 - q_0), P)² dt

`Q` is the union of the *present* edges `ℓ_i, i ∉ M`, so `d_1(p, Q) = min_{i ∉ M} d_1(p, ℓ_i)`
(minimum per point, then averaged).

| n | objective |
|---|---|
| 1 | `q_0` = centre of mass of `P`, each coordinate rounded to the nearest integer with halves rounded **up** (3.5 → 4); reported `F² = D_1(P, {q_0})²` |
| 2 | `F² = ½ D_1(P, ℓ)² + ½ D_2(ℓ, P)²` |
| ≥ 3 | `F² = ½ D_1(P, Q)² + (1 / (2(n − |M|))) Σ_{i ∉ M} D_2(ℓ_i, P)²` |

Rounding each coordinate of the centre of mass gives exactly the integer point that
minimises `D_1(P, {q})²`, since that quantity splits into an `i` part and a `j` part.

The solver minimises `F²`, which is equivalent to minimising `F`. With integer vertices,
`F²` is an **exact rational number**:
- `diam(P)²` and `L(ℓ)²` are integers.
- Squared point-to-segment distances are rational.
- The integral is computed exactly. Every `|q(t) − p|² = L² t² + a_p t + b_p` has the same
  `t²` coefficient, so `d_1² = L² t² + min_p (a_p t + b_p)`, a lower envelope of lines with
  integer coefficients and rational breakpoints.

During the search, a zero-length edge uses `L² = 1` in place of `0`. Only the final
polygon is checked for zero-length edges (error 3).

## Pipeline (agreed 2026-10-20): Python conducts, Lean carries out the steps
Python controls the flow and records the result of every step; each step is one Lean
command. Lean is stateless (Python resends the points each time) and recomputes anything
it relies on (such as `diam(P)`) rather than trusting values from Python.

**`PointSet` (immutable, recorded once per set of points).** At least 2 distinct points
(Python raises an error otherwise; duplicates are removed). Computed by Lean's `describe`:
- centre of mass `COM` (exact fractions),
- `diam(P)²` (integer), inner radius² `min_p |p − COM|²` and outer radius² `max_p |p − COM|²`
  (exact fractions; the inner radius may be 0),
- the convex hull: vertices only (collinear points on hull edges are left out),
  counterclockwise on screen, starting at the vertex with the largest `j`; on a tie
  (two vertices on a vertical right-hand edge) the one at or just above `COM`'s row
  (largest `i` with `i ≤ COM_i`), or, if both are below it, the higher one (smaller `i`).

**`FitAttempt` (mutable, one per choice of `n` and `M`)**, filled in this order:
1. *Reduced hull* (`reduce_hull`): let `h` = number of hull vertices. If `h < n`: error 5.
   If `n ≤ h ≤ 2n`: keep all. If `h > 2n`: Visvalingam–Whyatt down to `2n` (repeatedly
   delete the vertex whose triangle with its two neighbours has the least area; ties go
   to the vertex found first). **Implemented** (Lean `Hull.lean`, Python
   `polyfit.reduce_hull`); the survivors keep their hull order.
2. *Rough fit* (`rough_fit`, given the candidates from Python): score every cyclically
   ordered `n`-subset of the candidates, and every rotation of its labels when `M ≠ ∅`.
   Record the top `K` (default 2) polygons with their `F²`. **Implemented** (Lean
   `Rough.lean`, Python `polyfit.rough_fit`). Details: the top `K` are *distinct*
   polygons (two labellings with the same present edges, which happens when `M` is
   rotation-symmetric, count once); on a tie the polygon found first is kept, in the
   order of lexicographic subsets, then rotations. Each edge's pieces of `F²` are
   computed once per pair of candidates and reused. At most 2,000,000 polygons are
   scored (otherwise error 4). Timing: n = 6 on 12 candidates takes about 0.1 s, or
   0.3 s with edges missing (5,544 polygons), including process start-up.
3. *Fine fit* (`fine_fit`, given the best rough polygon): local search; record the
   polygon, its `F²`, the number of accepted moves, and whether it converged (did not
   run out of fuel; only a converged result is a guaranteed local minimum).
   **Implemented for all n ≥ 2 (agreed 2026-10-20; Lean `Polish.lean`)** as two
   alternating searches from the best rough fit, sharing one fuel budget of 1,000
   accepted moves:
   - *Fine:* best-improvement local search with step size 1 (see below).
     Moves: for each edge (present or missing), its two endpoints by `δ` each,
     `δ ∈ {-1,0,1}²` (80 per edge, including moving just one endpoint); for `n ≥ 3`
     also translating the whole polygon (8). For `n = 2` these are the 80 moves of
     the two endpoints.
   - *Step size 1 only (decided 2026-10-23):* the fine and ultra-fine searches stay in
     the basin the rough fit chose; choosing the basin is the rough fit's job. Large
     steps (from about `diam/4`, halving) were tried and found a lower `F²` in 12 of 39
     notebook fits with n ≥ 3 (up to 3× lower), against 5 the other way: evidence that
     the rough fit does not always pick the best basin. Improving it is deferred.
   - *Ultra-fine:* the whole cube: all `n` vertices moved by `δ_v ∈ {-1,0,1}²`
     at once (`9ⁿ − 1` candidates). If one is better, take the best and run the fine
     search again; if none is, the result is **certified**: no polygon in the unit
     cube around it has a lower `F²`. Skipped for `n > 7` (then not certified); for
     `n = 2` the fine moves already are the cube.
   - Candidates with a zero-length edge are scored with the `L² := 1` fallback; the
     final polygon is checked (error 3).
   - Speed-ups, all exact: unchanged edges reuse their pieces of `F²`; candidates are
     abandoned once certain not to beat the best so far; in the cube each edge has
     only 81 versions, precomputed, and each candidate is first tested with
     whole-number lower bounds (`⌊1024·d⌋`), so only near-winners are scored exactly.
     Typical times: 0.3–4 s for n = 3…7 (n = 7 was 55 s before the lower bounds).
   - *Proof target:* termination (structural recursion on fuel or round counters; since
     2026-10-23 `polish` and everything it calls has no mutable variables, with replies
     identical to the earlier loops); the result is never worse than the start; if
     certified, `F²(Q') ≥ F²(result)` for every `Q'` in the unit cube.

**Recorded in each `FitAttempt`** (agreed 2026-10-20: only the rough fits and the final
result, not the intermediate fine fit; Python `polyfit/attempt.py`): `k`,
`reduced_hull`, `rough_fits` (top `k`, each with exact `F²`), `fine_method`
(`centre_of_mass` for n = 1, `local_search` for n ≥ 2, `mock`), `certified`
(local_search only), and the final `vertices` and `objective_sq`. An attempt's
characteristics are `(n, missing edges, engine, k)`, with `k` only where there is a
rough fit. Loading a saved `PointSet` replays every attempt and requires the same
results (everything but the timing).

**The `mock` engine (agreed 2026-10-22; Python `polyfit/mock.py`)** is a rough,
purely geometric baseline that does not optimise `F`. Candidates: the reduced hull from
Lean's `reduce_hull` (so error 5 if the hull has fewer than `n` vertices), recorded in
the attempt's `reduced_hull`. n = 1: the rounded centre of mass. n = 2: the two
candidates farthest apart. n ≥ 3: among all `n`-subsets of the candidates in hull order
(so convex), the one whose edge lengths are most nearly equal, minimising
`Σ_i (ℓ_i − mean ℓ)² / (mean ℓ)²` over all `n` edges, missing or not (scale-free, so
small polygons get no advantage); ties go to the first subset. Lengths are floats. The
chosen polygon is then scored with its exact `F²` by a Lean `evaluate` query.

*Effect on the fooling example:* the hull candidates include the diagonal's ends, so
the local search from the rough fit starts in the right basin and finds `F² = 0.0117`
(0.0264 from the farthest pair, the old segment start).

*Rough-fit speed-up (exact):* a candidate polygon is abandoned as soon as it is certain
not to make the top `k` (first by its `D₂` part alone, then while its `D₁` sum is added
up point by point); results are unchanged.

For `n = 1` the attempt records only the rounded `COM` and its `F²`.
Every attempt also records its settings (`K`, fuel, ...) for reproducibility, and results
can be saved to and loaded from JSON. Everything is recorded exactly (`F²`, not `F`).

**Attempts policy (agreed 2026-10-20; implemented in `polyfit/attempt.py`, `pointset.py`):**
- Each `PointSet` carries `attempts`, the list of its completed fits in order
  (`ps.fit(n_vertices=…, missing_edges=…, engine=…)` runs one and appends it).
- Only polygon fits are attempts. `evaluate` calls are queries and are not recorded.
- An attempt is never repeated: an attempt's characteristics are `(n_vertices,
  missing_edges, engine)`, with the missing edges normalised as the solver uses them
  (sorted, duplicates removed, ignored for `n ≤ 2`). If a matching attempt is already
  recorded, `ps.fit` does not run the fitter and returns the recorded one. Solver
  settings (fuel, `K`, …) will join the characteristics once attempts record them.
  Saved data with two matching attempts is rejected.
- A failed fit is not recorded: it raises, and by policy it stops the work on that
  point set (`attempt_fits` moves on to the next point set).
- A completed attempt is frozen, and records its start time and duration (wall clock,
  including the solver process start-up).
- Purpose: later, compare a point set's attempts and pick the one that best balances
  complexity (fewer vertices is better) against `F²` (lower is better, but more
  vertices always lower it).
- For now an attempt holds the one-call Lean result. The pipeline steps (reduced hull,
  top-`K` rough fits, fine fit with converged flag) will be added as those commands exist.

## Search strategy
**Segment (n = 2):** since 2026-10-23 the same pipeline as for polygons (reduced hull,
rough fit, fine fit; see above). The earlier separate segment search, which started from
the farthest pair of points, was removed: a poor start, and the notebooks never used it.

*Observed property of the objective:* for points evenly spaced with gap `g` along a
segment of length `L₀`, extending the segment by `e` at each end gives
`D₂² = (L₀g²/12 + 2e³/3) / (L₀ + 2e)³`, which is minimised at `e = g/2`. So the best
segment overshoots sparse data by about half the point spacing (exactly 0 for dense
pixels on the integer grid). **Accepted (2026-10-20):** the points are samples of the
true segment, so with few samples its ends should lie past the extreme samples; the
overshoot shrinks as the sampling gets denser.

**Polygons (n ≥ 3), tentative:** the full joint neighbourhood has `9ⁿ − 1` moves, which is
too many. Use moves that grow linearly in `n`: single vertices (`8n`), the two endpoints
of one edge jointly (`80n`), and translating the whole polygon (`8`).

## Python ↔ Lean protocol
Request on stdin: `{"points": [[i, j], ...], "n": n, "missing": [m, ...]}`

**Evaluate mode:** adding `"vertices": [[i, j], ...]` (exactly `n` integer points; negative
coordinates allowed) makes the solver skip the search and return the exact `F²` of those
vertices, for any `n`. A zero-length edge gives error 3. Python:
`polyfit.evaluate(points, vertices=…, missing_edges=…)`.

**Commands** (`"command"` field; without it, a fit or evaluation):
- no command: a search only for `n = 1` (error 4 for `n ≥ 2`; Python's `polyfit.fit` runs
  `reduce_hull` → `rough_fit` → `fine_fit` itself), or evaluate mode for any `n`.
- `describe`: `{points}` → `com`, `diam_sq`, `inner_radius_sq`, `outer_radius_sq`, `hull`.
- `reduce_hull`: `{points, n}` (n ≥ 2) → `{"candidates": [[i, j], ...]}`.
- `rough_fit`: `{points, n, missing, candidates, k}` (n ≥ 2, distinct candidates, k ≥ 1,
  default 2) → `{"rough_fits": [{"poly_points": …, "objective_function": [a, b]}, …]}`,
  best first.
- `fine_fit`: `{points, n, missing, start}` (n ≥ 2, `start` has n vertices) → the usual
  reply plus `"moves"` and `"certified"`.

Reply on stdout: `{"error": e, "objective_function": [a, b], "poly_points": [[i, j], ...]}`,
where `F² = a / b`. When `e ≠ 0` the other two fields are `null`, and a human-readable
explanation goes to stderr.

| error | meaning |
|---|---|
| 0 | OK |
| 1 | `diam(P) = 0` |
| 2 | two cyclically consecutive entries in `M` |
| 3 | the final polygon has an edge of length 0 |
| 4 | malformed input (bad JSON, `n < 1`, missing-edge index out of range, negative coordinate, empty `P`) |
| 5 | the convex hull has fewer than `n` vertices |

## Proofs (plan agreed 2026-10-21; started 2026-10-22)
**Layout:** a separate Lake project `proofs/` (sibling of `lean/`) that requires Mathlib
and requires the solver package by path (`../lean`), so the theorems are about the very
functions the executable runs, and building the solver never needs Mathlib. Both
projects must use the same Lean toolchain (Mathlib pins one; `lean/` may need to move to
it). Mathlib tag `v4.35.0` matches the solver's toolchain. Proof files import only the
Mathlib modules they need (loading all of Mathlib is slow).

**Layers, easiest first:**
- *A. Warm-ups:* `roundHalfUp a b` is the nearest integer to `a/b` with halves rounded up;
  **the n = 1 theorem (first proof to do):** the rounded centre of mass minimises
  `objectivePoint pts (diamSq pts) q` (equivalently `Σ_p distSq p q`) over all integer
  points `q`, for nonempty `pts` with `diam(P) > 0`. Needs only rational algebra
  (`Σ |p − q|² = k |q − c|² + const`, separately in `i` and `j`), no reals.
  **Done** (`proofs/Proofs/Point.lean`, `objectivePoint_centreOfMassRounded_le`), with
  no hypotheses at all: for empty `P` or `diam(P) = 0` both sides are 0, since Lean's
  `x / 0 = 0`.
- *B. Search guarantees, about the computed objective* (`objectivePolygon`, exact
  rationals, no analysis): the result is never worse than the start; **certificate
  theorem:** if `certified`, every polygon in the unit cube `{-1,0,1}^{2n}` around the
  result has `objectivePolygon` ≥ the result's. Needs lemmas for the speed-ups:
  `objectiveBelow = none` ⇒ value ≥ bound; the `⌊1024·d⌋` lower bounds are lower bounds;
  cached `EdgeTerms` equal recomputed ones.
  **Next (2026-10-23):** these theorems for `polish`, which covers n = 2 as well (the
  separate segment search was removed). `polish` and everything it calls are now
  structural recursion, so they can be proved by induction.
  **Agreed 2026-10-24:** the certificate assumes `diam(P) > 0` (without it the `D₁` part
  divides by 0 and `objectiveBelow` rejects every candidate, so the theorem would be
  false; `parseProblem` already guarantees it). The ultra-fine whole-number bounds
  (`floorScaled`/`ceilScaled`, which clip negatives to 0) are sound because every
  computed `D₂` is `≥ 0`, proved by a piecewise argument that needs no correctness of
  the envelope walk: the walk cuts `[0, 1]` into ordered pieces and integrates one line
  `ℓ_p` on each, and `L² t² + ℓ_p(t) = |q(t) − p|² ≥ 0` for every `p`, so each piece adds
  `∫ |q(t) − p|² dt ≥ 0` (in `Rat`: `∫ₛᵉ (a + bt)² dt = (e − s)(x² + xy + y²)/3` with
  `x = a + bs`, `y = a + be`). For this, `lowerEnvelopeIntegral` was made recursive and
  clamps each switch time with `max t tc`, so the pieces are in order by construction.
  **Proved 2026-10-24** (`proofs/Proofs/Polish.lean`, no `sorry`, standard axioms only):
  for every `n`, `polish` keeps the vertex count, reports `F²` of its result, is never
  worse than its start, and **if `diam(P) > 0` and the result is certified, no polygon in
  the unit cube `{-1,0,1}^{2n}` around it has a lower computed `F²`** (`polish_certified`).
  On the way: computed `D₂ ≥ 0` and `F² ≥ 0`; `objectiveBelow`'s early exits are exact;
  each fine and ultra-fine move picks the best candidate (the ultra-fine step visits all
  `9ⁿ` offset choices, its table holds the moved edges, its whole-number bounds are
  sound). Still about the computed objective: equality with the true `F²` is layer C.
- *C. The computed objective equals the mathematical one* (Mathlib reals and integrals):
  **Proved 2026-10-25** (`proofs/Proofs/Faithful.lean`, `Envelope.lean`; no `sorry`,
  standard axioms only): the true `F²` is defined in `ℝ²` (Euclidean distance written out,
  since Mathlib's distance on `ℝ × ℝ` is the max of the coordinate distances), and
  `objectivePolygon = trueF2` for nonempty `P` and polygons without zero-length present
  edges. Ingredients: `diamSq = diam(P)²`; `distSqToSegment` is the infimum over the
  segment; the envelope walk computes `∫₀¹ min_ℓ ℓ(t) dt` (it keeps the lowest line, ties
  to the smallest slope, and never runs out of switches). Hence `polish_certified_true`:
  a certified result has no larger true `F²` than any polygon in its unit cube, when
  neither has a zero-length edge.
  `distSqToSegment` = `inf_{t∈[0,1]} |q(t) − p|²`; `segmentIntegral` = `∫₀¹ min_p |q(t) − p|² dt`
  (correctness of the lower-envelope walk); hence `objectivePolygon` = `F²` of this spec.
- B + C: a certified result is a local minimum of the true `F²` over the integer cube.
- Optional: hull correctness, `combinations` lists each subset once, `insertBest` keeps
  the true top `K`.

**Method:** write all theorem statements first with `sorry`, fill them in one by one
(`#print axioms` shows what is still open); prove properties of simple reference
versions (lists, plain recursion) and prove the fast code equal to them. The JSON
parsing and the Python side stay trusted, not verified.

## Status (2026-10-21)
Done: describe, reduce_hull, rough_fit, fine + ultra-fine fit (certified for n ≤ 7),
attempts with replay verification, notebook experiments (random points, annulus,
thick data). Possible later work, discussed but not started: speeding up the fine
search for many points (check D1 + unchanged D2 before integrating; O(k log k)
envelope), multicore or branch-and-bound ultra-fine check for larger n, truncated D1
for outliers, a baseline comparison with standard methods.

## Convexity
Fitted polygons are expected to be roughly convex, but convexity is **not enforced**:
the search may move to a non-convex polygon if that lowers `F²`. Initial guesses
should be convex.

## Ideas for later: initial guesses for polygons (n ≥ 3)
- **Visvalingam–Whyatt on the convex hull:** repeatedly delete the hull vertex whose
  removal changes the area least, until `n` remain. Integer-only (areas from `cross`).
- **PCA** (centre, main axis, spread): good for orientation and for `n = 4` or thin shapes;
  computing it needs floats, so it would be done in Python and sent as a starting guess
  (an optional `"start"` field that Lean only refines; the local-minimum theorem holds
  for any start).
- **Detecting missing edges from the data:** missing edges should line up with gaps in
  the points that are larger than random sampling would produce. Goal: decide
  statistically how many edges are missing and roughly where, before the search.
  Possible tool: for `m` points spread at random along a perimeter of length `P`, the
  gaps are roughly exponential with mean `P/m`, and the largest is typically about
  `(P/m) ln m`, so gaps well beyond that are evidence of a missing edge.
- **Multiple starts:** run the search from several guesses and keep the lowest `F²`.
- **Subsets of simplified hull vertices (user's plan):** simplify the hull to `2n` vertices
  with Visvalingam–Whyatt, label them in hull order, and score every `n`-subset in cyclic
  order (`C(2n, n)` candidates: 20, 70, 252, 924 for n = 3…6; 12,870 for n = 8). Search
  from the best few. With missing edges each subset has `n` rotations, which gap
  detection could narrow down. If this gets too slow for large `n`: an additive
  approximation of `F²` (charge points to hull arcs) allows an exact dynamic program over
  `m` ordered candidates in about `O(m³ n)`.
- **Segments (n = 2), same idea:** the farthest-pair start can be fooled (two outliers at
  opposite corners plus points on the diagonal: the search ends at a local minimum with
  `F² = 0.026` versus `0.012` on the diagonal). Fix: score all (or sampled) pairs of
  points as candidate segments and search from the best few; optionally add a PCA start.
