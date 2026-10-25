# polyfit-lean

**Exact, certifiable polygon fitting, with the solver written in Lean 4 and designed for formal proof.**

Given a set of pixels, polyfit-lean finds the polygon with *n* vertices (a point, a segment, a triangle, …) that best fits them, optionally with some edges declared *missing*, for shapes that are open on one side. In brief:

- **A new objective function.** A two-sided, mean-square relative of the Hausdorff distance. It measures both how well the polygon covers the points and how well the points cover the polygon, and it is scale-invariant.
- **Exact arithmetic throughout.** Every score, including an integral along each edge, is an exact rational number. The solver contains no floating point.
- **Certified results, built for verification.** Each fit can be certified as a local minimum by an exhaustive check, and the Lean code is structured so that these guarantees can be proved formally. That is the project's next stage.

![Fits with 3 to 8 vertices to a thick, noisy pentagon outline, and the objective against n](docs/images/thick_data.png)

*Fits to a noisy pentagon outline (223 points) with n = 3 … 8. Light blue: the coarse initial guess. Red: the refined, certified fit. Last panel: the objective and its two parts. It is lowest at the true n = 5, where the two parts balance.*

---

## The objective function

For a point set $P$ and a polygon $Q$, write $d_1(x, A) = \inf_{a\in A}|x - a|$. The objective combines two terms:

$$
D_1(P,Q)^2 = \frac{1}{\mathrm{diam}(P)^2}\cdot\frac{1}{|P|}\sum_{p\in P} d_1(p,Q)^2,
\qquad
D_2(\ell,P)^2 = \frac{1}{L(\ell)^2}\int_0^1 d_1\big(q_0 + t(q_1-q_0),P\big)^2 dt ,
$$

$$
F(Q)^2 = \tfrac12 D_1(P,Q)^2 + \frac{1}{2m}\sum_{i\notin M} D_2(\ell_i,P)^2 ,
$$

where $\ell_i$ are the polygon's edges, $M$ the missing ones, and $m$ the number present.

**Why this shape of objective.** The Hausdorff distance between two sets combines the two directed distances, *points → shape* and *shape → points*, but by their maximum: it is an $L^\infty$ measure, so a single outlier decides it. $F$ keeps both directions but averages squares, as an $L^2$ measure:

- $D_1$ (points → polygon) is essentially orthogonal least squares. When points are plentiful it is the maximum-likelihood fit of the edge lines under Gaussian noise.
- $D_2$ (polygon → points) is an integral along each edge. It decides what $D_1$ cannot see: where edges **start and stop**, edges that run **through empty space**, and how many vertices are justified.

**Some consequences, derived and confirmed by experiment.**

- **Principled overshoot.** For collinear points spaced $g$ apart, the optimal segment extends exactly $g/2$ beyond the outermost points at each end. This is the right answer if the points are samples of a longer segment, and it vanishes as the sampling gets denser.
- **A built-in complexity penalty.** Each edge's $D_2$ is roughly *(gap between points) ÷ (edge length)*. For a fixed outline, extra vertices shorten the edges, so the $D_2$ part grows like $n^2$. On data with real corners, $F$ is therefore lowest near the true number of corners (as in the figure); on unstructured data it prefers small polygons.
- **Evenly sized edges.** For a fixed perimeter, $\sum_i 1/L_i^2$ is smallest when all lengths are equal (it is a convex function of the lengths), so fits avoid tiny edges.
- **Scale invariance.** Both terms are dimensionless, so the fit does not depend on the image resolution.

## Exactness: an integral computed in rational arithmetic

Polygon vertices live on the integer grid, so the distance and length terms are rational. The edge integral is the interesting part. Along an edge, $q(t) = q_0 + tv$ with $L^2 = |v|^2$, and

$$
|q(t)-p|^2 = L^2 t^2 + a_p t + b_p ,\qquad a_p = 2(q_0-p)\cdot v,\quad b_p = |q_0-p|^2 .
$$

Every point $p$ gives a quadratic with the **same** $t^2$ coefficient. Hence

$$
\min_p |q(t)-p|^2 = L^2 t^2 + \min_p (a_p t + b_p),
$$

so the integrand is a fixed quadratic plus the **lower envelope of straight lines** with integer coefficients. The envelope's breakpoints are rational, and each piece integrates exactly. So the whole objective $F^2$ is an exact rational number, computed with Lean's arbitrary-precision integers and rationals.

## The algorithm

1. **Describe** the point set: exact centre of mass, diameter, radii, convex hull.
2. **Reduce the hull** to at most $2n$ candidate vertices (using the Visvalingam–Whyatt trimming algorithm).
3. **Rough fit:** a global search over every cyclically ordered $n$-subset of the candidates, and over every labelling of the edges when some are missing.
4. **Fine fit:** a local pattern search, with a move set that grows linearly in the polygon number $n$.
5. **Ultra-fine fit:** examine *all* $9^n - 1$ polygons in the unit cube around the result (every vertex moved by at most one pixel in each coordinate). If none is better, the result is **certified** as a local minimum.

Every speed-up is **exact**, so it never changes the answer: candidates are abandoned only once they provably cannot win, and the ultra-fine check first screens candidates with whole-number lower bounds. A hexagon is fitted and certified in seconds.

## Why Lean, and what will be proved

Lean 4 is both a fast, compiled functional language and an interactive theorem prover. The solver is written so that its guarantees can be stated and proved *about the very code that runs*:

- **Termination by construction:** every loop is bounded, and the code uses no `partial` definitions.
- **No floating point:** every quantity is an exact `Int`, `Nat` or `Rat`, so mathematical statements apply literally.
- **Small, checkable steps:** each optimisation (pruning, caching, lower bounds) is a separate function with a one-line correctness property.

**Proof roadmap** (in a separate project using Mathlib):

- [x] **n = 1:** the rounded centre of mass minimises the objective over all integer points.
- [x] **Certificate theorem:** if a result is certified (and $\operatorname{diam}(P) > 0$), then $F^2(Q') \ge F^2(Q)$ for the *computed* $F^2$, for every polygon $Q'$ in the unit cube around it.
- [x] **Faithfulness:** the computed objective equals the mathematical definition above, including the exact lower-envelope integral.

Together, the last two state that **every certified fit is a true local minimum of $F$**, checked by machine.

## Using it

Python drives the pipeline step by step and records every attempt: the rough fits, the final polygon, its exact $F^2$, whether it is certified, and timings. Saved results are re-verified on loading by replaying each step in Lean.

```python
import polyfit
from polyfit import samples

ps = polyfit.PointSet.from_points(samples.hexagon_outline())
attempt = ps.fit(n_vertices=6)
attempt.vertices, attempt.objective_sq, attempt.certified
```

**Setup:** [elan](https://github.com/leanprover/elan) (Lean 4; the version is pinned in `lean/lean-toolchain`) and Python 3.11 or later.

```bash
cd lean && lake build && cd ..                       # build the Lean solver
python -m venv .venv
.venv/Scripts/python -m pip install -e ".[dev]"      # on Linux/macOS: .venv/bin/python
.venv/Scripts/python -m pytest                       # about 500 tests
```

| Path | Contents |
|---|---|
| [`lean/PolyFit/`](lean/PolyFit) | The Lean 4 solver: geometry, exact objective, hull, rough fit, local search, JSON protocol |
| [`polyfit/`](polyfit) | The Python package: point sets, fit attempts, the Lean bridge, plotting, an independent exact reference implementation |
| [`tests/`](tests) | Tests, most checking Lean's results exactly against the Python reference |
| [`notebooks/explore.ipynb`](notebooks/explore.ipynb) | Experiments: sample shapes, random points, an annulus, dense noisy outlines |
| [`docs/spec.md`](docs/spec.md) | The full specification, the design decisions, and the proof plan |

## Development

The problem, the objective function and the design decisions are the author's. The implementation was developed with [Claude Code](https://claude.com/claude-code), working step by step from the specification in [docs/spec.md](docs/spec.md), with every component tested against an independent reference.

## License

[MIT](LICENSE)
