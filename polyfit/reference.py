"""Exact reference implementations of the objective, in pure Python with Fractions.

These are written straight from docs/spec.md, independently of the Lean code, and
are used by the tests to check the Lean solver's answers exactly.
"""

from __future__ import annotations

from fractions import Fraction
from itertools import combinations


def dist_sq(p, q) -> int:
    return (int(p[0]) - int(q[0])) ** 2 + (int(p[1]) - int(q[1])) ** 2


def diam_sq(points) -> int:
    return max((dist_sq(p, q) for p, q in combinations(points, 2)), default=0)


def round_half_up(x: Fraction) -> int:
    """Nearest integer, with halves rounded up (3.5 -> 4, -3.5 -> -3)."""
    return (x + Fraction(1, 2)).__floor__()


def centre_of_mass_rounded(points) -> tuple[int, int]:
    k = len(points)
    return (round_half_up(Fraction(sum(int(p[0]) for p in points), k)),
            round_half_up(Fraction(sum(int(p[1]) for p in points), k)))


def d1_sq_to_point(points, q) -> Fraction:
    """D_1(P, {q})^2 = mean d(p, q)^2 / diam(P)^2."""
    return Fraction(sum(dist_sq(p, q) for p in points), len(points) * diam_sq(points))


def objective_point(points, q) -> Fraction:
    """F(q_0)^2 for n = 1."""
    return d1_sq_to_point(points, q)


# --- Point-set description ---------------------------------------------------------
# The hull is found by brute force (a directed pair a -> b is a counterclockwise hull
# edge when no point lies to its right and every collinear point lies between a and b),
# independently of the monotone chain used in Lean.

def centre_of_mass(points) -> tuple[Fraction, Fraction]:
    k = len(points)
    return (Fraction(sum(int(p[0]) for p in points), k), Fraction(sum(int(p[1]) for p in points), k))


def radius_sq(p, c) -> Fraction:
    return (int(p[0]) - c[0]) ** 2 + (int(p[1]) - c[1]) ** 2


def cross(u, v) -> int:
    """u.i v.j - u.j v.i: positive for a counterclockwise turn on screen (i down, j right)."""
    return u[0] * v[1] - u[1] * v[0]


def convex_hull(points, com) -> list[tuple[int, int]]:
    """Hull vertices, counterclockwise on screen, collinear points left out, starting
    at the rightmost vertex (ties: at or just above COM's row, else the higher one)."""
    pts = sorted({(int(p[0]), int(p[1])) for p in points})
    nxt = {}
    for a in pts:
        for b in pts:
            if a == b:
                continue
            ab = (b[0] - a[0], b[1] - a[1])
            ok = True
            for p in pts:
                c = cross(ab, (p[0] - a[0], p[1] - a[1]))
                between = min(a[0], b[0]) <= p[0] <= max(a[0], b[0]) and min(a[1], b[1]) <= p[1] <= max(a[1], b[1])
                if c < 0 or (c == 0 and not between):
                    ok = False
                    break
            if ok:
                nxt[a] = b
    best_j = max(v[1] for v in nxt)
    tied = [v for v in nxt if v[1] == best_j]
    above = [v for v in tied if v[0] <= com[0]]
    start = max(above) if above else min(tied)
    hull = [start]
    while nxt[hull[-1]] != start:
        hull.append(nxt[hull[-1]])
    return hull


def describe(points) -> dict:
    com = centre_of_mass(points)
    radii = [radius_sq(p, com) for p in points]
    return {"com": com, "diam_sq": diam_sq(points), "inner_radius_sq": min(radii),
            "outer_radius_sq": max(radii), "hull": convex_hull(points, com)}


# --- Segments (n = 2) -------------------------------------------------------------
# Deliberately computed differently from the Lean code: the nearest point on the
# segment is found by clamping the projection parameter (not with a cross product),
# and the integral uses every pairwise crossing as a breakpoint (not an envelope walk).

def dist_sq_to_segment(p, q0, q1) -> Fraction:
    """d_1(p, segment q0 q1)^2."""
    vi, vj = int(q1[0]) - int(q0[0]), int(q1[1]) - int(q0[1])
    length_sq = vi * vi + vj * vj
    if length_sq == 0:
        return Fraction(dist_sq(p, q0))
    t = Fraction((int(p[0]) - int(q0[0])) * vi + (int(p[1]) - int(q0[1])) * vj, length_sq)
    t = min(max(t, Fraction(0)), Fraction(1))
    ci, cj = int(q0[0]) + t * vi, int(q0[1]) + t * vj
    return (int(p[0]) - ci) ** 2 + (int(p[1]) - cj) ** 2


def segment_integral(points, q0, q1) -> Fraction:
    """Integral over t in [0, 1] of min_p |q0 + t (q1 - q0) - p|^2, exactly.

    Each |q(t) - p|^2 is a quadratic A t^2 + B t + C with the same A for every p, so
    two of them can only swap order where their B t + C parts cross. Between
    consecutive crossings a single p is nearest; find it at the midpoint and
    integrate that quadratic exactly.
    """
    vi, vj = int(q1[0]) - int(q0[0]), int(q1[1]) - int(q0[1])
    a = vi * vi + vj * vj
    quads = []
    for p in points:
        ui, uj = int(q0[0]) - int(p[0]), int(q0[1]) - int(p[1])
        quads.append((a, 2 * (ui * vi + uj * vj), ui * ui + uj * uj))

    breaks = {Fraction(0), Fraction(1)}
    for (_, b1, c1), (_, b2, c2) in combinations(quads, 2):
        if b1 != b2:
            t = Fraction(c2 - c1, b1 - b2)
            if 0 < t < 1:
                breaks.add(t)
    breaks = sorted(breaks)

    total = Fraction(0)
    for s, e in zip(breaks, breaks[1:]):
        mid = (s + e) / 2
        qa, qb, qc = min(quads, key=lambda q: q[0] * mid * mid + q[1] * mid + q[2])
        total += Fraction(qa, 3) * (e ** 3 - s ** 3) + Fraction(qb, 2) * (e ** 2 - s ** 2) + qc * (e - s)
    return total


def d1_sq_to_segment(points, q0, q1) -> Fraction:
    total = sum(dist_sq_to_segment(p, q0, q1) for p in points)
    return total / (len(points) * diam_sq(points))


def d2_sq(points, q0, q1) -> Fraction:
    """D_2(segment, P)^2, with L^2 replaced by 1 when L = 0."""
    length_sq = dist_sq(q0, q1)
    return segment_integral(points, q0, q1) / (length_sq if length_sq else 1)


def objective_segment(points, q0, q1) -> Fraction:
    """F(q_0, q_1)^2 for n = 2."""
    return (d1_sq_to_segment(points, q0, q1) + d2_sq(points, q0, q1)) / 2


# --- Polygons (n >= 3), hull trimming, rough fit ------------------------------------
# Brute force, straight from docs/spec.md.

def objective_polygon(points, verts, missing=()) -> Fraction:
    """F^2 for the polygon `verts` (n >= 2) with the edges in `missing` absent."""
    n = len(verts)
    present = [0] if n == 2 else [e for e in range(n) if e not in set(missing)]
    edges = [(verts[e], verts[(e + 1) % n]) for e in present]
    d1 = sum(min(dist_sq_to_segment(p, a, b) for a, b in edges) for p in points)
    d1 /= len(points) * diam_sq(points)
    d2 = sum(d2_sq(points, a, b) for a, b in edges)
    return d1 / 2 + d2 / (2 * len(edges))


def visvalingam(poly, target: int) -> list[tuple[int, int]]:
    """Repeatedly delete the vertex whose triangle with its neighbours has the least
    area (the first such, on a tie) until at most `target` remain."""
    cur = [tuple(int(c) for c in p) for p in poly]
    while len(cur) > target:
        m = len(cur)
        areas = [abs(cross((cur[k][0] - cur[k - 1][0], cur[k][1] - cur[k - 1][1]),
                           (cur[(k + 1) % m][0] - cur[k - 1][0], cur[(k + 1) % m][1] - cur[k - 1][1])))
                 for k in range(m)]
        del cur[areas.index(min(areas))]
    return cur


def reduce_hull(points, n: int) -> list[tuple[int, int]] | None:
    """The reduced hull, or None where Lean reports error 5 (fewer than n hull vertices)."""
    hull = convex_hull(points, centre_of_mass(points))
    return None if len(hull) < n else visvalingam(hull, 2 * n)


def rough_fit(points, n: int, missing, candidates, k: int) -> list[tuple[list, Fraction]]:
    """Score every cyclic n-subset of the candidates (every rotation of its labels when
    edges are missing), and return the best k distinct polygons, best first; ties go to
    the one found first."""
    from itertools import combinations as combos
    missing = sorted(set(missing)) if n >= 3 else []
    present = [0] if n == 2 else [e for e in range(n) if e not in missing]
    rotations = range(n) if (missing and n >= 3) else [0]
    scored = []
    for sub in combos(range(len(candidates)), n):
        for r in rotations:
            labels = [sub[(t + r) % n] for t in range(n)]
            verts = [tuple(int(c) for c in candidates[i]) for i in labels]
            key = frozenset(frozenset((labels[e], labels[(e + 1) % n])) for e in present)
            scored.append((objective_polygon(points, verts, missing), len(scored), key, verts))
    scored.sort(key=lambda s: (s[0], s[1]))
    best, seen = [], set()
    for f2, _, key, verts in scored:
        if key not in seen:
            seen.add(key)
            best.append(([list(v) for v in verts], f2))
        if len(best) == k:
            break
    return best
