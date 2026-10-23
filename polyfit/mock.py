"""The "mock" engine: a rough, purely geometric baseline fit in Python.

It does not optimise F. Instead it picks the most regular polygon on the reduced
convex hull:

- n = 1: the centre of mass, rounded to the nearest integer point;
- n = 2: the two candidates farthest apart;
- n >= 3: among all n-subsets of the candidates, taken in hull order (so every
  candidate polygon is convex), the one whose edge lengths l_i are most nearly equal,
  i.e. with the smallest  sum_i (l_i - mean(l))^2 / mean(l)^2  (all n edges count,
  missing or not; dividing by mean(l)^2 makes it independent of the polygon's size).
  On a tie the subset found first wins.

The candidates are the reduced hull from Lean's `reduce_hull` (all hull vertices if
there are between n and 2n, otherwise trimmed to 2n; error 5 if fewer than n). Edge
lengths are computed in floating point. The chosen polygon is then scored with its
exact F^2 by a Lean `evaluate` query (a query, so nothing is recorded by it).
"""

from __future__ import annotations

from itertools import combinations

import numpy as np

from . import bridge
from .problem import FitRequest, FitResult, make_request


def edge_spread(verts: np.ndarray) -> float:
    """sum_i (l_i - mean(l))^2 / mean(l)^2 for the closed polygon `verts`."""
    edges = np.roll(verts, -1, axis=0) - verts
    lengths = np.sqrt((edges.astype(float) ** 2).sum(axis=1))
    mean = lengths.mean()
    return float(((lengths - mean) ** 2).sum() / mean ** 2)


def mock_polygon(points: np.ndarray, n: int, exe=None, timeout: float = 600.0) -> tuple[np.ndarray, np.ndarray | None]:
    """The mock polygon's vertices, and the candidates it was chosen from (None for n = 1)."""
    if n == 1:
        return np.round(points.mean(axis=0)).astype(np.int64)[None, :], None

    cands = bridge.reduce_hull(points, n_vertices=n, exe=exe, timeout=timeout)
    if n == 2:
        best, best_d = (0, 1), -1
        for a, b in combinations(range(len(cands)), 2):
            d = int(((cands[a] - cands[b]) ** 2).sum())
            if d > best_d:
                best, best_d = (a, b), d
        return cands[list(best)], cands

    best, best_spread = None, float("inf")
    for subset in combinations(range(len(cands)), n):
        spread = edge_spread(cands[list(subset)])
        if spread < best_spread:
            best, best_spread = subset, spread
    return cands[list(best)], cands


def mock_fit(points, *, n_vertices: int, missing_edges=(), exe=None,
             timeout: float = 600.0) -> tuple[FitResult, np.ndarray | None]:
    """The mock fit, scored with its exact F^2. Returns (result, candidates); candidates
    is None for n = 1. Raises FitFailed (code 5) if the hull has fewer than n vertices."""
    request = make_request(points, n_vertices=n_vertices, missing_edges=missing_edges)
    verts, cands = mock_polygon(request.points, request.n_vertices, exe=exe, timeout=timeout)
    scored = bridge.evaluate(request.points, vertices=verts, missing_edges=request.missing_edges,
                             exe=exe, timeout=timeout)
    return FitResult(request=request, vertices=verts, objective_sq=scored.objective_sq), cands


def solve_mock(request: FitRequest, exe=None, timeout: float = 600.0) -> FitResult:
    """The mock fit for an already validated request (used by polyfit.fit)."""
    result, _ = mock_fit(request.points, n_vertices=request.n_vertices,
                         missing_edges=request.missing_edges, exe=exe, timeout=timeout)
    return result
