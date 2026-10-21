"""Problem and result types, plus input validation.

Coordinate convention: every point is (i, j) in matrix style, where i is the row
counted downward from the top and j is the column counted rightward from the left
(origin at the upper left). Pixel (i, j) is centred at the integer point (i, j).
Fitted polygon vertices are integer points too. "Counterclockwise" means as seen on
screen.

Edge convention: for a polygon with n >= 3 vertices v[0..n-1], edge e joins
v[e] to v[(e + 1) % n]. A point (n = 1) has no edges and a segment (n = 2)
has the single edge 0; for n <= 2 any missing edges are ignored.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction

import numpy as np


class FitInputError(ValueError):
    """The request sent to the solver is malformed."""


@dataclass(frozen=True)
class FitRequest:
    points: np.ndarray  # shape (k, 2), int64, (row, col)
    n_vertices: int  # 1 = point, 2 = segment, 3 = triangle, ...
    missing_edges: tuple[int, ...]  # sorted, unique, each in [0, n_vertices - 1]
    vertices: np.ndarray | None = None  # evaluate mode: (n_vertices, 2) int64; else None

    def to_json_dict(self) -> dict:
        request = {
            "points": self.points.tolist(),
            "n": self.n_vertices,
            "missing": list(self.missing_edges),
        }
        if self.vertices is not None:
            request["vertices"] = self.vertices.tolist()
        return request


@dataclass(frozen=True)
class FitResult:
    request: FitRequest
    vertices: np.ndarray  # shape (n_vertices, 2), int64, (i, j)
    objective_sq: Fraction | None = None  # F^2, exactly

    @property
    def objective(self) -> float | None:
        """F itself (a float, since F is usually irrational)."""
        return None if self.objective_sq is None else math.sqrt(self.objective_sq)

    def edges(self) -> list[tuple[int, np.ndarray, np.ndarray, bool]]:
        """(edge index, start vertex, end vertex, is_missing) for each edge."""
        n = self.request.n_vertices
        if n == 1:
            return []
        if n == 2:
            return [(0, self.vertices[0], self.vertices[1], False)]
        missing = set(self.request.missing_edges)
        return [
            (e, self.vertices[e], self.vertices[(e + 1) % n], e in missing)
            for e in range(n)
        ]


def _integer_pairs(values, what: str) -> np.ndarray:
    """A (k, 2) int64 array from integer-valued input, or FitInputError."""
    arr = np.asarray(values)
    if arr.ndim == 1 and arr.size == 2:
        arr = arr.reshape(1, 2)
    if arr.ndim != 2 or arr.shape[1] != 2:
        raise FitInputError(f"{what} must have shape (k, 2), got {arr.shape}")
    if not np.issubdtype(arr.dtype, np.integer):
        if not np.all(np.isfinite(arr)) or not np.all(arr == np.round(arr)):
            raise FitInputError(f"{what} must be integer coordinates")
    return arr.astype(np.int64)


def make_request(points, *, n_vertices: int=2, missing_edges=(), vertices=None) -> FitRequest:
    """Validate and normalise user input into a FitRequest.

    Everything after `points` must be passed by keyword, e.g.
    `make_request(pts, n_vertices=4, missing_edges=[3])`.

    Passing `vertices` (n_vertices integer points, negatives allowed) asks the solver
    to score those vertices instead of searching (evaluate mode).

    Only basic shape and range checks happen here. The solver's own checks
    (diam(P) = 0, consecutive missing edges) are left to Lean so they get exercised.
    """
    request = _make_request(points, n_vertices, missing_edges)
    if vertices is None:
        return request
    verts = _integer_pairs(vertices, "vertices")
    if verts.shape[0] != request.n_vertices:
        raise FitInputError(f"need exactly {request.n_vertices} vertices, got {verts.shape[0]}")
    return FitRequest(request.points, request.n_vertices, request.missing_edges, verts)


def _make_request(points, n_vertices: int, missing_edges=()) -> FitRequest:
    pts = _integer_pairs(points, "points")
    if pts.shape[0] == 0:
        raise FitInputError("need at least one point")
    if np.any(pts < 0):
        raise FitInputError("pixel coordinates must be non-negative")

    if isinstance(n_vertices, bool) or int(n_vertices) != n_vertices or n_vertices < 1:
        raise FitInputError(f"n_vertices must be an integer >= 1, got {n_vertices!r}")
    n = int(n_vertices)

    if n <= 2:
        # A point has no edges and a segment has one; missing edges are ignored.
        return FitRequest(points=pts, n_vertices=n, missing_edges=())

    missing = []
    for e in missing_edges:
        if isinstance(e, bool) or int(e) != e:
            raise FitInputError(f"missing edge index must be an integer, got {e!r}")
        if not 0 <= e <= n - 1:
            raise FitInputError(f"missing edge {e} out of range [0, {n - 1}]")
        missing.append(int(e))

    return FitRequest(points=pts, n_vertices=n, missing_edges=tuple(sorted(set(missing))))
