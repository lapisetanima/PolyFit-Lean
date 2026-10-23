"""One completed attempt to fit a polygon to a PointSet's points.

Attempts are made with `PointSet.fit(...)`, which records them in `PointSet.attempts`.
A FitAttempt is frozen once made, and it does not copy the points: it belongs to the
PointSet that holds it. Only successful fits become attempts; a failed fit raises.

An attempt records the pipeline's results (see docs/spec.md):

1. `reduced_hull`: the candidate vertices (the convex hull trimmed to at most 2n),
2. `rough_fits`: the best `k` polygons chosen from those candidates, best first,
3. the final result (`vertices`, `objective_sq`): the fine and ultra-fine local searches
   from the best rough fit. `certified` says whether it is certified: no polygon in the
   unit cube around it has a lower F^2. (Not certified: the search ran out of fuel, or
   n > 7, where the ultra-fine check is skipped.)

How the final result was obtained is recorded in `fine_method`:
- "centre_of_mass": n = 1 (no hull, rough fit or search; the rounded centre of mass is
  optimal),
- "local_search": n >= 2, the fine and ultra-fine searches,
- "mock": the rough geometric baseline in polyfit/mock.py: the most equal-edged polygon
  on the reduced hull (recorded in `reduced_hull`; no rough fit or search), scored with
  its exact F^2 by a Lean query.
"""

from __future__ import annotations

import math
import time
from dataclasses import dataclass
from datetime import datetime
from fractions import Fraction

import numpy as np

from . import bridge
from ._saved import SavedDataError, fraction, fraction_pair, int_pairs, read_only, strict_int, strict_number
from .problem import FitResult, make_request

ENGINES = ("lean", "mock")
FINE_METHODS = ("centre_of_mass", "local_search", "mock")


@dataclass(frozen=True, eq=False)   # eq=False: comparing NumPy arrays with == is ambiguous
class ScoredPolygon:
    vertices: np.ndarray               # (n, 2) int64, read-only
    objective_sq: Fraction             # exact F^2

    def to_dict(self) -> dict:
        return {"vertices": self.vertices.tolist(), "objective_sq": fraction_pair(self.objective_sq)}

    @classmethod
    def from_dict(cls, d: dict) -> ScoredPolygon:
        return cls(int_pairs(d["vertices"]), fraction(d["objective_sq"]))


@dataclass(frozen=True, eq=False)
class FitAttempt:
    """
    FitAttmept records the information obtained from the fitting engine (either the "Lean" or the "Mock" engine)
    """
    n_vertices: int                       # number of vertices the polygon has
    missing_edges: tuple[int, ...]        # as the solver used them: sorted, unique. Empty when n <= 2
    engine: str                           # "lean" or "mock"
    k: int | None                         # number of rough fits kept. None when the request is not for a rough fit
    reduced_hull: np.ndarray | None       # (m, 2) candidate vertices, or None (n = 1)
    rough_fits: tuple[ScoredPolygon, ...] # list of rough_fit candidates, in order of increasing objective function (best is first)
    fine_method: str                      # either fine or ultrafine
    certified: bool | None                # local_search only: a certified local minimum? (certification only if ultrafine)
    vertices: np.ndarray                  # the final result: (n_vertices, 2) int64, read-only
    objective_sq: Fraction | None         # its exact F^2 (None only in mock attempts saved before mock was scored)
    started_at: str                       # local time the attempt started, ISO 8601
    duration_s: float                     # wall-clock seconds, including starting solver processes

    @property
    def objective(self) -> float | None:
        """F itself, as a float (for display)."""
        return None if self.objective_sq is None else math.sqrt(self.objective_sq)

    @property
    def key(self) -> tuple:
        """The characteristics that identify an attempt: two attempts with the same key
        are the same fit, so a PointSet keeps only one."""
        return (self.n_vertices, self.missing_edges, self.engine, self.k)

    def as_result(self, points) -> FitResult:
        """This attempt's fine fit as a FitResult for the given points (for plot_fit)."""
        request = make_request(points, n_vertices=self.n_vertices, missing_edges=self.missing_edges)
        return FitResult(request=request, vertices=np.array(self.vertices), objective_sq=self.objective_sq)

    def outcome(self) -> dict:
        """Everything the attempt computed (all but its timing): replaying the attempt
        must reproduce this exactly."""
        d = self.to_dict()
        del d["started_at"], d["duration_s"]
        return d

    def to_dict(self) -> dict:
        return {
            "n_vertices": self.n_vertices,
            "missing_edges": list(self.missing_edges),
            "engine": self.engine,
            "k": self.k,
            "reduced_hull": None if self.reduced_hull is None else self.reduced_hull.tolist(),
            "rough_fits": [r.to_dict() for r in self.rough_fits],
            "fine_method": self.fine_method,
            "certified": self.certified,
            "vertices": self.vertices.tolist(),
            "objective_sq": None if self.objective_sq is None else fraction_pair(self.objective_sq),
            "started_at": self.started_at,
            "duration_s": self.duration_s,
        }

    @classmethod
    def from_dict(cls, d: dict) -> FitAttempt:
        """Rebuild a saved attempt, checking that it is well formed. (Whether its results
        are right is checked by PointSet.from_dict, which replays it.)"""
        try:
            n = strict_int(d["n_vertices"])
            if n < 1:
                raise ValueError(f"n_vertices must be at least 1, got {n}")
            missing = tuple(strict_int(m) for m in d["missing_edges"])
            if list(missing) != sorted(set(missing)) or any(not 0 <= m < n for m in missing) \
                    or (n <= 2 and missing):
                raise ValueError(f"missing_edges {list(missing)} are not valid for n = {n}")
            engine = d["engine"]
            if engine not in ENGINES:
                raise ValueError(f"unknown engine {engine!r}")
            k = None if d["k"] is None else strict_int(d["k"])
            reduced_hull = None if d["reduced_hull"] is None else int_pairs(d["reduced_hull"])
            if not isinstance(d["rough_fits"], list):
                raise TypeError("rough_fits must be a list")
            rough_fits = tuple(ScoredPolygon.from_dict(r) for r in d["rough_fits"])
            if any(len(r.vertices) != n for r in rough_fits):
                raise ValueError(f"every rough fit must have {n} vertices")
            fine_method = d["fine_method"]
            if fine_method not in FINE_METHODS:
                raise ValueError(f"unknown fine_method {fine_method!r}")
            certified = d["certified"]
            if certified is not None and not isinstance(certified, bool):
                raise TypeError(f"certified must be true, false or null, got {certified!r}")
            if (certified is None) != (fine_method != "local_search"):
                raise ValueError("certified is recorded exactly for local_search results")
            vertices = int_pairs(d["vertices"])
            if len(vertices) != n:
                raise ValueError(f"expected {n} vertices, got {len(vertices)}")
            objective_sq = None if d["objective_sq"] is None else fraction(d["objective_sq"])
            if objective_sq is None and engine != "mock":
                raise ValueError("only mock attempts may lack an objective")
            if objective_sq is not None and objective_sq < 0:
                raise ValueError(f"objective_sq must be >= 0, got {objective_sq}")
            started_at = d["started_at"]
            datetime.fromisoformat(started_at)     # raises if not a valid timestamp
            duration_s = strict_number(d["duration_s"])
            if not duration_s >= 0:
                raise ValueError(f"duration_s must be >= 0, got {duration_s}")
        except (KeyError, TypeError, ValueError, ZeroDivisionError) as err:
            raise SavedDataError(f"not a valid saved FitAttempt: {type(err).__name__}: {err}") from err
        return cls(n, missing, engine, k, reduced_hull, rough_fits, fine_method, certified,
                   vertices, objective_sq, started_at, duration_s)


def normalised_settings(points, *, n_vertices: int, missing_edges=(), engine: str = "lean",
                        k: int = 2) -> tuple:
    """An attempt's key, from the arguments of PointSet.fit: the missing edges as the
    solver uses them, and k only where there is a rough fit (Lean, n >= 2)."""
    if engine not in ENGINES:
        raise ValueError(f"unknown engine {engine!r}")
    request = make_request(points, n_vertices=n_vertices, missing_edges=missing_edges)
    has_rough = engine == "lean" and request.n_vertices >= 2
    return (request.n_vertices, request.missing_edges, engine, k if has_rough else None)


def run_attempt(points, *, n_vertices: int, missing_edges=(), engine: str = "lean", k: int = 2,
                exe=None, timeout: float = 600.0) -> FitAttempt:
    """Run the whole pipeline on `points` and return the completed attempt (not recorded
    anywhere; PointSet.fit does that). A failed step raises FitFailed or FitInputError."""
    n, missing, engine, k = normalised_settings(points, n_vertices=n_vertices, missing_edges=missing_edges,
                                                engine=engine, k=k)
    started_at = datetime.now().astimezone().isoformat(timespec="seconds")
    clock = time.perf_counter()
    reduced_hull, rough_fits, certified = None, (), None
    common = dict(n_vertices=n, missing_edges=missing, exe=exe, timeout=timeout)

    if engine == "mock":
        from .mock import mock_fit
        fine, mock_hull = mock_fit(points, **common)
        reduced_hull = None if mock_hull is None else read_only(mock_hull)
        method = "mock"
    elif n == 1:
        fine = bridge.fit(points, **common)
        method = "centre_of_mass"
    else:
        reduced_hull = read_only(bridge.reduce_hull(points, n_vertices=n, exe=exe, timeout=timeout))
        rough = bridge.rough_fit(points, candidates=reduced_hull, k=k, **common)
        rough_fits = tuple(ScoredPolygon(read_only(r.vertices), r.objective_sq) for r in rough)
        fine, _moves, certified = bridge.fine_fit(points, start=rough_fits[0].vertices, **common)
        method = "local_search"

    return FitAttempt(n, missing, engine, k, reduced_hull, rough_fits, method, certified,
                      read_only(fine.vertices), fine.objective_sq, started_at, time.perf_counter() - clock)
