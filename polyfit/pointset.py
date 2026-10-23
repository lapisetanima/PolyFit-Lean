"""A set of points: its fixed properties, and the record of every fit attempted on it.

The fixed properties (centre of mass, diameter, radii, convex hull) are computed once
by the Lean `describe` command and never change. All lengths are recorded squared and
exact (as Fractions or ints); the float properties are for convenience only.

`attempts` is the one part that grows: `PointSet.fit(...)` runs the fitting pipeline
(reduced hull, rough fits, fine fit; see attempt.py) and appends the completed (frozen)
FitAttempt, unless an attempt with the same characteristics is already recorded, in
which case that one is reused and nothing runs. A failed fit raises and records
nothing; by our policy that ends the work on this point set (see `attempt_fits`).
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction

import numpy as np

from ._saved import (SavedDataError, fraction, fraction_pair, int_pairs, read_only,
                     strict_int)
from .attempt import FitAttempt, normalised_settings, run_attempt
from .bridge import FitFailed, SolverError, run_solver
from .problem import FitInputError, _integer_pairs

FIXED_FIELDS = ("points", "com", "diam_sq", "inner_radius_sq", "outer_radius_sq", "hull")


def build_point_sets(named_points: dict, exe=None) -> tuple[dict, dict]:
    """Build a PointSet for each named array of points.

    Returns (point_sets, failures). point_sets maps name -> PointSet for every set that
    could be built, in the input order. failures maps name -> the exception for every
    set that could not (too few distinct points, bad coordinates, ...); those sets are
    simply left out of point_sets. A missing Lean executable (SolverError) is raised
    rather than collected, since it would make every set fail.
    """
    point_sets, failures = {}, {}
    for name, pts in named_points.items():
        try:
            point_sets[name] = PointSet.from_points(pts, exe=exe)
        except (FitInputError, FitFailed) as err:
            failures[name] = err
    return point_sets, failures


def attempt_fits(point_sets: dict, plans: dict, exe=None) -> dict:
    """Run the planned fits on each point set, recording them in its `attempts`.

    `plans` maps a point set's name to a list of keyword-argument dicts for
    PointSet.fit, run in order, e.g. {"blob": [dict(n_vertices=2), dict(n_vertices=3)]}.
    The first failed fit on a point set stops the work on that set; the other sets
    carry on. Fits already recorded are reused, not rerun, so running the same plans
    again changes nothing. Returns {name: exception} for the point sets that were stopped.
    A missing Lean executable (SolverError) is raised, since every fit would fail.
    """
    stopped = {}
    for name, ps in point_sets.items():
        for kwargs in plans.get(name, []):
            try:
                ps.fit(exe=exe, **kwargs)
            except (FitInputError, FitFailed) as err:
                stopped[name] = err
                break
    return stopped


@dataclass(frozen=True)
class PointSet:
    points: np.ndarray                 # (k, 2) int64, distinct, read-only
    com: tuple[Fraction, Fraction]     # centre of mass (i, j), exact
    diam_sq: int                       # diam(P)^2
    inner_radius_sq: Fraction          # min |p - com|^2 (may be 0)
    outer_radius_sq: Fraction          # max |p - com|^2
    hull: np.ndarray                   # (h, 2) convex hull vertices, counterclockwise on screen
    attempts: list = field(default_factory=list, compare=False, repr=False)  # FitAttempts, in order

    @classmethod
    def from_points(cls, points, exe=None) -> PointSet:
        """Validate the points, drop duplicates (keeping first occurrences), and ask Lean
        to describe them. Needs at least 2 distinct non-negative integer points."""
        pts = _integer_pairs(points, "points")
        if np.any(pts < 0):
            raise FitInputError("pixel coordinates must be non-negative")
        _, first = np.unique(pts, axis=0, return_index=True)
        pts = pts[np.sort(first)]
        if len(pts) < 2:
            raise FitInputError(f"need at least 2 distinct points, got {len(pts)}")

        reply, stderr = run_solver({"command": "describe", "points": pts.tolist()}, exe=exe)
        code = reply.get("error")
        if code != 0:
            raise FitFailed(code, stderr) if isinstance(code, int) else SolverError(repr(reply))
        return cls(
            points=read_only(pts),
            com=(fraction(reply["com"][0]), fraction(reply["com"][1])),
            diam_sq=int(reply["diam_sq"]),
            inner_radius_sq=fraction(reply["inner_radius_sq"]),
            outer_radius_sq=fraction(reply["outer_radius_sq"]),
            hull=read_only(reply["hull"]),
        )

    def find_attempt(self, *, n_vertices: int, missing_edges=(), engine: str = "lean",
                     k: int = 2) -> FitAttempt | None:
        """The recorded attempt with these characteristics, or None. The missing edges
        are compared as the solver uses them (sorted, duplicates removed, and ignored
        for n <= 2), so [3, 1, 3] matches [1, 3]; k counts only where there is a rough
        fit (Lean, n >= 2)."""
        key = normalised_settings(self.points, n_vertices=n_vertices, missing_edges=missing_edges,
                                  engine=engine, k=k)
        return next((a for a in self.attempts if a.key == key), None)

    def fit(self, *, n_vertices: int, missing_edges=(), engine: str = "lean", k: int = 2,
            exe=None, timeout: float = 600.0) -> FitAttempt:
        """Fit a polygon to these points through the pipeline (reduced hull, the best k
        rough fits, fine fit; see FitAttempt), record the attempt in `self.attempts`,
        and return it. If an attempt with the same characteristics (see `find_attempt`)
        is already recorded, nothing runs and that attempt is returned instead.
        A failed step raises (FitFailed or FitInputError) and records nothing."""
        existing = self.find_attempt(n_vertices=n_vertices, missing_edges=missing_edges,
                                     engine=engine, k=k)
        if existing is not None:
            return existing
        attempt = run_attempt(self.points, n_vertices=n_vertices, missing_edges=missing_edges,
                              engine=engine, k=k, exe=exe, timeout=timeout)
        self.attempts.append(attempt)
        return attempt

    # Floats, for display.
    @property
    def diameter(self) -> float:
        return math.sqrt(self.diam_sq)

    @property
    def inner_radius(self) -> float:
        return math.sqrt(self.inner_radius_sq)

    @property
    def outer_radius(self) -> float:
        return math.sqrt(self.outer_radius_sq)

    # Saving and loading: fractions as [numerator, denominator].
    def to_dict(self) -> dict:
        return {
            "points": self.points.tolist(),
            "com": [fraction_pair(self.com[0]), fraction_pair(self.com[1])],
            "diam_sq": self.diam_sq,
            "inner_radius_sq": fraction_pair(self.inner_radius_sq),
            "outer_radius_sq": fraction_pair(self.outer_radius_sq),
            "hull": self.hull.tolist(),
            "attempts": [a.to_dict() for a in self.attempts],
        }

    @classmethod
    def from_dict(cls, d: dict, verify: bool = True, exe=None) -> PointSet:
        """Rebuild a saved PointSet, with its attempts.

        Raises SavedDataError if the dictionary is malformed (a missing key, a
        non-integer coordinate, a zero denominator, a bad attempt, ...). With
        verify=True (the default) it also recomputes the fixed fields from the saved
        points with Lean's `describe`, and replays every attempt (every step is
        deterministic) to check that its reduced hull, rough fits and fine fit are
        exactly what was saved; it raises SavedDataError if anything differs.
        verify=False skips those checks (and the Lean calls). A dictionary without
        "attempts" (saved before attempts existed) loads with no attempts.
        """
        try:
            com_i, com_j = d["com"]
            attempts = d.get("attempts", [])
            if not isinstance(attempts, list):
                raise TypeError(f"attempts must be a list, got {type(attempts).__name__}")
            ps = cls(
                points=int_pairs(d["points"], min_rows=2),
                com=(fraction(com_i), fraction(com_j)),
                diam_sq=strict_int(d["diam_sq"]),
                inner_radius_sq=fraction(d["inner_radius_sq"]),
                outer_radius_sq=fraction(d["outer_radius_sq"]),
                hull=int_pairs(d["hull"], min_rows=2),
                attempts=[FitAttempt.from_dict(a) for a in attempts],
            )
            keys = [a.key for a in ps.attempts]
            if len(set(keys)) != len(keys):
                raise ValueError("two attempts have the same characteristics (n, missing edges, engine, k)")
        except SavedDataError:
            raise
        except (KeyError, TypeError, ValueError, ZeroDivisionError) as err:
            raise SavedDataError(f"not a valid saved PointSet: {type(err).__name__}: {err}") from err

        if verify:
            ps._verify(exe)
        return ps

    def _verify(self, exe=None) -> None:
        """Check every recorded value against Lean (see from_dict)."""
        try:
            fresh = PointSet.from_points(self.points, exe=exe)
        except FitInputError as err:
            raise SavedDataError(f"the saved points are invalid: {err}") from err
        saved, recomputed = self.to_dict(), fresh.to_dict()
        wrong = [key for key in FIXED_FIELDS if saved[key] != recomputed[key]]
        if wrong:
            raise SavedDataError(f"the saved PointSet disagrees with its points in: {', '.join(wrong)}")

        for idx, a in enumerate(self.attempts):
            try:
                replay = run_attempt(self.points, n_vertices=a.n_vertices, missing_edges=a.missing_edges,
                                     engine=a.engine, k=a.k if a.k is not None else 2, exe=exe)
            except (FitFailed, FitInputError) as err:
                raise SavedDataError(f"attempt {idx} cannot be replayed: {err}") from err
            saved, again = a.outcome(), replay.outcome()
            wrong = [key for key in saved if saved[key] != again[key]]
            if wrong:
                raise SavedDataError(f"attempt {idx} disagrees with a replay in: {', '.join(wrong)}")
