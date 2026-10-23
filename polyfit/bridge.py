"""Talk to the Lean solver executable over stdin/stdout JSON.

Request (one JSON object on stdin):
    {"points": [[i, j], ...], "n": <int >= 1>, "missing": [<edge index>, ...]}

Reply (one JSON object on stdout):
    {"error": 0, "objective_function": [a, b], "poly_points": [[i, j], ...]}
    {"error": <code>, "objective_function": null, "poly_points": null}

where F^2 = a / b exactly. On an error the solver also explains itself on stderr.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

from .problem import FitRequest, FitResult, _integer_pairs, make_request

REPO_ROOT = Path(__file__).resolve().parent.parent
_EXE_NAME = "polyfit.exe" if sys.platform == "win32" else "polyfit"
DEFAULT_EXE = REPO_ROOT / "lean" / ".lake" / "build" / "bin" / _EXE_NAME

ERROR_CODES = {
    1: "diam(P) = 0: all points coincide",
    2: "two cyclically consecutive edges are both missing",
    3: "the best fit found has an edge of length 0",
    4: "malformed input",
    5: "not enough candidate vertices (for example, a convex hull with fewer than n vertices)",
}


class SolverError(RuntimeError):
    """The solver could not be run, or returned something unusable."""


class FitFailed(SolverError):
    """The solver ran and reported an error code (1-5)."""

    def __init__(self, code: int, detail: str = ""):
        self.code = code
        self.detail = detail.strip()
        message = f"solver error {code}: {ERROR_CODES.get(code, 'unknown error')}"
        if self.detail:
            message += f"\n{self.detail}"
        super().__init__(message)


def find_executable(exe: str | os.PathLike | None = None) -> Path:
    """Explicit argument, then $POLYFIT_LEAN_EXE, then the Lake build output."""
    path = Path(exe or os.environ.get("POLYFIT_LEAN_EXE") or DEFAULT_EXE)
    if not path.is_file():
        raise SolverError(
            f"Lean solver not found at {path}. Build it with `lake build` in the "
            "lean/ folder, or set POLYFIT_LEAN_EXE."
        )
    return path


def run_solver(request_json: dict, exe=None, timeout: float = 60.0) -> tuple[dict, str]:
    """
        run_solver is how Python talks to the Lean engine. One request is sent, with instructions in request_json.
        
        "request_json" contains the "command" and any necessary data (such as the rough-fit polygon if the command is to find a fine fit)

        returns: parsed reply, stderr text
        "parsed reply" is some JSON with any error code, along with the requested information (a rough fit, a fine fit, a query, etc)
        "stderr text" is a human-readable error description, if there is any error
    """
    path = find_executable(exe)
    try:
        proc = subprocess.run(
            [str(path)],
            input=json.dumps(request_json),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as err:
        raise SolverError(f"solver timed out after {timeout} s") from err

    if proc.returncode != 0:
        raise SolverError(f"solver crashed with exit code {proc.returncode}:\n{proc.stderr}")
    try:
        return json.loads(proc.stdout), proc.stderr
    except json.JSONDecodeError as err:
        raise SolverError(f"solver output is not JSON:\n{proc.stdout!r}") from err


def solve_request(request: FitRequest, exe=None, timeout: float = 60.0) -> FitResult:
    reply, stderr = run_solver(request.to_json_dict(), exe=exe, timeout=timeout)
    return parse_reply(request, reply, stderr)


def parse_reply(request: FitRequest, reply: dict, stderr: str = "") -> FitResult:
    code = reply.get("error")
    if not isinstance(code, int):
        raise SolverError(f"reply has no integer error code: {reply!r}")
    if code != 0:
        raise FitFailed(code, stderr)

    vertices = np.asarray(reply.get("poly_points"))
    if vertices.shape != (request.n_vertices, 2) or not np.issubdtype(vertices.dtype, np.integer):
        raise SolverError(
            f"expected {request.n_vertices} integer [i, j] vertices, got {reply.get('poly_points')!r}"
        )

    objective = reply.get("objective_function")
    if objective is None:
        objective_sq = None  # only the mock solver omits the objective
    else:
        try:
            a, b = objective
            objective_sq = Fraction(int(a), int(b))
        except (TypeError, ValueError, ZeroDivisionError) as err:
            raise SolverError(f"objective_function must be [a, b] with b != 0, got {objective!r}") from err

    return FitResult(request=request, vertices=vertices.astype(np.int64), objective_sq=objective_sq)


def fit(points, *, n_vertices: int, missing_edges=(), engine: str = "lean",
        exe=None, timeout: float = 60.0) -> FitResult:
    """
    Fit a polygon with `n_vertices` vertices to `points`.

    engine="lean" runs the Lean executable; engine="mock" uses the rough geometric baseline in
    polyfit.mock (the most equal-edged polygon on the reduced hull, scored by a Lean query).
    
    Raises FitFailed if the solver reports an error code.
    """
    request = make_request(points, n_vertices=n_vertices, missing_edges=missing_edges)
    if engine == "lean":
        return solve_request(request, exe=exe, timeout=timeout)
    if engine == "mock":
        from .mock import solve_mock
        return solve_mock(request, exe=exe, timeout=timeout)
    raise ValueError(f"unknown engine {engine!r}")


def _checked(reply: dict, stderr: str) -> dict:
    """The reply itself, or FitFailed / SolverError if it reports an error."""
    code = reply.get("error")
    if not isinstance(code, int):
        raise SolverError(f"reply has no integer error code: {reply!r}")
    if code != 0:
        raise FitFailed(code, stderr)
    return reply


def reduce_hull(points, *, n_vertices: int, exe=None, timeout: float = 60.0) -> np.ndarray:
    """The convex hull of `points`, trimmed to at most 2n candidate vertices with
    Visvalingam-Whyatt (all of them if it has between n and 2n). Raises FitFailed with
    code 5 if the hull has fewer than n vertices."""
    request = make_request(points, n_vertices=n_vertices)
    reply, stderr = run_solver({"command": "reduce_hull", "points": request.points.tolist(),
                                "n": request.n_vertices}, exe=exe, timeout=timeout)
    return np.asarray(_checked(reply, stderr)["candidates"], dtype=np.int64).reshape(-1, 2)


def rough_fit(points, *, n_vertices: int, missing_edges=(), candidates, k: int = 2,
              exe=None, timeout: float = 60.0) -> list[FitResult]:
    """The best `k` polygons whose `n_vertices` vertices are chosen, in cyclic order,
    from `candidates` (with every labelling tried when edges are missing), best first,
    each with its exact F^2."""
    request = make_request(points, n_vertices=n_vertices, missing_edges=missing_edges)
    cands = _integer_pairs(candidates, "candidates")
    reply, stderr = run_solver({**request.to_json_dict(), "command": "rough_fit",
                                "candidates": cands.tolist(), "k": k}, exe=exe, timeout=timeout)
    results = []
    for entry in _checked(reply, stderr)["rough_fits"]:
        results.append(parse_reply(request, {"error": 0, **entry}))
    return results


def fine_fit(points, *, n_vertices: int, missing_edges=(), start, exe=None,
             timeout: float = 600.0) -> tuple[FitResult, int, bool]:
    """The fine and ultra-fine local searches, starting from the polygon `start`
    (n >= 2). Returns (result, number of accepted moves, certified). certified is True
    when no polygon in the unit cube around the result (every vertex moved by at most
    1 in each coordinate) has a lower F^2; it is False if the search ran out of fuel,
    or if n > 7 (the ultra-fine check is skipped)."""
    request = make_request(points, n_vertices=n_vertices, missing_edges=missing_edges)
    start = _integer_pairs(start, "start")
    reply, stderr = run_solver({**request.to_json_dict(), "command": "fine_fit", "start": start.tolist()},
                               exe=exe, timeout=timeout)
    reply = _checked(reply, stderr)
    moves, certified = reply.get("moves"), reply.get("certified")
    if not isinstance(moves, int) or not isinstance(certified, bool):
        raise SolverError(f"fine_fit reply lacks moves/certified: {reply!r}")
    return parse_reply(request, reply), moves, certified


def evaluate(points, *, vertices, missing_edges=(), exe=None, timeout: float = 60.0) -> FitResult:
    """Score the given polygon (no search): the result's objective_sq is its exact F^2.

    Everything after `points` must be passed by keyword, e.g.
    `evaluate(pts, vertices=[[0, 0], [5, 5]])`. The number of vertices sets n.
    Raises FitFailed with code 3 for a zero-length edge.
    """
    vertices = np.asarray(vertices)
    request = make_request(points, n_vertices=len(vertices), missing_edges=missing_edges,
                           vertices=vertices)
    return solve_request(request, exe=exe, timeout=timeout)
