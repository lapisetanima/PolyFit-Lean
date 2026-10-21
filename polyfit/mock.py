"""Placeholder solver in pure Python.

This does NOT optimise any objective. It exists only so the plotting and the
request/response plumbing can be exercised without the Lean solver. Its reply
uses the same format as the Lean solver's (with no objective) and goes through
the same parser.
"""

from __future__ import annotations

import numpy as np

from .bridge import parse_reply
from .problem import FitRequest, FitResult


def solve_mock(request: FitRequest) -> FitResult:
    pts = request.points.astype(np.float64)
    n = request.n_vertices
    centre = pts.mean(axis=0)

    if n == 1:
        vertices = centre[None, :]
    elif n == 2:
        # Endpoints of the points' extent along their principal direction.
        centred = pts - centre
        _, _, vt = np.linalg.svd(centred, full_matrices=False)
        direction = vt[0]
        t = centred @ direction
        vertices = np.array([centre + t.min() * direction, centre + t.max() * direction])
    else:
        # Regular n-gon around the centroid, sized by the RMS distance.
        radius = max(np.sqrt(np.mean(np.sum((pts - centre) ** 2, axis=1))), 0.5)
        angles = np.pi / 2 + 2 * np.pi * np.arange(n) / n
        vertices = centre + radius * np.column_stack([np.sin(angles), np.cos(angles)])

    reply = {
        "error": 0,
        "objective_function": None,
        "poly_points": np.round(vertices).astype(int).tolist(),
    }
    return parse_reply(request, reply)
