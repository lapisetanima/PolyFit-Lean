"""The mock engine: the most equal-edged polygon on the reduced hull, scored by Lean."""

from itertools import combinations

import numpy as np
import pytest

from polyfit import FitFailed, PointSet, evaluate, fit, reduce_hull, samples
from polyfit.bridge import DEFAULT_EXE
from polyfit.mock import edge_spread

pytestmark = pytest.mark.skipif(not DEFAULT_EXE.is_file(),
                                reason="Lean solver not built (run `lake build` in lean/)")

SETS = [make(keep=keep) for name, make in samples.ALL.items() if name != "single_pixel" for keep in (0.25, 1.0)]


def hull_order_positions(cands, verts):
    rows = [tuple(c) for c in cands.tolist()]
    return [rows.index(tuple(v)) for v in verts.tolist()]


@pytest.mark.parametrize("pts", SETS)
@pytest.mark.parametrize("n", [3, 4, 5])
def test_mock_is_the_most_equal_edged_hull_polygon(pts, n):
    cands = reduce_hull(pts, n_vertices=n) if len(PointSet.from_points(pts).hull) >= n else None
    if cands is None:
        with pytest.raises(FitFailed) as info:
            fit(pts, n_vertices=n, engine="mock")
        assert info.value.code == 5
        return
    result = fit(pts, n_vertices=n, engine="mock")
    positions = hull_order_positions(cands, result.vertices)
    assert positions == sorted(positions)                       # vertices in hull order: convex
    best = min(edge_spread(cands[list(s)]) for s in combinations(range(len(cands)), n))
    assert edge_spread(result.vertices) == best
    assert result.objective_sq == evaluate(pts, vertices=result.vertices).objective_sq


@pytest.mark.parametrize("pts", SETS)
def test_mock_segment_is_the_farthest_pair_of_candidates(pts):
    cands = reduce_hull(pts, n_vertices=2)
    result = fit(pts, n_vertices=2, engine="mock")
    a, b = result.vertices
    assert int(((a - b) ** 2).sum()) == max(int(((p - q) ** 2).sum()) for p, q in combinations(cands, 2))


def test_mock_point_is_the_rounded_centre_of_mass():
    pts = samples.blob()
    result = fit(pts, n_vertices=1, engine="mock")
    assert result.vertices.tolist() == [np.round(np.asarray(pts).mean(axis=0)).astype(int).tolist()]
    assert result.objective_sq is not None


def test_equal_edged_square_is_preferred():
    # A square's corners plus one extra hull point near a corner: the square has spread 0.
    pts = [[2, 2], [2, 12], [12, 12], [12, 2], [3, 1]]
    result = fit(pts, n_vertices=4, engine="mock")
    assert sorted(result.vertices.tolist()) == [[2, 2], [2, 12], [12, 2], [12, 12]]
    assert edge_spread(result.vertices) == 0.0


def test_spread_ignores_size():
    tri = np.array([[0, 0], [3, 0], [0, 4]])
    assert edge_spread(tri) == pytest.approx(edge_spread(10 * tri))


def test_mock_with_missing_edges_scores_present_edges_only():
    pts = samples.square_missing_edge()
    result = fit(pts, n_vertices=4, missing_edges=[2], engine="mock")
    assert result.objective_sq == evaluate(pts, vertices=result.vertices, missing_edges=[2]).objective_sq
