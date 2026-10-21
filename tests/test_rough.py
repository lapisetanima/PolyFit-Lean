"""Polygon F^2, hull trimming (reduce_hull) and the rough fit, against brute-force references."""

import time
from fractions import Fraction
from itertools import combinations

import numpy as np
import pytest

from polyfit import FitFailed, PointSet, evaluate, reduce_hull, reference, rough_fit, samples
from polyfit.bridge import DEFAULT_EXE, run_solver

pytestmark = pytest.mark.skipif(not DEFAULT_EXE.is_file(),
                                reason="Lean solver not built (run `lake build` in lean/)")


def valid_missing(n, rng):
    """A random set of missing edges with no two cyclically consecutive."""
    missing = []
    for e in rng.permutation(n):
        if len(missing) < n // 2 and all((e - m) % n not in (1, n - 1) for m in missing):
            if rng.random() < 0.4:
                missing.append(int(e))
    return sorted(missing)


def random_polygons(count=40, seed=7):
    rng = np.random.default_rng(seed)
    cases = []
    while len(cases) < count:
        pts = np.unique(rng.integers(0, 25, size=(int(rng.integers(3, 25)), 2)), axis=0)
        n = int(rng.integers(3, 7))
        verts = rng.integers(-5, 30, size=(n, 2))
        if len(pts) >= 2 and all(not np.array_equal(verts[e], verts[(e + 1) % n]) for e in range(n)):
            cases.append((pts, verts, valid_missing(n, rng)))
    return cases


# --- polygon F^2 ------------------------------------------------------------------

@pytest.mark.parametrize("pts, verts, missing", random_polygons())
def test_evaluate_polygon_matches_reference(pts, verts, missing):
    result = evaluate(pts, vertices=verts, missing_edges=missing)
    assert result.objective_sq == reference.objective_polygon(pts, [tuple(v) for v in verts], missing)


def test_square_with_points_at_corners():
    square = [[0, 0], [0, 4], [4, 4], [4, 0]]
    assert evaluate(square, vertices=square).objective_sq == Fraction(1, 24)
    assert evaluate(square, vertices=square, missing_edges=[1]).objective_sq == Fraction(1, 24)


def test_polygon_with_zero_length_edge_is_error_3():
    with pytest.raises(FitFailed) as info:
        evaluate([[0, 0], [0, 4], [4, 4]], vertices=[[0, 0], [0, 4], [0, 4]])
    assert info.value.code == 3


# --- reduce_hull --------------------------------------------------------------------

def hull_cases():
    sets = [make(keep=1.0) for name, make in samples.ALL.items() if name != "single_pixel"]
    rng = np.random.default_rng(8)
    sets += [np.unique(rng.integers(0, 20, size=(int(rng.integers(3, 40)), 2)), axis=0) for _ in range(15)]
    return [(pts, n) for pts in sets for n in (2, 3, 4, 6)]


@pytest.mark.parametrize("pts, n", hull_cases())
def test_reduce_hull_matches_reference(pts, n):
    expected = reference.reduce_hull(pts, n)
    if expected is None:
        with pytest.raises(FitFailed) as info:
            reduce_hull(pts, n_vertices=n)
        assert info.value.code == 5
    else:
        got = reduce_hull(pts, n_vertices=n)
        assert [tuple(v) for v in got.tolist()] == expected
        assert n <= len(got) <= 2 * n


def test_reduce_hull_keeps_hull_order_and_drops_flattest_vertices():
    ps = PointSet.from_points(samples.hexagon_outline(keep=1.0))
    hull = [tuple(v) for v in ps.hull.tolist()]
    reduced = [tuple(v) for v in reduce_hull(ps.points, n_vertices=3).tolist()]
    assert len(hull) > 6 and len(reduced) == 6
    positions = [hull.index(v) for v in reduced]
    assert positions == sorted(positions)          # a subsequence of the hull, same order


def test_reduce_hull_error_5_for_collinear_points():
    with pytest.raises(FitFailed) as info:
        reduce_hull([[0, 0], [1, 1], [2, 2], [4, 4]], n_vertices=3)
    assert info.value.code == 5


# --- rough_fit ----------------------------------------------------------------------

def rough_cases(count=30, seed=9):
    rng = np.random.default_rng(seed)
    cases = []
    while len(cases) < count:
        pts = np.unique(rng.integers(0, 20, size=(int(rng.integers(4, 15)), 2)), axis=0)
        n = int(rng.integers(2, 6))
        m = int(rng.integers(n, min(2 * n, 8) + 1))
        cands = np.unique(rng.integers(-3, 23, size=(m, 2)), axis=0)
        rng.shuffle(cands)
        if len(pts) >= 2 and len(cands) >= n:
            cases.append((pts, n, valid_missing(n, rng) if n >= 3 else [], cands, int(rng.integers(1, 5))))
    return cases


@pytest.mark.parametrize("pts, n, missing, cands, k", rough_cases())
def test_rough_fit_matches_brute_force(pts, n, missing, cands, k):
    got = rough_fit(pts, n_vertices=n, missing_edges=missing, candidates=cands, k=k)
    expected = reference.rough_fit(pts, n, missing, cands.tolist(), k)
    assert [(r.vertices.tolist(), r.objective_sq) for r in got] == expected


def test_rough_fit_puts_the_missing_edge_on_the_empty_side():
    # Points on three sides of a square; its left side (j = 0) is empty.
    u_shape = [[0, 0], [0, 2], [0, 4], [2, 4], [4, 4], [4, 2], [4, 0]]
    corners = [[0, 4], [0, 0], [4, 0], [4, 4]]
    best = rough_fit(u_shape, n_vertices=4, missing_edges=[2], candidates=corners, k=1)[0]
    q = best.vertices.tolist()
    assert sorted([q[2], q[3]]) == [[0, 0], [4, 0]]         # missing edge 2 joins q2 and q3
    assert best.objective_sq == Fraction(1, 96)


def test_rough_fit_returns_distinct_polygons():
    # n = 4 with edges 0 and 2 missing: rotating the labels by 2 gives the same polygon.
    corners = [[0, 4], [0, 0], [4, 0], [4, 4]]
    fits = rough_fit(corners, n_vertices=4, missing_edges=[0, 2], candidates=corners, k=10)
    assert len(fits) == 2                                   # 4 rotations, 2 distinct polygons
    keys = {frozenset(map(tuple, map(sorted, [[tuple(f.vertices[1]), tuple(f.vertices[2])],
                                              [tuple(f.vertices[3]), tuple(f.vertices[0])]]))) for f in fits}
    assert len(keys) == 2


def test_rough_fit_errors():
    pts = samples.triangle_outline()
    with pytest.raises(FitFailed) as info:
        rough_fit(pts, n_vertices=4, candidates=[[0, 0], [5, 5], [9, 0]])
    assert info.value.code == 5
    for bad in [dict(n=1, candidates=[[0, 0], [5, 5]]),
                dict(n=3, candidates=[[0, 0], [5, 5], [0, 0]]),     # not distinct
                dict(n=3, candidates=[[0, 0], [5, 5], [9, 0]], k=0)]:
        reply, _ = run_solver({"command": "rough_fit", "points": pts.tolist(), "missing": [], **bad})
        assert reply["error"] == 4


def test_rough_fit_hexagon_with_missing_edges_is_fast():
    """n = 6 on 12 candidates with edges missing: 6 * C(12, 6) = 5544 polygons."""
    pts = samples.hexagon_outline(keep=1.0)
    cands = reduce_hull(pts, n_vertices=6)
    assert len(cands) == 12
    start = time.perf_counter()
    fits = rough_fit(pts, n_vertices=6, missing_edges=[0, 3], candidates=cands, k=2)
    assert len(fits) == 2 and fits[0].objective_sq <= fits[1].objective_sq
    assert time.perf_counter() - start < 30
