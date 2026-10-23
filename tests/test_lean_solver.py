"""End-to-end tests against the built Lean executable (skipped if it isn't built)."""

from fractions import Fraction
from itertools import product

import numpy as np
import pytest

from polyfit import FitFailed, evaluate, fit, reduce_hull, reference, rough_fit, samples
from polyfit.bridge import DEFAULT_EXE, run_solver

pytestmark = pytest.mark.skipif(not DEFAULT_EXE.is_file(),
                                reason="Lean solver not built (run `lake build` in lean/)")

TWO_POINTS = [[1, 2], [3, 4]]
DECAGON = [[0, 5], [1, 8], [3, 10], [6, 10], [9, 8], [10, 5], [9, 2], [6, 0], [3, 0], [1, 2]]  # 10 hull vertices


@pytest.mark.parametrize("n", [1, 2, 3, 6])
def test_returns_n_integer_vertices(n):
    result = fit(samples.triangle_outline(), n_vertices=n)
    assert result.vertices.shape == (n, 2)
    assert result.objective_sq is not None and result.objective_sq >= 0


def test_missing_edges_ignored_for_point_and_segment():
    reply, _ = run_solver({"points": TWO_POINTS, "n": 1, "missing": [0, 1, 99]})
    assert reply["error"] == 0
    reply, _ = run_solver({"command": "fine_fit", "points": TWO_POINTS, "n": 2, "missing": [0, 1, 99],
                           "start": TWO_POINTS})
    assert reply["error"] == 0


@pytest.mark.parametrize("n", [2, 3])
def test_lean_fit_command_searches_only_n_1(n):
    """For n >= 2 Python runs the pipeline; Lean's fit command alone is malformed (error 4)."""
    reply, _ = run_solver({"points": DECAGON, "n": n, "missing": []})
    assert reply["error"] == 4


def random_point_sets(count=20, seed=1):
    rng = np.random.default_rng(seed)
    for _ in range(count):
        k = int(rng.integers(2, 30))
        pts = np.unique(rng.integers(0, 40, size=(k, 2)), axis=0)
        if len(pts) >= 2:
            yield pts


POINT_SETS = [make() for name, make in samples.ALL.items() if name != "single_pixel"]
POINT_SETS += list(random_point_sets())


@pytest.mark.parametrize("pts", POINT_SETS)
def test_n1_matches_reference_exactly(pts):
    result = fit(pts, n_vertices=1)
    q = reference.centre_of_mass_rounded(pts)
    assert tuple(result.vertices[0]) == q
    assert result.objective_sq == reference.objective_point(pts, q)


@pytest.mark.parametrize("pts", POINT_SETS[:10])
def test_n1_is_optimal_among_nearby_integer_points(pts):
    result = fit(pts, n_vertices=1)
    qi, qj = result.vertices[0]
    nearby = [reference.objective_point(pts, (qi + di, qj + dj))
              for di in range(-3, 4) for dj in range(-3, 4)]
    assert result.objective_sq == min(nearby)


@pytest.mark.parametrize("pts, expected_q, expected_f2", [
    ([[0, 0], [0, 1]], (0, 1), Fraction(1, 2)),             # centre (0, 0.5) rounds up
    ([[0, 0], [2, 0], [0, 4]], (1, 1), Fraction(7, 30)),     # centre (2/3, 4/3)
    ([[1, 1], [2, 2], [3, 3], [4, 4]], (3, 3), Fraction(1, 6)),  # centre (2.5, 2.5) rounds up
])
def test_n1_hand_checked(pts, expected_q, expected_f2):
    result = fit(pts, n_vertices=1)
    assert tuple(result.vertices[0]) == expected_q
    assert result.objective_sq == expected_f2


def random_segments(count=60, seed=2):
    """(points, q0, q1) cases, with endpoints sometimes outside the points' range."""
    rng = np.random.default_rng(seed)
    cases = []
    while len(cases) < count:
        pts = np.unique(rng.integers(0, 30, size=(int(rng.integers(2, 25)), 2)), axis=0)
        q0, q1 = rng.integers(-10, 40, size=(2, 2))
        if len(pts) >= 2 and not np.array_equal(q0, q1):
            cases.append((pts, q0, q1))
    return cases


@pytest.mark.parametrize("pts, q0, q1", random_segments())
def test_evaluate_segment_matches_reference_exactly(pts, q0, q1):
    result = evaluate(pts, vertices=[q0, q1])
    assert result.objective_sq == reference.objective_segment(pts, q0, q1)


def tie_heavy_segments(count=25, seed=11):
    """Points on a tiny grid (duplicates allowed): many equal crossings and parallel lines."""
    rng = np.random.default_rng(seed)
    cases = []
    while len(cases) < count:
        pts = rng.integers(0, 4, size=(int(rng.integers(2, 9)), 2))
        q0, q1 = rng.integers(-2, 6, size=(2, 2))
        if len({tuple(p) for p in pts}) >= 2 and not np.array_equal(q0, q1):
            cases.append((pts, q0, q1))
    return cases


@pytest.mark.parametrize("pts, q0, q1", tie_heavy_segments())
def test_evaluate_segment_with_ties(pts, q0, q1):
    reply, _ = run_solver({"points": pts.tolist(), "n": 2, "missing": [],
                           "vertices": [q0.tolist(), q1.tolist()]})
    assert Fraction(*reply["objective_function"]) == reference.objective_segment(pts, q0, q1)


@pytest.mark.parametrize("pts, q0, q1", random_segments(count=10, seed=5))
def test_evaluate_segment_symmetric_in_endpoints(pts, q0, q1):
    assert evaluate(pts, vertices=[q0, q1]).objective_sq == evaluate(pts, vertices=[q1, q0]).objective_sq


@pytest.mark.parametrize("pts, verts, expected", [
    # Segment exactly through both points: D1 = 0, integral = 1/3, L^2 = 4.
    ([[0, 0], [0, 2]], [[0, 0], [0, 2]], Fraction(1, 24)),
    # n = 1 at the midpoint: (1 + 1) / (2 * 4).
    ([[0, 0], [0, 2]], [[0, 1]], Fraction(1, 4)),
])
def test_evaluate_hand_checked(pts, verts, expected):
    assert evaluate(pts, vertices=verts).objective_sq == expected


@pytest.mark.parametrize("pts", POINT_SETS[:10])
def test_evaluate_point_matches_fit(pts):
    fitted = fit(pts, n_vertices=1)
    assert evaluate(pts, vertices=fitted.vertices).objective_sq == fitted.objective_sq


SEGMENT_FIT_SETS = [samples.noisy_segment(), samples.noisy_segment(keep=1.0),
                    samples.triangle_outline(), samples.blob(keep=1.0)]


@pytest.mark.parametrize("pts", SEGMENT_FIT_SETS)
def test_segment_fit_is_exact_and_locally_optimal(pts):
    """F^2 agrees with the reference, and none of the 80 step-1 moves improves it."""
    result = fit(pts, n_vertices=2)
    q0, q1 = result.vertices
    assert result.objective_sq == reference.objective_segment(pts, q0, q1)
    offsets = [np.array(d) for d in product([-1, 0, 1], repeat=2)]
    for d0 in offsets:
        for d1 in offsets:
            if d0.any() or d1.any():
                assert reference.objective_segment(pts, q0 + d0, q1 + d1) >= result.objective_sq


@pytest.mark.parametrize("pts", SEGMENT_FIT_SETS)
def test_segment_fit_improves_on_its_rough_start(pts):
    best_rough = rough_fit(pts, n_vertices=2, candidates=reduce_hull(pts, n_vertices=2), k=1)[0]
    assert fit(pts, n_vertices=2).objective_sq <= best_rough.objective_sq


def test_segment_fit_recovers_dense_straight_line():
    line = [[i, 3] for i in range(11)]
    assert sorted(fit(line, n_vertices=2).vertices.tolist()) == [[0, 3], [10, 3]]


def test_segment_overshoots_sparse_points_by_half_the_gap():
    """With gap g between collinear points the optimum overshoots by about g/2 at each end."""
    result = fit([[0, 3], [5, 3], [10, 3]], n_vertices=2)
    assert sorted(result.vertices.tolist()) == [[-3, 3], [13, 3]]


def test_evaluate_zero_length_segment_is_error_3():
    with pytest.raises(FitFailed) as info:
        evaluate([[0, 0], [0, 2]], vertices=[[1, 1], [1, 1]])
    assert info.value.code == 3


def test_evaluate_polygon_matches_reference():
    pts, verts = [[0, 0], [0, 2]], [(0, 0), (0, 2), (5, 5)]
    assert evaluate(pts, vertices=verts).objective_sq == reference.objective_polygon(pts, verts)


def test_error_1_zero_diameter():
    with pytest.raises(FitFailed) as info:
        fit(samples.single_pixel(), n_vertices=1)
    assert info.value.code == 1


@pytest.mark.parametrize("n, missing", [(4, [0, 1]), (4, [3, 0]), (3, [0, 2]), (6, [1, 3, 4])])
def test_error_2_consecutive_missing(n, missing):
    with pytest.raises(FitFailed) as info:
        fit(DECAGON, n_vertices=n, missing_edges=missing)
    assert info.value.code == 2


def test_non_consecutive_missing_ok():
    assert fit(DECAGON, n_vertices=6, missing_edges=[0, 2, 4]).vertices.shape == (6, 2)


@pytest.mark.parametrize("request_json", [
    {"points": [], "n": 3, "missing": []},
    {"points": [[1, -2], [3, 4]], "n": 3, "missing": []},
    {"points": [[1, 2.5], [3, 4]], "n": 3, "missing": []},
    {"points": TWO_POINTS, "n": 0, "missing": []},
    {"points": TWO_POINTS, "n": 3, "missing": [3]},
    {"points": TWO_POINTS, "n": 3},
    {"points": TWO_POINTS, "n": 2, "missing": [], "vertices": [[0, 0]]},
    {"points": TWO_POINTS, "n": 2, "missing": [], "vertices": [[0, 0], [1, 1.5]]},
])
def test_error_4_malformed(request_json):
    reply, stderr = run_solver(request_json)
    assert reply == {"error": 4, "objective_function": None, "poly_points": None}
    assert "malformed" in stderr
