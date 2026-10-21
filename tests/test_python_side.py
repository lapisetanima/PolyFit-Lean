import json
from fractions import Fraction

import matplotlib

matplotlib.use("Agg")

import numpy as np
import pytest

from polyfit import FitFailed, FitInputError, SolverError, fit, make_request
from polyfit import samples
from polyfit.bridge import parse_reply
from polyfit.plotting import plot_fit


def test_request_normalises_input():
    req = make_request([[1, 2], [3, 4]], n_vertices=4, missing_edges=[3, 1, 3])
    assert req.points.dtype == np.int64
    assert req.missing_edges == (1, 3)
    assert json.loads(json.dumps(req.to_json_dict())) == {
        "points": [[1, 2], [3, 4]], "n": 4, "missing": [1, 3]}


def test_single_point_accepts_flat_pair():
    assert make_request([5, 7], n_vertices=1).points.shape == (1, 2)


@pytest.mark.parametrize("points, n, missing", [
    ([], 3, ()),
    ([[1, 2, 3]], 3, ()),
    ([[1.5, 2]], 3, ()),
    ([[-1, 2]], 3, ()),
    ([[1, 2]], 0, ()),
    ([[1, 2]], 3, (3,)),
    ([[1, 2]], 3, (-1,)),
])
def test_bad_requests_rejected(points, n, missing):
    with pytest.raises(FitInputError):
        make_request(points, n_vertices=n, missing_edges=missing)


@pytest.mark.parametrize("n", [1, 2])
def test_missing_edges_ignored_for_point_and_segment(n):
    assert make_request([[1, 2], [3, 4]], n_vertices=n, missing_edges=[0, 1, 99]).missing_edges == ()


def test_good_reply_parsed():
    req = make_request([[1, 2], [3, 4]], n_vertices=3)
    result = parse_reply(req, {"error": 0, "objective_function": [1, 4],
                               "poly_points": [[0, 0], [1, 1], [2, 0]]})
    assert result.objective_sq == Fraction(1, 4)
    assert result.objective == pytest.approx(0.5)
    assert result.vertices.dtype == np.int64


@pytest.mark.parametrize("reply", [
    {"error": 0, "objective_function": [0, 1], "poly_points": [[0, 0], [1, 1]]},  # too few
    {"error": 0, "objective_function": [0, 1], "poly_points": [[0, 0.5], [1, 1], [2, 0]]},
    {"error": 0, "objective_function": [1, 0], "poly_points": [[0, 0], [1, 1], [2, 0]]},
    {"poly_points": [[0, 0], [1, 1], [2, 0]]},  # no error code
])
def test_bad_reply_rejected(reply):
    with pytest.raises(SolverError):
        parse_reply(make_request([[1, 2], [3, 4]], n_vertices=3), reply)


def test_error_code_reported():
    reply = {"error": 2, "objective_function": None, "poly_points": None}
    with pytest.raises(FitFailed) as info:
        parse_reply(make_request([[1, 2], [3, 4]], n_vertices=4, missing_edges=[0, 1]), reply, "details here")
    assert info.value.code == 2
    assert "details here" in str(info.value)


def test_arguments_after_points_must_be_keywords():
    with pytest.raises(TypeError):
        make_request([[1, 2], [3, 4]], 3)
    with pytest.raises(TypeError):
        fit([[1, 2], [3, 4]], 2)


def test_evaluate_request_carries_vertices():
    req = make_request([[1, 2], [3, 4]], n_vertices=2, vertices=[[-1, 0], [5, 5]])
    assert req.to_json_dict()["vertices"] == [[-1, 0], [5, 5]]
    with pytest.raises(FitInputError):
        make_request([[1, 2], [3, 4]], n_vertices=2, vertices=[[0, 0]])


def test_reference_integral_matches_numerical_integration():
    """The exact reference integral agrees with brute-force sampling of the integrand."""
    from polyfit import reference
    rng = np.random.default_rng(3)
    for _ in range(20):
        pts = rng.integers(0, 30, size=(8, 2))
        q0, q1 = rng.integers(-5, 35, size=(2, 2))
        t = np.linspace(0, 1, 20001)
        curve = q0 + t[:, None] * (q1 - q0)
        d2 = ((curve[:, None, :] - pts[None, :, :]) ** 2).sum(axis=2).min(axis=1)
        numeric = np.trapezoid(d2, t)
        assert float(reference.segment_integral(pts, q0, q1)) == pytest.approx(numeric, rel=1e-6, abs=1e-6)


def test_missing_executable_is_clear(tmp_path):
    with pytest.raises(SolverError, match="not found"):
        fit([[1, 2]], n_vertices=1, exe=tmp_path / "nope.exe")


@pytest.mark.parametrize("name", list(samples.ALL))
@pytest.mark.parametrize("n", [1, 2, 3, 6])
def test_mock_fit_and_plot(name, n):
    result = fit(samples.ALL[name](), n_vertices=n, missing_edges=[0], backend="mock")
    assert result.vertices.shape == (n, 2)
    assert len(result.edges()) == {1: 0, 2: 1}.get(n, n)
    plot_fit(result)
    matplotlib.pyplot.close("all")
