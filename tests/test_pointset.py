"""The describe command and PointSet, checked against the independent Python reference."""

from fractions import Fraction

import numpy as np
import pytest

from polyfit import FitFailed, FitInputError, PointSet, SavedDataError, reference, samples
from polyfit.bridge import DEFAULT_EXE, run_solver

pytestmark = pytest.mark.skipif(not DEFAULT_EXE.is_file(),
                                reason="Lean solver not built (run `lake build` in lean/)")


def point_sets():
    sets = [make() for name, make in samples.ALL.items() if name != "single_pixel"]
    sets += [make(keep=1.0) for name, make in samples.ALL.items() if name != "single_pixel"]
    rng = np.random.default_rng(4)
    for _ in range(25):
        pts = np.unique(rng.integers(0, 15, size=(int(rng.integers(2, 30)), 2)), axis=0)
        if len(pts) >= 2:
            sets.append(pts)
    return sets


@pytest.mark.parametrize("pts", point_sets())
def test_describe_matches_reference(pts):
    ps = PointSet.from_points(pts)
    ref = reference.describe(ps.points)
    assert ps.com == ref["com"]
    assert ps.diam_sq == ref["diam_sq"]
    assert ps.inner_radius_sq == ref["inner_radius_sq"]
    assert ps.outer_radius_sq == ref["outer_radius_sq"]
    assert [tuple(v) for v in ps.hull.tolist()] == ref["hull"]


@pytest.mark.parametrize("pts", point_sets())
def test_hull_is_strictly_counterclockwise(pts):
    hull = PointSet.from_points(pts).hull.tolist()
    if len(hull) >= 3:
        for a, b, c in zip(hull, hull[1:] + hull[:1], hull[2:] + hull[:2]):
            assert reference.cross((b[0] - a[0], b[1] - a[1]), (c[0] - b[0], c[1] - b[1])) > 0


def test_square_hand_checked():
    ps = PointSet.from_points([[0, 0], [0, 4], [4, 4], [4, 0], [2, 2], [0, 2]])
    assert ps.com == (Fraction(5, 3), Fraction(2))
    assert ps.diam_sq == 32
    assert ps.inner_radius_sq == Fraction(1, 9)       # from (2, 2)
    assert ps.outer_radius_sq == Fraction(85, 9)      # from (4, 0) and (4, 4)
    # (0, 2) is collinear on the left edge, so it is left out. Start: of the two
    # rightmost vertices, (0, 4) is above COM's row; then counterclockwise on screen.
    assert ps.hull.tolist() == [[0, 4], [0, 0], [4, 0], [4, 4]]


@pytest.mark.parametrize("pts, expected_start", [
    ([[0, 4], [4, 4], [0, 0], [4, 0]], [0, 4]),     # one right-hand vertex on each side of COM's row
    ([[0, 4], [1, 4], [5, 0]], [1, 4]),             # both above COM's row (i = 2): the lower one
    ([[4, 4], [5, 4], [0, 0]], [4, 4]),             # both below COM's row (i = 3): the higher one
    ([[2, 4], [4, 4], [0, 0]], [2, 4]),             # (2, 4) exactly on COM's row (i = 2) counts as above
])
def test_hull_start_rule(pts, expected_start):
    ps = PointSet.from_points(pts)
    assert ps.hull[0].tolist() == expected_start


def test_collinear_points_have_two_hull_vertices():
    ps = PointSet.from_points([[1, 1], [2, 2], [3, 3], [5, 5]])
    assert ps.hull.tolist() == [[5, 5], [1, 1]]


def test_pointset_drops_duplicates_and_needs_two_points():
    ps = PointSet.from_points([[1, 2], [3, 4], [1, 2]])
    assert ps.points.tolist() == [[1, 2], [3, 4]]
    with pytest.raises(FitInputError):
        PointSet.from_points([[1, 2], [1, 2]])
    with pytest.raises(FitInputError):
        PointSet.from_points([[-1, 2], [3, 4]])


def test_pointset_is_read_only_and_round_trips():
    ps = PointSet.from_points(samples.triangle_outline())
    with pytest.raises(ValueError):
        ps.points[0, 0] = 99
    with pytest.raises(AttributeError):
        ps.diam_sq = 0
    again = PointSet.from_dict(ps.to_dict())
    assert again.to_dict() == ps.to_dict()
    assert again.com == ps.com and again.hull.tolist() == ps.hull.tolist()


def _saved():
    return PointSet.from_points([[0, 0], [0, 4], [4, 4], [4, 0], [2, 2]]).to_dict()


def _with(**changes):
    d = _saved()
    for key, value in changes.items():
        if value is None:
            del d[key]
        else:
            d[key] = value
    return d


@pytest.mark.parametrize("bad", [
    _with(points=None),                                   # missing key
    _with(points=[[0, 0], [0, 4.5], [4, 4]]),             # non-integer coordinate
    _with(points=[[0, 0], [0, "4"], [4, 4]]),             # string, not a number
    _with(points=[[0, 0, 1], [0, 4]]),                    # not a pair
    _with(points=[[0, 0]]),                               # too few points
    _with(com=[[2, 1], [2, 0]]),                          # zero denominator
    _with(com=[[2, 1]]),                                  # only one coordinate
    _with(diam_sq=32.0),                                  # float, not an int
    _with(diam_sq=True),                                  # bool is not an int here
    _with(hull="not a list"),
    "not a dict at all",
])
def test_from_dict_rejects_malformed_data(bad):
    with pytest.raises(SavedDataError):
        PointSet.from_dict(bad)


@pytest.mark.parametrize("field, value", [
    ("com", [[7, 3], [2, 1]]),                            # wrong centre of mass
    ("diam_sq", 31),
    ("inner_radius_sq", [1, 1]),                          # true value is 0: COM (2, 2) is a point
    ("hull", [[0, 0], [0, 4], [4, 4], [4, 0]]),           # right vertices, wrong order
    ("points", [[0, 0], [0, 4], [4, 4], [4, 0], [2, 2], [2, 2]]),   # a duplicate point
    ("points", [[0, 0], [0, 4], [4, 4], [4, 0], [-2, 2]]),          # a negative coordinate
])
def test_from_dict_rejects_inconsistent_data(field, value):
    with pytest.raises(SavedDataError, match="disagrees|invalid"):
        PointSet.from_dict(_with(**{field: value}))


def test_from_dict_verify_false_skips_consistency_check():
    tampered = _with(diam_sq=31)
    assert PointSet.from_dict(tampered, verify=False).diam_sq == 31
    with pytest.raises(SavedDataError):
        PointSet.from_dict(_with(diam_sq=31.0), verify=False)   # malformed is still rejected


def test_build_point_sets_skips_failures():
    from polyfit import build_point_sets
    named = {"good": [[0, 0], [3, 4]], "one point": [[1, 1]], "duplicates": [[2, 2], [2, 2]],
             "negative": [[-1, 0], [1, 1]], "also good": samples.blob()}
    point_sets, failures = build_point_sets(named)
    assert list(point_sets) == ["good", "also good"]
    assert set(failures) == {"one point", "duplicates", "negative"}
    assert all(isinstance(err, FitInputError) for err in failures.values())


def test_describe_errors():
    reply, _ = run_solver({"command": "describe", "points": [[1, 1], [1, 1]]})
    assert reply["error"] == 1
    reply, _ = run_solver({"command": "nonsense", "points": [[1, 1], [2, 2]]})
    assert reply["error"] == 4
