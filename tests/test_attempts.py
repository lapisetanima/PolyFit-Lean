"""FitAttempt and PointSet.attempts: recording, freezing, failure policy, saving."""

import copy
import dataclasses
from datetime import datetime

import numpy as np
import pytest

from polyfit import (FitAttempt, FitFailed, PointSet, SavedDataError, attempt_fits,
                     build_point_sets, evaluate, reduce_hull, reference, rough_fit, samples)
from polyfit.bridge import DEFAULT_EXE

pytestmark = pytest.mark.skipif(not DEFAULT_EXE.is_file(),
                                reason="Lean solver not built (run `lake build` in lean/)")


@pytest.fixture
def ps():
    return PointSet.from_points(samples.noisy_segment())


def test_fit_records_a_frozen_attempt(ps):
    attempt = ps.fit(n_vertices=2)
    assert ps.attempts == [attempt]
    assert attempt.n_vertices == 2 and attempt.engine == "lean"
    assert attempt.objective_sq == reference.objective_segment(ps.points, *attempt.vertices)
    assert attempt.duration_s > 0
    datetime.fromisoformat(attempt.started_at)
    with pytest.raises(dataclasses.FrozenInstanceError):
        attempt.objective_sq = 0
    with pytest.raises(ValueError):
        attempt.vertices[0, 0] = 99


def test_attempts_accumulate_in_order(ps):
    ps.fit(n_vertices=1)
    ps.fit(n_vertices=2)
    ps.fit(n_vertices=3, engine="mock")
    assert [(a.n_vertices, a.engine) for a in ps.attempts] == [(1, "lean"), (2, "lean"), (3, "mock")]


def test_repeated_fit_reuses_the_recorded_attempt(ps, tmp_path):
    first = ps.fit(n_vertices=2)
    # A missing executable would make any real run fail, so success proves nothing ran.
    again = ps.fit(n_vertices=2, exe=tmp_path / "no-such-solver.exe")
    assert again is first
    assert ps.attempts == [first]


@pytest.mark.parametrize("first, second", [
    (dict(n_vertices=4, missing_edges=[3, 1, 3]), dict(n_vertices=4, missing_edges=[1, 3])),
    (dict(n_vertices=2, missing_edges=[0, 5]), dict(n_vertices=2)),      # ignored for segments
    (dict(n_vertices=1), dict(n_vertices=1, missing_edges=[0])),
])
def test_same_characteristics_after_normalising(ps, first, second):
    a = ps.fit(engine="mock", **first)
    assert ps.fit(engine="mock", **second) is a
    assert len(ps.attempts) == 1


def test_different_characteristics_are_separate_attempts(ps):
    ps.fit(n_vertices=2)
    ps.fit(n_vertices=2, engine="mock")
    ps.fit(n_vertices=3, engine="mock")
    ps.fit(n_vertices=4, missing_edges=[1], engine="mock")
    ps.fit(n_vertices=4, missing_edges=[2], engine="mock")
    assert len(ps.attempts) == 5
    assert ps.find_attempt(n_vertices=4, missing_edges=[2], engine="mock") is ps.attempts[-1]
    assert ps.find_attempt(n_vertices=5) is None


def test_running_the_same_plans_twice_changes_nothing():
    point_sets, _ = build_point_sets({"a": samples.blob(), "b": samples.noisy_segment()})
    plans = {"a": [dict(n_vertices=2), dict(n_vertices=3, engine="mock")], "b": [dict(n_vertices=1)]}
    attempt_fits(point_sets, plans)
    before = {name: list(ps.attempts) for name, ps in point_sets.items()}
    attempt_fits(point_sets, plans)
    assert {name: list(ps.attempts) for name, ps in point_sets.items()} == before


@pytest.mark.parametrize("n, missing", [(2, []), (3, []), (4, [2]), (6, [0, 3])])
def test_attempt_records_every_pipeline_step(n, missing):
    pts = samples.hexagon_outline(keep=1.0) if n == 6 else samples.square_missing_edge()
    ps = PointSet.from_points(pts)
    a = ps.fit(n_vertices=n, missing_edges=missing, k=3)
    assert a.k == 3
    assert a.reduced_hull.tolist() == reduce_hull(ps.points, n_vertices=n).tolist()
    rough = rough_fit(ps.points, n_vertices=n, missing_edges=missing, candidates=a.reduced_hull, k=3)
    assert [(r.vertices.tolist(), r.objective_sq) for r in a.rough_fits] == \
           [(r.vertices.tolist(), r.objective_sq) for r in rough]
    assert a.fine_method == "local_search" and a.certified is True
    assert a.objective_sq <= a.rough_fits[0].objective_sq          # the search only improves
    assert a.objective_sq == evaluate(ps.points, vertices=a.vertices, missing_edges=missing).objective_sq


def test_segment_search_from_farthest_pair_matches_old_segment_search():
    """The general search, for n = 2, is the segment search: same moves, same order."""
    from polyfit.bridge import fine_fit
    from polyfit import fit
    for make in (samples.noisy_segment, samples.blob, samples.triangle_outline):
        pts = make(keep=1.0)
        a, b = max(((p, q) for p in pts for q in pts), key=lambda pq: reference.dist_sq(*pq))
        result, _, certified = fine_fit(pts, n_vertices=2, start=[a, b])
        old = fit(pts, n_vertices=2)
        assert result.vertices.tolist() == old.vertices.tolist()
        assert result.objective_sq == old.objective_sq and certified


def test_large_n_skips_certification():
    ps = PointSet.from_points(samples.hexagon_outline(keep=1.0))
    a = ps.fit(n_vertices=8)
    assert a.fine_method == "local_search" and a.certified is False
    assert a.objective_sq <= a.rough_fits[0].objective_sq


def test_point_and_mock_attempts_have_no_rough_fit(ps):
    for a in (ps.fit(n_vertices=1), ps.fit(n_vertices=4, engine="mock")):
        assert a.rough_fits == () and a.k is None and a.certified is None
    point, mock = ps.attempts
    assert [point.fine_method, mock.fine_method] == ["centre_of_mass", "mock"]
    assert point.reduced_hull is None
    assert mock.reduced_hull.tolist() == reduce_hull(ps.points, n_vertices=4).tolist()


def test_k_is_part_of_the_characteristics(ps):
    a2 = ps.fit(n_vertices=3)
    a5 = ps.fit(n_vertices=3, k=5)
    assert a2 is not a5 and len(ps.attempts) == 2
    assert ps.fit(n_vertices=3, k=2) is a2
    assert ps.fit(n_vertices=1, k=9) is ps.fit(n_vertices=1)    # k means nothing without a rough fit


def test_tampered_rough_fit_is_caught_by_replay(ps):
    ps.fit(n_vertices=3)
    d = ps.to_dict()
    d["attempts"][0]["rough_fits"][1]["vertices"][0] = [0, 0]
    with pytest.raises(SavedDataError, match="rough_fits"):
        PointSet.from_dict(d)


def test_saved_duplicate_attempts_are_rejected(ps):
    ps.fit(n_vertices=2)
    d = ps.to_dict()
    d["attempts"].append(dict(d["attempts"][0]))
    with pytest.raises(SavedDataError, match="same characteristics"):
        PointSet.from_dict(d)


def test_failed_fit_raises_and_records_nothing(ps):
    ps.fit(n_vertices=2)
    with pytest.raises(FitFailed) as info:
        ps.fit(n_vertices=4, missing_edges=[0, 1])
    assert info.value.code == 2
    assert len(ps.attempts) == 1


def test_evaluate_is_not_recorded(ps):
    evaluate(ps.points, vertices=[[4, 3], [16, 25]])
    assert ps.attempts == []


def test_missing_edges_recorded_as_the_solver_used_them(ps):
    attempt = ps.fit(n_vertices=2, missing_edges=[0, 5])   # ignored for a segment
    assert attempt.missing_edges == ()


def test_attempt_fits_stops_a_point_set_at_its_first_failure():
    point_sets, _ = build_point_sets({"a": samples.blob(), "b": samples.noisy_segment()})
    plans = {
        "a": [dict(n_vertices=2), dict(n_vertices=4, missing_edges=[3, 0]), dict(n_vertices=1)],
        "b": [dict(n_vertices=1), dict(n_vertices=2)],
    }
    stopped = attempt_fits(point_sets, plans)
    assert list(stopped) == ["a"] and stopped["a"].code == 2
    assert [a.n_vertices for a in point_sets["a"].attempts] == [2]      # n = 1 never ran
    assert [a.n_vertices for a in point_sets["b"].attempts] == [1, 2]   # "b" carried on


def test_attempts_are_saved_and_verified_on_load(ps):
    ps.fit(n_vertices=1)
    ps.fit(n_vertices=2)
    ps.fit(n_vertices=4, engine="mock")
    loaded = PointSet.from_dict(ps.to_dict())
    assert [a.to_dict() for a in loaded.attempts] == [a.to_dict() for a in ps.attempts]
    assert all(isinstance(a, FitAttempt) for a in loaded.attempts)


def test_old_saves_without_attempts_still_load(ps):
    d = ps.to_dict()
    del d["attempts"]
    assert PointSet.from_dict(d).attempts == []


def _saved_with_one_attempt():
    ps = PointSet.from_points(samples.noisy_segment())
    ps.fit(n_vertices=2)
    return ps.to_dict()


@pytest.mark.parametrize("field, value", [
    ("n_vertices", 2.0),
    ("n_vertices", 0),
    ("missing_edges", [1]),                     # not allowed for a segment
    ("engine", "magic"),
    ("vertices", [[0, 0]]),                     # wrong number of vertices
    ("vertices", [[0, 0], [1, 2.5]]),
    ("objective_sq", None),                     # only mock attempts may lack it
    ("objective_sq", [1, 0]),
    ("objective_sq", [-1, 2]),
    ("started_at", "yesterday"),
    ("duration_s", -1.0),
    ("duration_s", "fast"),
])
def test_malformed_attempt_is_rejected(field, value):
    d = _saved_with_one_attempt()
    d["attempts"][0][field] = value
    with pytest.raises(SavedDataError):
        PointSet.from_dict(d)


def test_wrong_objective_is_caught_by_verification():
    d = _saved_with_one_attempt()
    good = copy.deepcopy(d)
    num, den = d["attempts"][0]["objective_sq"]
    d["attempts"][0]["objective_sq"] = [num + 1, den]
    with pytest.raises(SavedDataError, match="attempt 0"):
        PointSet.from_dict(d)
    assert PointSet.from_dict(d, verify=False).attempts[0].objective_sq != PointSet.from_dict(good).attempts[0].objective_sq
