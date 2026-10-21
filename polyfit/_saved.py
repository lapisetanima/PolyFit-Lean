"""Strict helpers for reading saved dictionaries (shared by PointSet and FitAttempt).

They accept only genuine values: no silent rounding of 2.5 to 2, no "2" read as 2,
no True read as 1. Anything else raises TypeError or ValueError, which the loaders
turn into a SavedDataError.
"""

from __future__ import annotations

from fractions import Fraction

import numpy as np


class SavedDataError(ValueError):
    """A saved dictionary is malformed, or disagrees with what its points imply."""


def strict_int(x) -> int:
    """x itself if it is an integer; an error otherwise."""
    if isinstance(x, bool) or not isinstance(x, (int, np.integer)):
        raise TypeError(f"expected an integer, got {x!r}")
    return int(x)


def strict_number(x) -> float:
    """x as a float if it is an int or float (not a bool or a string); an error otherwise."""
    if isinstance(x, bool) or not isinstance(x, (int, float, np.integer, np.floating)):
        raise TypeError(f"expected a number, got {x!r}")
    return float(x)


def fraction(pair) -> Fraction:
    """[a, b] -> Fraction(a, b), for integers a, b with b != 0."""
    a, b = pair
    return Fraction(strict_int(a), strict_int(b))


def fraction_pair(f: Fraction) -> list[int]:
    """Fraction -> [numerator, denominator], the saved form."""
    return [f.numerator, f.denominator]


def read_only(arr) -> np.ndarray:
    """A read-only (k, 2) int64 copy of `arr`."""
    arr = np.array(arr, dtype=np.int64).reshape(-1, 2)
    arr.setflags(write=False)
    return arr


def int_pairs(values, min_rows: int = 0) -> np.ndarray:
    """A read-only (k, 2) array from a list of [i, j] integer pairs, with k >= min_rows."""
    rows = [[strict_int(a), strict_int(b)] for a, b in values]
    if len(rows) < min_rows:
        raise ValueError(f"expected at least {min_rows} [i, j] pairs, got {len(rows)}")
    return read_only(rows)
