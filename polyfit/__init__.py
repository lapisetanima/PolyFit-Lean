"""Best-fit polygons to pixel point sets. The solver is written in Lean 4."""

from .bridge import FitFailed, SolverError, evaluate, fit, reduce_hull, rough_fit
from ._saved import SavedDataError
from .attempt import FitAttempt
from .pointset import PointSet, attempt_fits, build_point_sets
from .problem import FitInputError, FitRequest, FitResult, make_request

__all__ = ["fit", "evaluate", "reduce_hull", "rough_fit", "make_request", "FitRequest", "FitResult", "FitInputError",
           "SolverError", "FitFailed", "PointSet", "FitAttempt", "SavedDataError",
           "build_point_sets", "attempt_fits"]
