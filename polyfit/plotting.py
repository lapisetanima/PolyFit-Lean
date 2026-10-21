"""Matplotlib helpers, in matrix style: column j runs rightward and row i runs downward
(origin at the upper left), as in an image."""

from __future__ import annotations

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.collections import PatchCollection
from matplotlib.patches import Rectangle

from .problem import FitResult


def subplot_grid(count: int, ncols: int = 3, size: float = 3.0):
    """A figure with `count` subplots in rows of `ncols`, each about `size` inches
    square; unused grid cells are hidden. Returns (fig, list of axes)."""
    nrows = max(1, -(-count // ncols))
    fig, axes = plt.subplots(nrows, ncols, figsize=(ncols * size, nrows * size), squeeze=False)
    axes = list(axes.flat)
    for ax in axes[count:]:
        ax.axis("off")
    return fig, axes[:count]


def plot_points(points, ax=None, shape=None, color="tab:blue", title=None, also_show=None):
    """Draw each (i, j) point as a filled unit pixel centred on its coordinates.

    shape=(I, J) fixes the axes to the full pixel grid; otherwise they fit the points
    plus any extra (i, j) points in `also_show` (such as polygon vertices).
    """
    if ax is None:
        _, ax = plt.subplots(figsize=(4.5, 4.5))
    pts = np.asarray(points).reshape(-1, 2)
    pixels = [Rectangle((c - 0.5, r - 0.5), 1, 1) for r, c in pts]
    ax.add_collection(PatchCollection(pixels, facecolor=color, edgecolor="none", alpha=0.6))

    if shape is not None:
        rows, cols = shape
        ax.set_xlim(-0.5, cols - 0.5)
        ax.set_ylim(rows - 0.5, -0.5)
    else:
        extent = pts if also_show is None else np.vstack([pts, np.asarray(also_show).reshape(-1, 2)])
        lo, hi = extent.min(axis=0) - 1.5, extent.max(axis=0) + 1.5
        ax.set_xlim(lo[1], hi[1])
        ax.set_ylim(hi[0], lo[0])
    ax.set_aspect("equal")
    ax.set_xlabel("column j")
    ax.set_ylabel("row i")
    if title:
        ax.set_title(title)
    return ax


def plot_pointset(ps, ax=None, shape=None, title=None):
    """Points, convex hull (vertices numbered in counterclockwise order), centre of mass,
    and the inner and outer circles about it."""
    from matplotlib.patches import Circle

    ci, cj = float(ps.com[0]), float(ps.com[1])
    r_out = ps.outer_radius
    corners = [[ci - r_out, cj - r_out], [ci + r_out, cj + r_out]]
    ax = plot_points(ps.points, ax=ax, shape=shape, title=title, also_show=corners)

    hull = np.vstack([ps.hull, ps.hull[:1]])
    ax.plot(hull[:, 1], hull[:, 0], "-", color="tab:green", linewidth=1.5)
    for k, (r, c) in enumerate(ps.hull):
        ax.annotate(f"h{k}", (c, r), textcoords="offset points", xytext=(4, 4), fontsize=8, color="tab:green")
    ax.plot([cj], [ci], "+", color="black", markersize=10)
    for radius in (ps.inner_radius, r_out):
        ax.add_patch(Circle((cj, ci), radius, fill=False, linestyle=":", color="gray"))
    return ax


def plot_attempt(ps, attempt, ax=None, shape=None, title=None, show_candidates=True):
    """Plot one recorded FitAttempt's fine fit over its PointSet's points, with the
    candidate vertices of its reduced hull marked as green crosses."""
    ax = plot_fit(attempt.as_result(ps.points), ax=ax, shape=shape, title=title)
    if show_candidates and attempt.reduced_hull is not None:
        c = attempt.reduced_hull
        ax.plot(c[:, 1], c[:, 0], "x", color="tab:green", markersize=6)
    return ax


def plot_fit(result: FitResult, ax=None, shape=None, title=None, label_vertices=True):
    """Points, plus the fitted polygon. Missing edges are drawn dashed and faint."""
    req = result.request
    if title is None:
        title = f"n = {req.n_vertices}, missing = {list(req.missing_edges)}"
        if result.objective is not None:
            title += f", F = {result.objective:.4g}"
    ax = plot_points(req.points, ax=ax, shape=shape, title=title, also_show=result.vertices)

    for e, a, b, missing in result.edges():
        style = dict(color="gray", linestyle="--", alpha=0.5) if missing else dict(color="tab:red")
        ax.plot([a[1], b[1]], [a[0], b[0]], linewidth=2, **style)
        mid = (a + b) / 2
        ax.annotate(f"e{e}", (mid[1], mid[0]), color=style["color"], fontsize=8,
                    ha="center", va="center", backgroundcolor="white")

    v = result.vertices
    ax.plot(v[:, 1], v[:, 0], "o", color="black", markersize=5)
    if label_vertices:
        for k, (r, c) in enumerate(v):
            ax.annotate(f"v{k}", (c, r), textcoords="offset points", xytext=(5, 5), fontsize=9)
    return ax
