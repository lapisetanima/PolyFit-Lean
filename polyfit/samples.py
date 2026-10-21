"""Hand-made point sets for testing. All return (k, 2) int64 arrays of (row, col)."""

from __future__ import annotations

import numpy as np


def rasterize_outline(vertices, missing_edges=(), closed=True, noise=0.0, seed=0):
    """Pixels along the edges of a polygon, skipping `missing_edges`.

    `noise` is the standard deviation (in pixels) of jitter added before rounding.
    Edge e joins vertices[e] to vertices[(e + 1) % n], as in polyfit.problem.
    """
    rng = np.random.default_rng(seed)
    v = np.asarray(vertices, dtype=np.float64)
    n = len(v)
    n_edges = n if closed and n > 2 else n - 1
    pixels = []
    for e in range(n_edges):
        if e in missing_edges:
            continue
        a, b = v[e], v[(e + 1) % n]
        steps = max(int(np.ceil(np.abs(b - a).max())) * 2, 1)
        t = np.linspace(0.0, 1.0, steps + 1)[:, None]
        pixels.append(a + t * (b - a))
    if not pixels:
        return np.empty((0, 2), dtype=np.int64)
    pts = np.vstack(pixels)
    if noise > 0:
        pts = pts + rng.normal(scale=noise, size=pts.shape)
    pts = np.clip(np.round(pts), 0, None).astype(np.int64)
    _, first = np.unique(pts, axis=0, return_index=True)
    return pts[np.sort(first)]  # distinct pixels, in order along the outline


def thin(points, keep=0.25):
    """About `keep` of the points (at least one), evenly spaced through their order.

    For an outline from rasterize_outline this keeps every (1/keep)-th pixel along
    the path, so the points stay spread over every edge rather than clumping.
    """
    pts = np.asarray(points)
    count = min(len(pts), max(1, int(round(keep * len(pts)))))
    chosen = np.unique(np.round(np.linspace(0, len(pts) - 1, count)).astype(int))
    return pts[chosen]


def single_pixel():
    return np.array([[5, 7]], dtype=np.int64)


def blob(seed=0, keep=0.25):
    """A small, roughly round cluster of pixels."""
    rng = np.random.default_rng(seed)
    pts = rng.normal(loc=(10.0, 12.0), scale=1.5, size=(25, 2))
    pts = np.unique(np.clip(np.round(pts), 0, None).astype(np.int64), axis=0)
    return thin(pts, keep)


def noisy_segment(seed=0, keep=0.25):
    pts = rasterize_outline([(4, 3), (16, 25)], closed=False, noise=0.6, seed=seed)
    return thin(pts, keep)


def triangle_outline(seed=0, keep=0.25):
    pts = rasterize_outline([(3, 5), (22, 3), (14, 26)], noise=0.4, seed=seed)
    return thin(pts, keep)


def square_missing_edge(seed=0, keep=0.25):
    """Square outline with edge 2 (from vertex 2 to vertex 3) absent."""
    pts = rasterize_outline([(4, 4), (4, 20), (20, 20), (20, 4)], missing_edges=(2,),
                            noise=0.3, seed=seed)
    return thin(pts, keep)


def hexagon_outline(seed=0, keep=0.25):
    angles = np.arange(6) * np.pi / 3
    verts = np.column_stack([15 + 11 * np.sin(angles), 15 + 11 * np.cos(angles)])
    pts = rasterize_outline(verts, noise=0.4, seed=seed)
    return thin(pts, keep)


ALL = {
    "single_pixel": single_pixel,
    "blob": blob,
    "noisy_segment": noisy_segment,
    "triangle_outline": triangle_outline,
    "square_missing_edge": square_missing_edge,
    "hexagon_outline": hexagon_outline,
}
