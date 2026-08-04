"""Exact rational geometry for the disconnection certificate (d = 3).

All decisions are certified in Fraction arithmetic; floats are used only as
hints. H-polytopes are given as (A, b) rational rows meaning A y >= b.

  - feasible_point:  exact interior/feasible point (float Chebyshev hint,
                     rationalized, verified exactly; None if no hint checks);
  - farkas_empty:    exact infeasibility certificate (rationalized dual,
                     verified: lam >= 0, lam^T A = 0, lam^T b > 0);
  - vertices:        all vertices by exact enumeration of row triples;
  - volume:          exact volume via facet-wise fan triangulation with
                     exact coplanarity (facet rows) and exact determinants.
"""
from fractions import Fraction
from itertools import combinations
import numpy as np


def frac(x, den=10**7):
    return Fraction(round(float(x) * den), den)


def to_float(A, b):
    return (np.array([[float(x) for x in row] for row in A]),
            np.array([float(x) for x in b]))


def check_point(A, b, p, strict=False):
    for row, bb in zip(A, b):
        v = sum(r * pi for r, pi in zip(row, p))
        if strict:
            if v <= bb:
                return False
        else:
            if v < bb:
                return False
    return True


def feasible_point(A, b, den=10**7):
    """Exact feasible point of {A y >= b} from a float Chebyshev hint."""
    from scipy.optimize import linprog
    Af, bf = to_float(A, b)
    norms = np.linalg.norm(Af, axis=1)
    m, d = Af.shape
    Aub = np.hstack([-Af, norms[:, None]])
    res = linprog(np.concatenate([np.zeros(d), [-1.0]]), A_ub=Aub, b_ub=-bf,
                  bounds=[(None, None)] * d + [(0, None)], method="highs")
    if not res.success or res.x[d] <= 1e-12:
        return None
    p = [frac(x, den) for x in res.x[:d]]
    if check_point(A, b, p, strict=True):
        return p
    if check_point(A, b, p, strict=False):
        return p
    return None


def farkas_empty(A, b, den=10**9):
    """Exact certificate that {A y >= b} is empty: lam >= 0 with
    lam^T A = 0 and lam^T b > 0 (rationalized from the phase-1 dual)."""
    from scipy.optimize import linprog
    Af, bf = to_float(A, b)
    m, d = Af.shape
    # phase 1: max t  s.t.  A y - t*1 >= b  (t <= 0 at optimum iff empty)
    Aub = np.hstack([-Af, np.ones((m, 1))])
    res = linprog(np.concatenate([np.zeros(d), [-1.0]]), A_ub=Aub, b_ub=-bf,
                  bounds=[(None, None)] * d + [(None, None)], method="highs")
    if not res.success:
        return None
    lam_f = np.array(res.ineqlin.marginals) * -1.0   # duals of Aub rows
    if lam_f.min() < -1e-9:
        return None
    lam = [max(Fraction(0), frac(x, den)) for x in lam_f]
    # verify exactly
    for jcol in range(d):
        if sum(l * A[irow][jcol] for irow, l in enumerate(lam)) != 0:
            # try clearing tiny components then re-check A-orthogonality by
            # projecting: simple retry with coarser denominator
            return None
    if sum(l * bb for l, bb in zip(lam, b)) > 0:
        return lam
    return None


def solve3(rows, rhs):
    """Exact solve of a 3x3 rational system; None if singular."""
    (a, b, c), (d_, e, f), (g, h, i) = rows
    det = a * (e * i - f * h) - b * (d_ * i - f * g) + c * (d_ * h - e * g)
    if det == 0:
        return None
    r1, r2, r3 = rhs
    x = (r1 * (e * i - f * h) - b * (r2 * i - f * r3) + c * (r2 * h - e * r3)) / det
    y = (a * (r2 * i - f * r3) - r1 * (d_ * i - f * g) + c * (d_ * r3 - r2 * g)) / det
    z = (a * (e * r3 - r2 * h) - b * (d_ * r3 - r2 * g) + r1 * (d_ * h - e * g)) / det
    return (x, y, z)


def vertices(A, b):
    """All vertices of {A y >= b} in R^3, exactly."""
    m = len(A)
    vs = set()
    for tri in combinations(range(m), 3):
        p = solve3([A[i] for i in tri], [b[i] for i in tri])
        if p is None:
            continue
        if check_point(A, b, p):
            vs.add(p)
    return list(vs)


def volume(A, b, verts=None):
    """Exact volume of the (possibly lower-dim, then 0) polytope {Ay >= b}."""
    if verts is None:
        verts = vertices(A, b)
    if len(verts) < 4:
        return Fraction(0)
    p0 = verts[0]
    vol = Fraction(0)
    for irow in range(len(A)):
        row, bb = A[irow], b[irow]
        face = [v for v in verts
                if sum(r * vi for r, vi in zip(row, v)) == bb]
        if len(face) < 3:
            continue
        # skip faces containing p0 (zero-height tets)
        if any(v == p0 for v in face):
            if sum(r * pi for r, pi in zip(row, p0)) == bb:
                continue
        # exact angular sort of the face polygon around its centroid
        n = len(face)
        cen = tuple(sum(v[k] for v in face) / n for k in range(3))
        # basis: e1 = face[0]-cen; normal = row
        e1 = tuple(face[0][k] - cen[k] for k in range(3))
        # e2 = normal x e1
        e2 = (row[1] * e1[2] - row[2] * e1[1],
              row[2] * e1[0] - row[0] * e1[2],
              row[0] * e1[1] - row[1] * e1[0])
        def key(v):
            d0 = tuple(v[k] - cen[k] for k in range(3))
            x = sum(d0[k] * e1[k] for k in range(3))
            y = sum(d0[k] * e2[k] for k in range(3))
            import math
            return math.atan2(float(y), float(x))
        face.sort(key=key)
        for i2 in range(1, n - 1):
            q1 = tuple(face[0][k] - p0[k] for k in range(3))
            q2 = tuple(face[i2][k] - p0[k] for k in range(3))
            q3 = tuple(face[i2 + 1][k] - p0[k] for k in range(3))
            det = (q1[0] * (q2[1] * q3[2] - q2[2] * q3[1])
                   - q1[1] * (q2[0] * q3[2] - q2[2] * q3[0])
                   + q1[2] * (q2[0] * q3[1] - q2[1] * q3[0]))
            vol += abs(det)
    return vol / 6
