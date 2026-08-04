"""The certified disconnection theorem, d = 3: an exact-rational, realizable,
alpha-balanced cutting-plane trajectory whose candidate body X_t is
disconnected — separated by an explicit open slab.

Everything decided in Fraction arithmetic; floats are hints only:
  1. rational apexes; displacements REBUILT by exact interval arithmetic
     (the game's own realizability recursion, in Q) => exact pairwise
     contraction inequalities => Lean realizable_of_pairwise supplies an
     actual l-inf contraction whose fixed point survives every cut;
  2. exact cell tree; per cell, all 6 pyramid pieces: exact volumes with the
     PARTITION IDENTITY (sum of pieces = parent, root = box = 1) gating the
     float-hinted vertex enumeration (fallback: full triple enumeration);
  3. per-round exact balance ratios of each apex;
  4. disconnection: a rational linear phi and thresholds th1 < th2 with
     every final cell's vertex set entirely in {phi <= th1} or {phi >= th2}
     and positive certified volume on both sides  =>  X_t is topologically
     disconnected by the open slab {th1 < phi < th2}.

Usage: python certify_disconnect.py [seed] [T]
"""
import sys
from fractions import Fraction
import numpy as np
import adversary_game as G
import exact_geom as eg

DEN = 10**6
LAM = Fraction(10**9 - 1, 10**9)
RHO = Fraction(1, 10**4)     # displacement scale (rational)
MARG = Fraction(1, 10**7)    # interval safety margin


def pyramid_rows(c, si, i, d=3):
    rows, rhs = [], []
    for j in range(d):
        if j == i:
            continue
        for tau in (1, -1):
            a = [Fraction(0)] * d
            a[i] = Fraction(si)
            a[j] = Fraction(-tau)
            rows.append(tuple(a))
            rhs.append(Fraction(si) * c[i] - Fraction(tau) * c[j])
    return rows, rhs


def box_rows(d=3):
    A, b = [], []
    for i in range(d):
        e = [Fraction(0)] * d
        e[i] = Fraction(1)
        A.append(tuple(e)); b.append(Fraction(0))
        e2 = [Fraction(0)] * d
        e2[i] = Fraction(-1)
        A.append(tuple(e2)); b.append(Fraction(-1))
    return A, b


def exact_displacements(apexes, signs):
    """Rebuild rational displacements by the game's interval recursion, in Q.
    Returns list of v (tuples of Fraction) with exact pairwise feasibility."""
    hist = []
    for (c, s) in zip(apexes, signs):
        lo = [max(-RHO, -c[i] + MARG) for i in range(3)]
        hi = [min(RHO, Fraction(1) - c[i] - MARG) for i in range(3)]
        for (cq, vq) in hist:
            D = max(abs(c[i] - cq[i]) for i in range(3))
            for i in range(3):
                a = c[i] - cq[i]
                lo[i] = max(lo[i], -LAM * D - a + vq[i])
                hi[i] = min(hi[i], LAM * D - a + vq[i])
        v = []
        for i in range(3):
            if s[i] > 0:
                x = min(max(RHO / 2, lo[i] + MARG), hi[i] - MARG)
            elif s[i] < 0:
                x = max(min(-RHO / 2, hi[i] - MARG), lo[i] + MARG)
            else:
                x = min(max(Fraction(0), lo[i]), hi[i])
            if x < lo[i] or x > hi[i]:
                return None, (len(hist), i)
            v.append(x)
        # sign consistency check
        for i in range(3):
            if s[i] > 0 and v[i] <= 0:
                return None, ("sign", len(hist), i)
            if s[i] < 0 and v[i] >= 0:
                return None, ("sign", len(hist), i)
        hist.append((c, tuple(v)))
    # exact pairwise verification
    n = len(hist)
    for r in range(n):
        for q in range(r + 1, n):
            cr, vr = hist[r]
            cq, vq = hist[q]
            lhs = max(abs((cr[i] + vr[i]) - (cq[i] + vq[i])) for i in range(3))
            rhs = LAM * max(abs(cr[i] - cq[i]) for i in range(3))
            if lhs > rhs:
                return None, ("pair", r, q)
    return [v for (_, v) in hist], None


class Cell:
    __slots__ = ("A", "b", "vol", "verts")

    def __init__(self, A, b):
        self.A, self.b = A, b
        self.vol, self.verts = None, None


def vertices_hint(A, b):
    """Vertex set via float HalfspaceIntersection hints, exact verification.
    Returns (verts, complete_flag); on hint failure returns full enumeration."""
    from scipy.spatial import HalfspaceIntersection
    from scipy.optimize import linprog
    Af, bf = eg.to_float(A, b)
    norms = np.linalg.norm(Af, axis=1)
    m, d = Af.shape
    Aub = np.hstack([-Af, norms[:, None]])
    res = linprog(np.concatenate([np.zeros(d), [-1.0]]), A_ub=Aub, b_ub=-bf,
                  bounds=[(None, None)] * d + [(0, None)], method="highs")
    if not res.success or res.x[d] <= 1e-10:
        return eg.vertices(A, b)
    ip = res.x[:d]
    try:
        hs = HalfspaceIntersection(
            np.hstack([-Af, bf[:, None]]), ip)
    except Exception:
        return eg.vertices(A, b)
    out = set()
    for vtx in hs.intersections:
        act = [i for i in range(m)
               if abs(Af[i] @ vtx - bf[i]) < 1e-7]
        from itertools import combinations
        found = False
        for tri in combinations(act, 3):
            p = eg.solve3([A[i] for i in tri], [b[i] for i in tri])
            if p is not None and eg.check_point(A, b, p):
                out.add(p)
                found = True
                break
        if not found:
            return eg.vertices(A, b)
    return list(out)


def cell_data(C):
    if C.verts is None:
        C.verts = vertices_hint(C.A, C.b)
        C.vol = eg.volume(C.A, C.b, C.verts)
    return C.vol, C.verts


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    T = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    d = 3
    print(f"replaying d=3 seed={seed} T={T} ...", flush=True)
    _, cuts = G.play(d, seed=seed, T=T, mode="adversary", verbose=False)
    apexes = [tuple(eg.frac(x, DEN) for x in c) for (c, s) in cuts[:T]]
    signs = [tuple(int(x) for x in s) for (c, s) in cuts[:T]]
    vs, err = exact_displacements(apexes, signs)
    print(f"realizability (exact, lam = 1-1e-9): "
          f"{'OK' if vs is not None else f'FAILED {err}'}", flush=True)
    if vs is None:
        return

    A0, b0 = box_rows()
    root = Cell(A0, b0)
    cells = [root]
    total = Fraction(1)
    balance_log = []
    for t in range(T):
        c, s = apexes[t], signs[t]
        active = [i for i in range(d) if s[i] != 0]
        bal = {key: Fraction(0) for key in
               [(i, sg) for i in range(d) for sg in (1, -1)]}
        new_cells = []
        for C in cells:
            pvol, _ = cell_data(C)
            if pvol == 0:
                continue
            csum = Fraction(0)
            pieces = {}
            for i in range(d):
                for sg in (1, -1):
                    Ar, br = pyramid_rows(c, sg, i)
                    child = Cell(C.A + Ar, C.b + br)
                    fp = eg.feasible_point(child.A, child.b)
                    if fp is None:
                        pieces[(i, sg)] = None
                        continue
                    v, _ = cell_data(child)
                    pieces[(i, sg)] = child
                    csum += v
                    bal[(i, sg)] += v
            if csum != pvol:
                # hint-based vertices missed something: full enumeration
                csum = Fraction(0)
                for key, child in pieces.items():
                    if child is None:
                        continue
                    child.verts = eg.vertices(child.A, child.b)
                    child.vol = eg.volume(child.A, child.b, child.verts)
                    csum += child.vol
                if csum != pvol:
                    print(f"  PARTITION FAILURE t={t}: "
                          f"{float(csum)} vs {float(pvol)}", flush=True)
                    return
            for i in active:
                ch = pieces.get((i, s[i]))
                if ch is not None and ch.vol > 0:
                    new_cells.append(ch)
        worst = min(min(bal[(i, 1)], bal[(i, -1)]) /
                    (bal[(i, 1)] + bal[(i, -1)]) for i in range(d))
        balance_log.append(worst)
        kept = sum(C.vol for C in new_cells)
        print(f"t={t + 1}: cells={len(new_cells)} "
              f"kept={float(kept / total):.4f} "
              f"worst pyramid-pair share={float(worst):.4f}", flush=True)
        cells, total = new_cells, kept
        if total == 0:
            print("body empty")
            return

    # ---- slab separation ----
    print("searching for a certified separating slab ...", flush=True)
    dirs = []
    for i in range(3):
        e = [Fraction(0)] * 3
        e[i] = Fraction(1)
        dirs.append(tuple(e))
        for j in range(i + 1, 3):
            for tau in (1, -1):
                a = [Fraction(0)] * 3
                a[i], a[j] = Fraction(1), Fraction(tau)
                dirs.append(tuple(a))
    best = None
    for phi in dirs:
        vals = []
        for C in cells:
            _, verts = cell_data(C)
            lo = min(sum(p * v for p, v in zip(phi, vt)) for vt in verts)
            hi = max(sum(p * v for p, v in zip(phi, vt)) for vt in verts)
            vals.append((lo, hi, C.vol))
        vals.sort()
        # scan for the widest gap between consecutive cells' [lo,hi] spans
        cur_hi, volA = vals[0][1], vals[0][2]
        for (lo, hi, vol) in vals[1:]:
            if lo > cur_hi:
                volB = total - volA
                gap = lo - cur_hi
                if volA > 0 and volB > 0:
                    cand = (min(volA, volB) / total, gap, phi, cur_hi, lo)
                    if best is None or cand > best:
                        best = cand
            cur_hi = max(cur_hi, hi)
            volA += vol
    if best is None:
        print("no single-slab separation among canonical directions "
              "(disconnection may need a piecewise certificate)")
        return
    share, gap, phi, th1, th2 = best
    print(f"CERTIFIED DISCONNECTION: phi = {tuple(str(x) for x in phi)}")
    print(f"  X_T ∩ {{{float(th1):.6f} < phi < {float(th2):.6f}}} = ∅ "
          f"(gap {float(gap):.2e}, exact)")
    print(f"  smaller side carries {float(share):.4f} of vol(X_T); "
          f"vol(X_T) = {float(total):.3e}")
    print(f"  balance: worst pyramid-pair share per round = "
          f"{[round(float(w), 3) for w in balance_log]}")
    print(f"  alpha (min over rounds) = {float(min(balance_log)):.4f}")


if __name__ == "__main__":
    main()
