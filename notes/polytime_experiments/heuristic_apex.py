"""Heuristic (sampler-free) balanced points: can an apex computed from the
cut HISTORY alone achieve 1/poly worst-case progress?

The history determines X_t exactly, so this is a computation question, not an
information one. Candidates, in decreasing use of mass information:

  samp   - weighted FW of an exact-rejection sample (the real algorithm;
           ground-truth baseline);
  cheb   - FW of cell Chebyshev CENTERS weighted by r^d (cheap volume proxy:
           inscribed-ball volume; no MCMC, no sampling);
  unif   - FW of cell Chebyshev centers, uniform weights (pure combinatorics);
  hist   - FW of the past query apexes {c^r} (no cells at all);
  prev   - previous apex (degenerate control).

Progress metric per prefix t (exact-rejection ground truth): the MINORITY
COUNT of the apex = sum_i min(n_i^+, n_i^-)/N = provable worst-case removal
over all sign vectors (Lean: card_removed_le_sum_min). A rule is viable iff
this stays >= 1/poly.

Cells are discovered from the ground-truth sample (favourable to the
heuristics: they get the true mass-carrying cell list for free; a real
implementation would enumerate the cell tree).

Usage: python heuristic_apex.py
"""
import sys
import numpy as np
from scipy.optimize import linprog
import adversary_game as G
from cells_adversarial import cell_sig, ssg_cuts
from telescope_algo import box_rows, pyramid_rows, fw_apex_weighted


def chebyshev(A, b):
    m, d = A.shape
    norms = np.linalg.norm(A, axis=1)
    Aub = np.hstack([-A, norms[:, None]])
    res = linprog(np.concatenate([np.zeros(d), [-1.0]]), A_ub=Aub, b_ub=-b,
                  bounds=[(None, None)] * d + [(0, None)], method="highs")
    if not res.success or res.x[d] < 1e-12:
        return None, 0.0
    return res.x[:d], float(res.x[d])


def minority(S, c):
    D = S - c[None, :]
    arg = np.abs(D).argmax(1)
    sgn = np.sign(D[np.arange(len(S)), arg])
    d = S.shape[1]
    npos = np.array([np.sum((arg == m) & (sgn > 0)) for m in range(d)])
    nneg = np.array([np.sum((arg == m) & (sgn <= 0)) for m in range(d)])
    return float(np.minimum(npos, nneg).sum()) / len(S)


def cell_centers(S, cuts, d, kmax=350):
    sig = cell_sig(S, cuts)
    uc, inv = np.unique(sig, axis=0, return_inverse=True)
    counts = np.bincount(inv)
    order = np.argsort(-counts)[:kmax]
    Ab, bb = box_rows(d)
    ctrs, rads = [], []
    for j in order:
        A, b = list(Ab), list(bb)
        for (cc, ss), i in zip(cuts, uc[j]):
            Ar, br = pyramid_rows(cc, ss, int(i), d)
            A.extend(Ar); b.extend(br)
        ctr, r = chebyshev(np.array(A), np.array(b))
        if ctr is not None:
            ctrs.append(ctr); rads.append(r)
    return np.array(ctrs), np.array(rads)


def apexes(S, cuts, d):
    out = {}
    N = len(S)
    w = np.full(min(N, 350), 1.0 / min(N, 350))
    out["samp"] = fw_apex_weighted(S[:350], w)
    ctrs, rads = cell_centers(S, cuts, d)
    if len(ctrs) >= 2:
        wv = rads ** d
        wv = wv / wv.sum()
        out["cheb"] = fw_apex_weighted(ctrs, wv)
        out["unif"] = fw_apex_weighted(ctrs, np.full(len(ctrs), 1.0 / len(ctrs)))
    hist = np.array([c for (c, s) in cuts])
    out["hist"] = fw_apex_weighted(hist, np.full(len(hist), 1.0 / len(hist)))
    out["prev"] = cuts[-1][0]
    return out


def main():
    rng = np.random.default_rng(31337)
    names = ["samp", "cheb", "unif", "hist", "prev"]
    for label, d, T, mk in [
        ("ssg  d=5", 5, 12, lambda: ssg_cuts(5, 1, 12, np.random.default_rng(7))),
        ("ssg  d=6", 6, 12, lambda: ssg_cuts(6, 1, 12, np.random.default_rng(7))),
        ("adv  d=6", 6, 12,
         lambda: G.play(6, 1, 12, mode="adversary", verbose=False)[1]),
    ]:
        cuts = mk()
        print(f"=== {label}: minority count (worst-case removal) per apex ===")
        print(f"{'t':>3}" + "".join(f" {n:>7}" for n in names))
        for t in range(3, len(cuts) + 1, 3):
            S, _ = G.rejection_sample(cuts[:t], d, rng, want=2000)
            if len(S) < 400:
                print(f"{t:>3}  exhausted")
                break
            ap = apexes(S, cuts[:t], d)
            row = f"{t:>3}"
            for n in names:
                row += f" {minority(S, ap[n]):>7.3f}" if n in ap else f" {'-':>7}"
            print(row, flush=True)


if __name__ == "__main__":
    main()


# ---------- closed-loop test: cut AT the unif apex, in-window ----------
def closed_loop(d, T, seed):
    """Run the actual game with apex = FW of cell Chebyshev centers (uniform
    weights). Exact rejection is used only for cell discovery and metrics -
    the apex never sees masses. Oracle: random SSG with known x*."""
    from common import make_ssg, fixed_point
    f, _ = make_ssg(d, 1e-4, seed)
    xstar = fixed_point(f, d)
    rng = np.random.default_rng(seed + 555)
    cuts = []
    print(f"=== closed-loop unif-cell apex, d={d} ssg seed={seed} ===")
    for t in range(1, T + 1):
        S, _ = G.rejection_sample(cuts, d, rng, want=2000)
        if len(S) < 400:
            print(f"  t={t}: exhausted")
            break
        if not cuts:
            c = np.full(d, 0.5)
        else:
            ctrs, _ = cell_centers(S, cuts, d)
            if len(ctrs) < 2:
                c = S[:350].mean(0)
            else:
                c = fw_apex_weighted(ctrs, np.full(len(ctrs), 1.0 / len(ctrs)))
        c = np.clip(c, 1e-6, 1 - 1e-6)
        mino = minority(S, c)
        v = f(c) - c
        s = np.sign(v)
        s[np.abs(v) < 1e-12] = 0.0
        kept = G.K_ok(S, c, s).mean()
        cuts.append((c.copy(), s.copy()))
        print(f"  t={t:>2} minority={mino:.3f} kept={kept:.3f} "
              f"|c-x*|={np.abs(c - xstar).max():.4f}", flush=True)


if len(sys.argv) > 1 and sys.argv[1] == "loop":
    closed_loop(5, 13, 1)
    closed_loop(6, 13, 1)
