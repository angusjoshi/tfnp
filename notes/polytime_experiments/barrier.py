import os
"""Test hand-designed cut families for bottlenecks using EXACT uniform samples
(rejection sampling from the box) -> ground-truth marginal-Cheeger, no mixing.
Also checks realizability-relevant facts (does a claimed x* stay in X)."""
import numpy as np
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import in_X, marginal_cheeger, candidate_directions

def rejection_uniform(cuts, d, N, rng, box=(0.0, 1.0), maxtries=200):
    lo, hi = box
    out = []
    tries = 0
    while len(out) < N and tries < maxtries:
        P = rng.uniform(lo, hi, size=(4 * N, d))
        ok = in_X(P, cuts)
        acc = P[ok]
        out.extend(list(acc))
        tries += 1
    if len(out) == 0:
        return np.empty((0, d)), 0.0
    frac = len(out) / (tries * 4 * N)
    return np.array(out[:N]), frac

def measure(cuts, d, N=12000, seed=0, label="", xstar=None):
    rng = np.random.default_rng(seed)
    S, frac = rejection_uniform(cuts, d, N, rng)
    if len(S) < 500:
        print(f"[{label}] d={d}: too few uniform samples (volfrac~{frac:.1e}) n={len(S)}")
        return None
    dirs = candidate_directions(S, xstar=xstar, n_random=200, rng=rng)
    h, bestdir, info = marginal_cheeger(S, dirs, min_side=0.02)
    # also report the deepest valley allowing small sides (isolated-lobe test)
    h_small, _, info_s = marginal_cheeger(S, dirs, min_side=0.002)
    print(f"[{label}] d={d} n={len(S)} volfrac={frac:.3f}  "
          f"h_hat={h:.3e} (side>=2%)  h_hat={h_small:.3e} (side>=0.2%)  "
          f"bestdir~{np.round(bestdir,2)}")
    return dict(h=h, h_small=h_small, frac=frac, bestdir=bestdir, S=S)

# ---------- cut family builders (centered box [0,1]^d, apex at center 0.5) ----------
def center(d): return np.full(d, 0.5)

def cut_signs(d, signs, c=None):
    c = center(d) if c is None else c
    return (c.copy(), np.array(signs, float))

if __name__ == "__main__":
    print("=== Family A: single cut, all-+1 sign (baseline; should be benign) ===")
    for d in [4, 6, 8]:
        measure([cut_signs(d, [1]*d)], d, label="A", seed=1)

    print("\n=== Family B: d cuts s^r = all +1 except coord r is -1, apex center ===")
    for d in [4, 6, 8, 10]:
        cuts = [cut_signs(d, [1 if i != r else -1 for i in range(d)]) for r in range(d)]
        measure(cuts, d, label="B", seed=2)

    print("\n=== Family C: all 2^? not feasible; use random sign cuts at center ===")
    for d in [4, 6, 8]:
        rng = np.random.default_rng(5)
        cuts = [cut_signs(d, list(rng.choice([-1.0, 1.0], size=d))) for _ in range(d)]
        measure(cuts, d, label="C", seed=3)

    print("\n=== Family D: opposing pair of cuts, apexes offset along diagonal ===")
    # two cuts with opposite sign vectors and offset apexes -> try to carve a waist
    for d in [4, 6, 8]:
        c1 = np.full(d, 0.5) + 0.15
        c2 = np.full(d, 0.5) - 0.15
        cuts = [(np.clip(c1,0,1), np.ones(d)), (np.clip(c2,0,1), -np.ones(d))]
        measure(cuts, d, label="D", seed=4)
