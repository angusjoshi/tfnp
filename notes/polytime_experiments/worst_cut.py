import os
"""C2 priority-1: how much can a SINGLE balanced cut inflate the covariance
condition number of a ROUND body? Body = box [0,1]^d (kappa=1 exactly). Center
c = box center (the balanced/FW point of the symmetric box). For every sign
pattern s (all 2^d for small d, else random+greedy), measure
kappa(box ∩ K(c,s)) via exact rejection sampling. Report the worst multiplier.

Also: 'offset' variant where c is moved off-center (still keeping the cut
balanced-ish) to search harder for an elongating cut.
"""
import sys, itertools
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import in_X

def kappa(S):
    w = np.linalg.eigvalsh(np.cov(S.T))
    return float(w.max() / max(w.min(), 1e-18))

def rej(cuts, d, N, rng, maxtries=400):
    out = []; tries = 0
    while len(out) < N and tries < maxtries:
        P = rng.uniform(0, 1, size=(4 * N, d))
        out.extend(list(P[in_X(P, cuts)])); tries += 1
    return (np.array(out[:N]) if out else np.empty((0, d)),
            len(out) / (tries * 4 * N) if tries else 0)

def signs_iter(d, rng, cap=256):
    if 2 ** d <= cap:
        for bits in itertools.product([-1.0, 1.0], repeat=d):
            yield np.array(bits)
    else:
        for _ in range(cap):
            yield rng.choice([-1.0, 1.0], size=d)

def main():
    for d in [3, 4, 5, 6, 8, 10]:
        rng = np.random.default_rng(d)
        c = np.full(d, 0.5)
        worst = (1.0, None, None)
        for s in signs_iter(d, rng):
            S, frac = rej([(c, s)], d, 6000, rng)
            if len(S) < 1000:
                continue
            k = kappa(S)
            if k > worst[0]:
                worst = (k, s.copy(), frac)
        # offset search: random balanced-ish centers
        worst_off = (1.0, None, None)
        for _ in range(60):
            cc = np.clip(0.5 + rng.normal(scale=0.12, size=d), 0.05, 0.95)
            s = rng.choice([-1.0, 1.0], size=d)
            S, frac = rej([(cc, s)], d, 6000, rng)
            if len(S) < 1000:
                continue
            k = kappa(S)
            if k > worst_off[0]:
                worst_off = (k, s.copy(), frac)
        print(f"d={d}: worst kappa(box∩K) center-cut = {worst[0]:.3f} (volfrac~{worst[2]}); "
              f"offset-cut = {worst_off[0]:.3f} (vf~{worst_off[2]})", flush=True)
    print("done", flush=True)

if __name__ == "__main__":
    main()
