"""The atomic lopsidedness law: how many mass-carrying children does each
mass-carrying cell spawn per round?

Additive total growth with ~80% of cells crossed forces per-cell
lopsidedness: multiplicity ~1 for almost all mass-carrying cells. This
measures the multiplicity profile exactly per round (float volumes are fine
here; the exact-rational machinery certifies specific instances).

Usage: python split_multiplicity.py
"""
import numpy as np
import adversary_game as G
from cells_adversarial import cell_sig, ssg_cuts

THRESH = 0.002    # mass-carrying = cell mass share >= THRESH


for label, d, mk in [
    ("ssg     d=6", 6, lambda: ssg_cuts(6, 1, 14, np.random.default_rng(7))),
    ("cellmax d=6", 6,
     lambda: G.play(6, 1, 14, mode="cellmax", verbose=False)[1]),
    ("adv     d=6", 6,
     lambda: G.play(6, 1, 14, mode="adversary", verbose=False)[1]),
]:
    cuts = mk()
    rng = np.random.default_rng(777)
    print(f"=== {label}: mass-carrying split multiplicity ===")
    print(f"{'t':>3} {'#mc':>4} {'crossed':>7} {'mult=1':>6} {'mult=2':>6} "
          f"{'mult>=3':>7} {'new mc':>6}")
    for t in range(3, len(cuts), 3):
        S, _ = G.rejection_sample(cuts[:t], d, rng, want=4000, cap=5e8)
        if len(S) < 800:
            print(f"{t:>3}  exhausted")
            break
        sig_t = cell_sig(S, cuts[:t])
        c_next, s_next = cuts[t]
        kept = G.K_ok(S, c_next, s_next)
        sig_next = cell_sig(S[kept], cuts[:t + 1])
        # parent cells (mass-carrying)
        u_t, inv_t = np.unique(sig_t, axis=0, return_inverse=True)
        counts_t = np.bincount(inv_t)
        mc_parents = {tuple(u_t[j]) for j in range(len(u_t))
                      if counts_t[j] / len(S) >= THRESH}
        # children grouping: parent sig = first t coords of child sig
        u_n, inv_n = np.unique(sig_next, axis=0, return_inverse=True)
        counts_n = np.bincount(inv_n)
        child_of = {}
        for j in range(len(u_n)):
            if counts_n[j] / len(S) < THRESH:   # mass share vs pre-cut total
                continue
            par = tuple(u_n[j][:t])
            child_of.setdefault(par, []).append(counts_n[j])
        mult = {p: len(chs) for p, chs in child_of.items() if p in mc_parents}
        crossed = 0
        for p in mc_parents:
            # crossed = parent's kept points fall in >1 pyramid piece OR lost mass
            pts = np.all(sig_t == np.array(p), axis=1)
            kpts = kept & pts
            if kpts.sum() and kpts.sum() < pts.sum():
                crossed += 1
            elif p in child_of and len(child_of[p]) > 1:
                crossed += 1
        m1 = sum(1 for m in mult.values() if m == 1)
        m2 = sum(1 for m in mult.values() if m == 2)
        m3p = sum(1 for m in mult.values() if m >= 3)
        newmc = sum(len(v) for p, v in child_of.items() if p in mc_parents) \
            - len(mult)
        print(f"{t:>3} {len(mc_parents):>4} {crossed:>7} {m1:>6} {m2:>6} "
              f"{m3p:>7} {newmc:>6}", flush=True)
