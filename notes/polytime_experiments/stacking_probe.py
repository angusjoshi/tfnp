"""Transverse stacking probe - the (ZONE)-deep residue, measured directly.

The last open quantity in the shed ledger (CHAIN cycles 26-27): per round,
per pencil (pair form phi(y) = y_i + sigma*y_j), how many TRACKED
(mass-carrying) cells have the new offset phi(c_t) in the interior of their
phi-extent? Two counts:

  geoK - geometric containment: tracked cells whose phi-extent interior
         contains the new offset. This is what any static/volumetric proof
         of (ZONE)-deep must bound - every containment is a potential
         mid-extent split.
  dynK - dynamical, per form: tracked cells whose KEPT points span that
         form's pyramid pair (i, j) under the new cut - an actual mid-cell
         crossing by that specific surface.
  birthK - dynK restricted to crossings where BOTH sides retain tracked
         mass (>= THRESH of the round's total): the events that create a
         new tracked lineage, i.e. the L-ledger increments.

geoK >> dynK would quantify the churn no-go: the bound cannot be geometric
(irrelevant forms sit mid-extent constantly) and must come from relevance/
marching dynamics. birthK is the quantity conjecture (*) needs bounded.

Also measures the cycle-31 re-stratification quantities (Tfnp/Restrat.lean,
tie_mem_pair_of_robust / pair_invariant_of_robust):

  robust  - survivor mass whose 3rd coordinate is > 4*delta below the top
            (delta = this round's apex step). THEOREM: this mass cannot
            change its tied pair this round; the scale-free pair-record
            ledger covers it.
  collar4 - mass with 3rd coordinate within 4*delta of the top (the
            doubled-scale collar; the residual the theorem does not cover).
  pairchg - fraction of mass 2-simple at both the old and new apex (at
            scale 2*delta) whose tied PAIR changed across the round.
  viaCollar - fraction of pair-changers that were inside the 4*delta collar
            at the old apex. The theorem forces this to be 1.0 exactly
            (instrument sanity check; deviations = sampling/tolerance).

Usage: [venv]/python stacking_probe.py [quick]
"""
import sys
import numpy as np
import adversary_game as G
from cells_adversarial import cell_sig, ssg_cuts

THRESH = 0.002     # mass-carrying = cell mass share >= THRESH
WANT = 5000        # rejection-sample size per round
CAP = 4e8
TOL = 1e-12


def pair_forms(d):
    """All d(d-1) pencils: (i, j, sigma) with i<j, phi(y) = y_i + sigma*y_j."""
    out = []
    for i in range(d):
        for j in range(i + 1, d):
            out.append((i, j, 1.0))
            out.append((i, j, -1.0))
    return out


def depth_class(S, apex):
    """Per point: sorted |y-apex| descending -> (top-2 indices, gap2, gap3),
    gap2 = top - 2nd, gap3 = top - 3rd."""
    A = np.abs(S - apex[None, :])
    order = np.argsort(-A, axis=1)
    top = A[np.arange(len(S)), order[:, 0]]
    second = A[np.arange(len(S)), order[:, 1]]
    third = A[np.arange(len(S)), order[:, 2]]
    return order[:, :2], top - second, top - third


def probe(label, cuts, d, rng, t_lo=2, t_hi=None):
    if t_hi is None:
        t_hi = len(cuts) - 1
    forms = pair_forms(d)
    print(f"=== {label}: transverse stacking + re-stratification ===")
    print(f"{'t':>3} {'#mc':>4} {'cross':>5} {'geoKmax':>7} {'geoKmu':>6} "
          f"{'dynKmax':>7} {'birthKmx':>8} {'births':>6} {'robust':>6} "
          f"{'collar4':>7} {'m3(2d)':>6} {'pairchg':>7} {'viaCol':>6}")
    for t in range(t_lo, t_hi):
        S, _ = G.rejection_sample(cuts[:t], d, rng, want=WANT, cap=CAP)
        if len(S) < 900:
            print(f"{t:>3}  exhausted ({len(S)} pts)")
            break
        sig = cell_sig(S, cuts[:t])
        u, inv = np.unique(sig, axis=0, return_inverse=True)
        counts = np.bincount(inv)
        mc = [j for j in range(len(u)) if counts[j] / len(S) >= THRESH]
        c_new, s_new = cuts[t]
        c_prev = cuts[t - 1][0]
        delta = np.abs(c_new - c_prev).max()
        kept = G.K_ok(S, c_new, s_new)

        # --- crossing status + per-form split attribution ---
        # form key for the surface between kept pyramids i and j of the new
        # cut: phi(y) = s_i*y_i - s_j*y_j, i.e. (min(i,j), max(i,j), sigma)
        # with phi = y_a + sigma*y_b matching s_a*y_a - s_b*y_b up to sign.
        min_birth = THRESH * len(S)
        crossed = np.zeros(len(mc), dtype=bool)
        masks = []
        dynK = np.zeros(len(forms), dtype=int)
        birthK = np.zeros(len(forms), dtype=int)
        fkey = {(i, j, sg): a for a, (i, j, sg) in enumerate(forms)}
        for a, jcell in enumerate(mc):
            m = inv == jcell
            masks.append(m)
            kj = kept[m]
            if 0 < kj.sum() < m.sum():
                crossed[a] = True
            if not kj.sum():
                continue
            W = s_new[None, :] * (S[m][kj] - c_new[None, :])
            W = np.where((s_new != 0)[None, :], W, -np.inf)
            idx = W.argmax(1)
            pyrs, pcounts = np.unique(idx, return_counts=True)
            if len(pyrs) > 1:
                crossed[a] = True
                for x in range(len(pyrs)):
                    for y in range(x + 1, len(pyrs)):
                        i, j = int(pyrs[x]), int(pyrs[y])
                        lo_, hi_ = min(i, j), max(i, j)
                        # s_i*y_i - s_j*y_j = y_lo + sigma*y_hi up to sign:
                        sg = -1.0 if s_new[lo_] * s_new[hi_] > 0 else 1.0
                        f = fkey[(lo_, hi_, sg)]
                        dynK[f] += 1
                        if pcounts[x] >= min_birth and pcounts[y] >= min_birth:
                            birthK[f] += 1

        # --- per-pencil geometric containment ---
        geoK = np.zeros(len(forms), dtype=int)
        for fidx, (i, j, sg) in enumerate(forms):
            off = c_new[i] + sg * c_new[j]
            phi = S[:, i] + sg * S[:, j]
            for a, m in enumerate(masks):
                pv = phi[m]
                if pv.min() + TOL < off < pv.max() - TOL:
                    geoK[fidx] += 1
        act = geoK > 0
        geo_mu = geoK[act].mean() if act.any() else 0.0

        # --- re-stratification block (classify at old apex, step scale) ---
        pair_o, gap2_o, gap3_o = depth_class(S, c_prev)
        robust = float((gap3_o > 4 * delta).mean())
        collar4 = float((gap3_o <= 4 * delta).mean())
        m3_2d = float((gap3_o <= 2 * delta).mean())
        # 2-simple at old apex: 2nd within 2d of top, 3rd more than 2d below
        simple_o = (gap2_o <= 2 * delta) & (gap3_o > 2 * delta)
        Sk = S[kept]
        if len(Sk) > 50 and simple_o[kept].sum() > 50:
            pair_n, gap2_n, gap3_n = depth_class(Sk, c_new)
            simple_n = (gap2_n <= 2 * delta) & (gap3_n > 2 * delta)
            both = simple_o[kept] & simple_n
            if both.sum() > 25:
                po = pair_o[kept][both]
                pn = pair_n[both]
                chg = ~np.all(np.sort(po, 1) == np.sort(pn, 1), axis=1)
                pairchg = float(chg.mean())
                if chg.sum():
                    g3 = gap3_o[kept][both][chg]
                    via = float((g3 <= 4 * delta).mean())
                else:
                    via = float("nan")
            else:
                pairchg, via = float("nan"), float("nan")
        else:
            pairchg, via = float("nan"), float("nan")

        print(f"{t:>3} {len(mc):>4} {int(crossed.sum()):>5} "
              f"{geoK.max():>7} {geo_mu:>6.2f} {dynK.max():>7} "
              f"{birthK.max():>8} {int(birthK.sum()):>6} "
              f"{robust:>6.3f} {collar4:>7.3f} {m3_2d:>6.3f} "
              f"{pairchg:>7.3f} {via:>6.3f}", flush=True)


if __name__ == "__main__":
    quick = "quick" in sys.argv[1:]
    d, T = (5, 8) if quick else (6, 14)
    rng = np.random.default_rng(31)
    runs = [("ssg      d=%d" % d, ssg_cuts(d, 1, T, np.random.default_rng(7)))]
    if not quick:
        runs += [
            ("adversary d=6", G.play(6, 1, T, mode="adversary",
                                     verbose=False)[1]),
            ("cellmax   d=6", G.play(6, 1, T, mode="cellmax",
                                     verbose=False)[1]),
            ("randbal   d=6", G.play(6, 1, T, mode="randbal",
                                     verbose=False)[1]),
        ]
    for label, cuts in runs:
        probe(label, cuts, d, rng)
