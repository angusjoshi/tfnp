"""The collar ledger - per-lineage accounting of the front-birth mechanism.

Cycle-31 sharpening of the open core: births of tracked lineages happen in
the tie front, entries into the tie are TOLLED (gap_lipschitz + the
transition atom: >= 1 full round of collar residence per entry), and the
needed bound is dynamical. Before proving anything, measure the exact
shape. Per tracked lineage (cell identity followed through the signature
tree), this ledger records:

  states  - per round, the lineage's cell stratum from median gaps at the
            current reference, step scale delta = |c_t - c_{t-1}|_inf:
              gap2-front:  med gap2 <= 2*delta   (the only place cells can
                           split at all - the no-split theorem)
              gap3 bands:  tied (<=2d) / collar ((2d,4d]) / robust (>4d)
  births  - rounds where the lineage has >= 2 tracked children (the L
            increments; extra children start new lineages, credited to the
            parent as birth events)
  entries - gap3-band transitions: collar entries (robust -> collar|tied)
            and tie entries (robust|collar -> tied)
  deaths / emergences - tracked lineage with no tracked child / tracked
            cell whose parent signature was not tracked (churn suspects:
            mass climbing back over the threshold)

The target statement this tests: births per lineage = O(1) per tie entry,
and tie entries per lineage small (no rapid in-out oscillation) - the
supermartingale shape of the front-birth inequality. Also tests the
prediction that birth events happen only at gap2-front lineages.

Usage: [venv]/python collar_ledger.py [quick]
"""
import sys
import numpy as np
import adversary_game as G
from cells_adversarial import cell_sig, ssg_cuts

THRESH = 0.002
WANT = 5000
CAP = 4e8


def med_gaps(S, apex):
    """Median over the cell's sample points of gap2 = top-2nd and
    gap3 = top-3rd of |y - apex|."""
    A = np.abs(S - apex[None, :])
    A = -np.sort(-A, axis=1)
    return float(np.median(A[:, 0] - A[:, 1])), \
        float(np.median(A[:, 0] - A[:, 2]))


def band(gap3, delta):
    if gap3 <= 2 * delta:
        return "tied"
    if gap3 <= 4 * delta:
        return "collar"
    return "robust"


def ledger(label, cuts, d, rng, t_lo=2, t_hi=None):
    if t_hi is None:
        t_hi = len(cuts)
    lin = {}          # lineage id -> record dict
    cur = {}          # signature tuple -> lineage id
    next_id = [0]

    def new_lin(t):
        i = next_id[0]
        next_id[0] += 1
        lin[i] = dict(born=t, births=0, tie_in=0, collar_in=0,
                      state=None, front_rounds=0, rounds=0, dead=False)
        return i

    print(f"=== {label}: collar ledger ===")
    print(f"{'t':>3} {'#mc':>4} {'birth':>5} {'death':>5} {'emerg':>5} "
          f"{'tieIn':>5} {'colIn':>5} {'front':>5} "
          f"{'b@front':>7} {'b@tied3':>7} {'b@rob':>5}")
    birth_state2 = {"front": 0, "off": 0}
    birth_state3 = {"tied": 0, "collar": 0, "robust": 0}
    emerg_mass = []   # mass share of emergent cells at detection
    emerg_age = []    # rounds since the lineage last had a tracked ancestor
    tracked_hist = {} # round -> set of tracked signature tuples
    # unnormalized (volume) accounting for the Doob/martingale prediction
    # (notes/smoothed.md #5.1): cumulative emerged volume <= cumulative
    # volume that left the tracked set (annealed self-financing).
    prev_keptvol = {} # parent sig -> unnormalized kept volume under next cut
    cum_in = [0.0]    # emerged volume, in-window origin (tracked ancestor)
    cum_orph = [0.0]  # emerged volume, orphan (initial untracked reservoir)
    cum_out = [0.0]   # tracked volume lost to sub-threshold
    for t in range(t_lo, t_hi):
        S, drawn = G.rejection_sample(cuts[:t], d, rng, want=WANT, cap=CAP)
        if len(S) < 900:
            print(f"{t:>3}  exhausted ({len(S)} pts)")
            break
        vol = len(S) / max(drawn, 1)   # acceptance-rate volume estimate
        sig = cell_sig(S, cuts[:t])
        u, inv = np.unique(sig, axis=0, return_inverse=True)
        counts = np.bincount(inv)
        mc = [j for j in range(len(u)) if counts[j] / len(S) >= THRESH]
        c_ref = cuts[t - 1][0]
        delta = np.abs(cuts[t][0] - c_ref).max() if t < len(cuts) else \
            np.abs(cuts[t - 1][0] - cuts[t - 2][0]).max()

        # group tracked cells by parent signature (first t-1 coords)
        by_parent = {}
        for j in mc:
            par = tuple(u[j][:t - 1])
            by_parent.setdefault(par, []).append(j)

        births = deaths = emerg = tie_in = col_in = 0
        nxt = {}
        parents_seen = set()
        for par, kids in by_parent.items():
            kids.sort(key=lambda j: -counts[j])
            if par in cur:
                lid = cur[par]
                parents_seen.add(par)
                heirs = [(kids[0], lid)]
                if len(kids) > 1:
                    lin[lid]["births"] += len(kids) - 1
                    births += len(kids) - 1
                    st = lin[lid]["state"]
                    if st is not None:
                        birth_state3[st[1]] += len(kids) - 1
                        birth_state2["front" if st[0] else "off"] += \
                            len(kids) - 1
                    for j in kids[1:]:
                        heirs.append((j, new_lin(t)))
            else:
                emerg += len(kids)
                if t > t_lo:
                    for j in kids:
                        emerg_mass.append(counts[j] / len(S))
                        # untracked age: rounds since a tracked ancestor.
                        # flicker = age 1-2; renormalization growth from
                        # far below threshold = larger age. No tracked
                        # ancestor in-window = orphan (initial reservoir).
                        age, found = t - t_lo + 1, False
                        for r in range(t - 1, t_lo - 1, -1):
                            if tuple(u[j][:r]) in tracked_hist.get(r, ()):
                                age, found = t - r, True
                                break
                        emerg_age.append(age)
                        if found:
                            cum_in[0] += counts[j] / len(S) * vol
                        else:
                            cum_orph[0] += counts[j] / len(S) * vol
                heirs = [(j, new_lin(t)) for j in kids]
            for j, lid in heirs:
                m = inv == j
                g2, g3 = med_gaps(S[m], c_ref)
                b3 = band(g3, delta)
                front2 = g2 <= 2 * delta
                prev = lin[lid]["state"]
                if prev is not None:
                    if prev[1] == "robust" and b3 in ("collar", "tied"):
                        lin[lid]["collar_in"] += 1
                        col_in += 1
                    if prev[1] in ("robust", "collar") and b3 == "tied":
                        lin[lid]["tie_in"] += 1
                        tie_in += 1
                lin[lid]["state"] = (front2, b3)
                lin[lid]["rounds"] += 1
                if front2:
                    lin[lid]["front_rounds"] += 1
                nxt[tuple(u[j])] = lid
        for par, lid in cur.items():
            if par not in parents_seen:
                lin[lid]["dead"] = True
                deaths += 1
        # unnormalized outflow: parents' kept volume not reaching a tracked
        # child (died entirely, or partially shed to sub-threshold pieces)
        childvol = {}
        for j in mc:
            par = tuple(u[j][:t - 1])
            childvol[par] = childvol.get(par, 0.0) + counts[j] / len(S) * vol
        for par, kv in prev_keptvol.items():
            cum_out[0] += max(0.0, kv - childvol.get(par, 0.0))
        # this round's tracked cells: kept volume under the next cut
        prev_keptvol = {}
        if t < len(cuts):
            c_nx, s_nx = cuts[t]
            for j in mc:
                m = inv == j
                kf = float(G.K_ok(S[m], c_nx, s_nx).mean())
                prev_keptvol[tuple(u[j])] = counts[j] / len(S) * vol * kf
        cur = nxt
        tracked_hist[t] = {tuple(u[j]) for j in mc}
        nfront = sum(1 for r in lin.values()
                     if not r["dead"] and r["state"] and r["state"][0])
        print(f"{t:>3} {len(mc):>4} {births:>5} {deaths:>5} {emerg:>5} "
              f"{tie_in:>5} {col_in:>5} {nfront:>5} "
              f"{birth_state2['front']:>7} {birth_state3['tied']:>7} "
              f"{birth_state3['robust']:>5}", flush=True)

    live = [r for r in lin.values() if r["rounds"] > 0]
    L = len(live)
    tot_b = sum(r["births"] for r in live)
    tot_tie = sum(r["tie_in"] for r in live)
    tot_col = sum(r["collar_in"] for r in live)
    max_b = max((r["births"] for r in live), default=0)
    max_tie = max((r["tie_in"] for r in live), default=0)
    multi_tie = sum(1 for r in live if r["tie_in"] >= 2)
    print(f"  SUMMARY {label}: L={L} births={tot_b} tieIn={tot_tie} "
          f"collarIn={tot_col} maxBirths/lin={max_b} maxTieIn/lin={max_tie} "
          f"lin's with >=2 tieIn: {multi_tie}")
    print(f"  birth states: gap2-front={birth_state2['front']} "
          f"off-front={birth_state2['off']} | gap3: tied={birth_state3['tied']} "
          f"collar={birth_state3['collar']} robust={birth_state3['robust']}")
    if emerg_mass:
        em = np.array(emerg_mass)
        ea = np.array(emerg_age)
        q = np.percentile(em, [50, 90, 99])
        print(f"  emergence mass (n={len(em)}, THRESH={THRESH}): "
          f"med={q[0]:.4f} p90={q[1]:.4f} p99={q[2]:.4f} max={em.max():.4f} "
          f"<2xTHRESH={float((em < 2*THRESH).mean()):.2f}")
        hist = {a: int((ea == a).sum()) for a in sorted(set(ea.tolist()))}
        print(f"  emergence age (rounds untracked): med={np.median(ea):.1f} "
          f"age1={hist.get(1, 0)} age2={hist.get(2, 0)} "
          f"age>=3={int((ea >= 3).sum())} dist={hist}")
    ratio = cum_in[0] / cum_out[0] if cum_out[0] > 0 else float("nan")
    print(f"  Doob check (unnormalized): emergedVol(in-window)={cum_in[0]:.3e} "
          f"orphanVol={cum_orph[0]:.3e} outflowVol={cum_out[0]:.3e} "
          f"ratio={ratio:.3f} (annealed prediction: <= 1)")


if __name__ == "__main__":
    quick = "quick" in sys.argv[1:]
    d, T = (5, 8) if quick else (6, 14)
    rng = np.random.default_rng(32)
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
        ledger(label, cuts, d, rng)
