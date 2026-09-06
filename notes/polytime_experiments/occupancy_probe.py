"""Deep-straddler occupancy probe - the (A1'') quantity, measured directly.

The general annealed theorem's one open piece (notes/smoothed.md #4d):
fully-straddling m-tied cells branch at m/2 (supercritical for m >= 3), so
the theorem needs E[straddling rounds per lineage] = O(1). The proof frame
is penetration-renewal: every split evicts every offset to the piece
boundary (pyr_mem_halfspace, Lean - definitional), so re-straddling needs
fresh penetration, budgeted at 2*delta/round (marching bound). The missing
inequality is a negative conditional drift of penetration for survivors
(the FW-refill response). This instrument measures:

  strad   - straddling tracked cells per round (kept points in >= 2
            pyramids of the new cut);
  deepstr - straddling cells with median tie depth >= 3 at step scale
            (the supercritical class);
  runs    - histogram of consecutive-straddling run lengths per lineage
            (prediction: mean O(1), geometric-ish tail for annealed;
            fatter for the adversarial ladder-climber);
  minfrac - the minority-side point fraction of each straddle (birth-grade
            requires >= THRESH/cellmass); its lag-1 drift for lineages
            straddling in consecutive rounds (prediction: negative drift
            for annealed - eviction + refill re-centering).

Usage: [venv]/python occupancy_probe.py [quick]
"""
import sys
import numpy as np
import adversary_game as G
from cells_adversarial import cell_sig, ssg_cuts

THRESH = 0.002
WANT = 5000
CAP = 4e8


def probe(label, cuts, d, rng, t_lo=2, t_hi=None):
    if t_hi is None:
        t_hi = len(cuts)
    prev_strad = {}   # sig tuple -> (run len, minority frac, birth-run len)
    runs_done = []    # completed run lengths
    drifts = []       # lag-1 minority-fraction changes for survivors
    bruns = []        # birth-grade consecutive-run lengths (running max)
    print(f"=== {label}: deep-straddler occupancy ===")
    print(f"{'t':>3} {'#mc':>4} {'strad':>5} {'deepstr':>7} {'birth':>6} "
          f"{'D~':>5} {'runmax':>6} {'mf_med':>6}")
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
        nstrad = ndeep = nbirth = 0
        mfracs = []
        cur_strad = {}
        depth_sum, depth_n = 0.0, 0
        for j in mc:
            m = inv == j
            pts = S[m]
            # tie depth at previous apex, step scale
            A = np.abs(pts - c_prev[None, :])
            A = -np.sort(-A, axis=1)
            depth = float(np.median((A >= (A[:, :1] - 2 * delta)).sum(1)))
            depth_sum += depth
            depth_n += 1
            kj = kept[m]
            if not kj.sum():
                continue
            W = s_new[None, :] * (pts[kj] - c_new[None, :])
            W = np.where((s_new != 0)[None, :], W, -np.inf)
            idx = W.argmax(1)
            pyrs, pcounts = np.unique(idx, return_counts=True)
            if len(pyrs) > 1:
                nstrad += 1
                if depth >= 3:
                    ndeep += 1
                mf = float(pcounts.min() / pcounts.sum())
                mfracs.append(mf)
                # birth-grade: >= 2 pyramid pieces each above the tracking
                # threshold (in points of the round's total sample)
                bgrade = int((pcounts >= THRESH * len(S)).sum()) >= 2
                nbirth += int(bgrade)
                key = tuple(u[j])
                par = tuple(u[j][:t - 1])
                if par in prev_strad:
                    run, mf_old, brun = prev_strad[par]
                    cur_strad[key] = (run + 1, mf,
                                      brun + 1 if bgrade else 0)
                    drifts.append(mf - mf_old)
                    if bgrade and brun + 1 > 0:
                        bruns.append(brun + 1)
                else:
                    cur_strad[key] = (1, mf, 1 if bgrade else 0)
                    if bgrade:
                        bruns.append(1)
        # close runs that ended (no straddle continuation)
        continued_pars = {k[:t - 1] for k in cur_strad}
        for par, (run, _, _) in prev_strad.items():
            if par not in continued_pars:
                runs_done.append(run)
        # re-key prev by current signatures for next round's parent check
        prev_strad = cur_strad
        mfm = float(np.median(mfracs)) if mfracs else float("nan")
        runmax = max((r for r, _, _ in cur_strad.values()), default=0)
        print(f"{t:>3} {len(mc):>4} {nstrad:>5} {ndeep:>7} {nbirth:>6} "
              f"{depth_sum / max(depth_n, 1):>5.2f} {runmax:>6} {mfm:>6.3f}",
              flush=True)
    runs_done.extend(r for r, _, _ in prev_strad.values())
    ra = np.array(runs_done) if runs_done else np.array([0])
    da = np.array(drifts) if drifts else np.array([np.nan])
    hist = {int(x): int((ra == x).sum()) for x in sorted(set(ra.tolist()))}
    print(f"  RUNS {label}: n={len(ra)} mean={ra.mean():.2f} "
          f"max={ra.max()} dist={hist}")
    print(f"  DRIFT {label}: n={len(da)} mean={np.nanmean(da):+.4f} "
          f"med={np.nanmedian(da):+.4f} frac<0={np.nanmean(da < 0):.2f}")
    ba = np.array(bruns) if bruns else np.array([0])
    bh = {int(x): int((ba == x).sum()) for x in sorted(set(ba.tolist()))}
    print(f"  BIRTH-GRADE RUNS {label}: n={len(ba)} mean={ba.mean():.2f} "
          f"max={ba.max()} dist={bh}")


if __name__ == "__main__":
    quick = "quick" in sys.argv[1:]
    d, T = (5, 8) if quick else (6, 14)
    rng = np.random.default_rng(37)
    runs = [("randbal  d=%d" % d, G.play(d, 1, T, mode="randbal",
                                         verbose=False)[1])]
    if not quick:
        runs += [
            ("ssg       d=6", ssg_cuts(6, 1, T, np.random.default_rng(7))),
            ("cellmax   d=6", G.play(6, 1, T, mode="cellmax",
                                     verbose=False)[1]),
        ]
    for label, cuts in runs:
        probe(label, cuts, d, rng)
