"""Condition-Number Transfer go/no-go (notes/ssg_directions.md §7):
does the SSG value-separation gap delta control our geometric conditioning?
i.e. is 1/kappa(X_t) >~ delta^O(1) and h_iso(X_t) >~ delta^O(1)?

Per instance (make_ssg_full, EXACT rejection ground truth): compute delta at x*,
run the real balanced-cut algorithm to Rmax rounds, and at chosen measurement
rounds record 1/kappa(X_t) and h_iso(X_t). Appends CSV rows to a data file so a
separate regress step can fit log(1/kappa) & log(h_iso) vs log(delta).

REFUTING case to watch: delta bounded away from 0 but kappa blows up / h collapses
(a dumbbell with a healthy value gap) => bridge refuted.

Usage: python condition_transfer.py <d> <disc(1-gamma)> <seeds_csv> <Rmax> <meas_csv> <outfile>
CAPS: d<=6, Rmax<=6, N<=400, batch<=50k, draws<=3M, one foreground job.
"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (make_ssg_full, ssg_value_gap, fixed_point, make_cut, in_X,
                    balanced, marginal_cheeger, candidate_directions)


def rej_sample(cuts, d, want, rng, cap=3_000_000, batch=50_000):
    out = []; tries = 0
    while len(out) < want and tries < cap:
        P = rng.uniform(0, 1, size=(batch, d)); tries += batch
        out.extend(P[in_X(P, cuts)])
    return (np.array(out[:want]) if out else np.zeros((0, d))), len(out) / max(tries, 1)


def kappa_inv(S):
    C = np.cov(S.T)
    w = np.clip(np.linalg.eigvalsh(C), 1e-15, None)
    return float(w.min() / w.max())          # 1/kappa (scale-free)


def run_instance(d, disc, seed, Rmax, meas, out_rows, rng):
    f, types, succ, rew, gamma = make_ssg_full(d, disc, seed)
    xstar = fixed_point(f, d)
    delta, gaps = ssg_value_gap(xstar, types, succ)
    nmaxmin = int((types != 2).sum())
    print(f"[d={d} 1-g={disc:g} seed={seed}] x*={np.round(xstar,3)} "
          f"delta={delta:.4e} (#MAX/MIN={nmaxmin}, gaps min..max="
          f"{min(gaps) if gaps else float('nan'):.3e}.."
          f"{max(gaps) if gaps else float('nan'):.3e})", flush=True)
    cuts = []; start = np.full(d, 0.5)
    for t in range(Rmax + 1):
        want = 400
        S, acc = rej_sample(cuts, d, want, rng)
        if len(S) < 120:
            print(f"  r{t}: acc={acc:.1e} n={len(S)} too low; stop", flush=True); break
        if t in meas:
            ik = kappa_inv(S)
            dirs = candidate_directions(S, xstar=xstar, d=d, n_random=200, rng=rng)
            # N<=400: coarse bins + smoothing, else empty interior bins give a
            # SPURIOUS h=0 (sampling gap, not a real conductance-0 bottleneck).
            h_iso, _, _ = marginal_cheeger(S, dirs, min_side=0.08, nbins=24,
                                           smooth=5, isotropic=True)
            print(f"  MEAS r{t}: acc={acc:.1e} n={len(S)} 1/kappa={ik:.4f} "
                  f"kappa={1/max(ik,1e-18):.2f} h_iso={h_iso:.4f}", flush=True)
            out_rows.append((d, disc, seed, delta, t, ik, h_iso))
        bp = balanced(S, d)
        c_, s_, vmag = make_cut(f, bp)
        if vmag < 1e-11:
            print(f"  r{t}: converged (||f(bp)-bp||={vmag:.1e})", flush=True); break
        cuts.append((c_, s_)); start = bp.copy()


def main():
    d = int(sys.argv[1]); disc = float(sys.argv[2])
    seeds = [int(x) for x in sys.argv[3].split(',')]
    Rmax = int(sys.argv[4])
    meas = set(int(x) for x in sys.argv[5].split(','))
    outfile = sys.argv[6]
    rng = np.random.default_rng(12345)
    rows = []
    for s in seeds:
        run_instance(d, disc, s, Rmax, meas, rows, rng)
    # append CSV
    hdr = "d,disc,seed,delta,t,inv_kappa,h_iso\n"
    write_hdr = not os.path.exists(outfile)
    with open(outfile, 'a') as fh:
        if write_hdr:
            fh.write(hdr)
        for r in rows:
            fh.write(",".join(str(x) for x in r) + "\n")
    print(f"  wrote {len(rows)} rows -> {outfile}", flush=True)


if __name__ == '__main__':
    main()
