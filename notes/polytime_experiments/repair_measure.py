r"""Repair-attack Target 1: measure the lambda_min trajectory of the REAL algorithm
under exact rejection sampling, and decompose each balanced cut's change in
covariance into the ASYMMETRIC-injection term and the DOWNDATE term.

Exact identity (verified inline): for a balanced 50/50 cut X -> K'=X∩K, R=X∩N,
  Sigma(K') - Sigma(X) = 1/2 (Sigma(K') - Sigma(R))  -  1/4 Delta Delta^T
                         \_____ ASYM ______________/    \___ DOWNDATE ___/
with Delta = m_K - m_R.  DOWNDATE is rank-1 and always REMOVES variance.
ASYM along v is POSITIVE iff the kept half is more spread than the removed half
along v -- this is the only mechanism that can REPAIR a thin axis.

For each cut we evaluate both terms along v_min = argmin eigvec of Sigma(X_t)
(the current thinnest axis) and report:
  - kappa_t, lam_min_t (absolute and relative lam_min/lam_max)
  - asym_v, down_v (the two contributions along v_min)
  - new variance along v_min vs old (ratio); whether asym repaired (>0) and
    whether asym out-paced downdate (asym_v > down_v).

Usage: python repair_measure.py <d> <delta> <R> [seed] [kind]   kind: ssg|topical
"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import make_ssg, make_topical, fixed_point, make_cut, in_X, balanced, K_ok


def rej_sample(cuts, d, want, rng, cap=3_000_000, batch=50_000):
    # RESOURCE CAPS (laptop-safe): batch<=50k, total draws<=3M per call.
    out = []; tries = 0
    while len(out) < want and tries < cap:
        P = rng.uniform(0, 1, size=(batch, d)); tries += batch
        out.extend(P[in_X(P, cuts)])
    acc = len(out) / max(tries, 1)
    return (np.array(out[:want]) if out else np.zeros((0, d))), acc


def run(d, delta, R, seed, kind):
    rng = np.random.default_rng(seed)
    f, _ = (make_ssg if kind == 'ssg' else make_topical)(d, delta, seed)
    xstar = fixed_point(f, d)
    cuts = []
    print(f"[{kind} d={d} delta={delta} seed={seed}] x*={np.round(xstar,3)}", flush=True)
    rows = []
    for t in range(R):
        want = 400            # RESOURCE CAP: sample size N <= 400
        S, acc = rej_sample(cuts, d, want, rng)
        if len(S) < 120:      # need enough for a d<=6 covariance estimate
            print(f"  r{t:2d}: acc={acc:.1e} n={len(S)} too low; stop", flush=True); break
        # covariance of X_t and its spectrum
        SX = np.cov(S.T)
        w, V = np.linalg.eigh(SX)          # ascending
        lam_min, lam_max = float(w[0]), float(w[-1])
        kappa = lam_max / max(lam_min, 1e-18)
        vmin = V[:, 0]                       # current thinnest axis
        # the balanced cut
        bp = balanced(S, d)
        c_, s_, vmag = make_cut(f, bp)
        keep = K_ok(S, c_, s_)
        Kp, Rr = S[keep], S[~keep]
        fk = keep.mean()
        info = f"  r{t:2d} acc={acc:.1e} n={len(S)} kappa={kappa:7.2f} " \
               f"lam_min={lam_min:.3e} lmn/lmx={1/kappa:.3e} fk={fk:.3f}"
        if len(Kp) > d + 2 and len(Rr) > d + 2 and vmag >= 1e-11:
            SK, SR = np.cov(Kp.T), np.cov(Rr.T)
            mK, mR = Kp.mean(0), Rr.mean(0)
            Delta = mK - mR
            # decomposition along vmin
            asym_v = 0.5 * (vmin @ SK @ vmin - vmin @ SR @ vmin)
            down_v = 0.25 * (vmin @ Delta) ** 2
            newvar_v = float(vmin @ SK @ vmin)   # var of X_{t+1} along OLD vmin
            change_v = newvar_v - lam_min
            resid = change_v - (asym_v - down_v)  # identity check ~0
            # actual new spectrum (direction may rotate)
            wk = np.linalg.eigvalsh(SK)
            lam_min_new, lam_max_new = float(wk[0]), float(wk[-1])
            kappa_new = lam_max_new / max(lam_min_new, 1e-18)
            # ---- Target 3: central-cut inequality along v_min ----
            # obstruction identity: v'Sig(K')v = 2 VarX(v) - VarR(v) - 1/2 (v.Delta)^2
            # so v'Sig(K')v >= c * VarX(v) with
            #   c = 2 - ( VarR(v) + 1/2 (v.Delta)^2 ) / VarX(v)  = newvar_v / VarX(v).
            varX_v = lam_min                      # Var_X(v_min) = lam_min by def
            varR_v = float(vmin @ SR @ vmin)      # Var_R(v_min)
            vD2 = float(vmin @ Delta) ** 2        # (v.Delta)^2
            lhs3 = varR_v + 0.5 * vD2             # Var_R + 1/2 (v.Delta)^2
            c_margin = 2.0 - lhs3 / max(varX_v, 1e-18)   # want > 0 (bdd away)
            info += (f"\n        along v_min: asym={asym_v:+.3e} down={down_v:.3e} "
                     f"-> change={change_v:+.3e} (id_resid={resid:+.1e}) "
                     f"newvar/old={newvar_v/max(lam_min,1e-18):.3f}")
            info += (f"\n        T3: VarR={varR_v:.3e} .5(vD)^2={0.5*vD2:.3e} "
                     f"2VarX={2*varX_v:.3e} | LHS/VarX={lhs3/max(varX_v,1e-18):.3f} "
                     f"c={c_margin:+.3f}")
            info += (f"\n        next: kappa'={kappa_new:7.2f} lam_min'={lam_min_new:.3e} "
                     f"| asym>0:{asym_v>0} asym>down:{asym_v>down_v}")
            rows.append(dict(t=t, kappa=kappa, lam_min=lam_min, inv_kappa=1/kappa,
                             asym_v=asym_v, down_v=down_v, change_v=change_v,
                             newratio=newvar_v/max(lam_min,1e-18),
                             kappa_new=kappa_new, lam_min_new=lam_min_new,
                             lammin_ratio=lam_min_new/max(lam_min,1e-18),
                             varR_v=varR_v, vD2=vD2, varX_v=varX_v,
                             c_margin=c_margin))
        print(info, flush=True)
        if vmag < 1e-11:
            print("        (converged: ||f(bp)-bp|| tiny)", flush=True); break
        cuts.append((c_, s_))
    # summary
    if rows:
        inv_k = [r['inv_kappa'] for r in rows]
        kap = [r['kappa'] for r in rows]
        nrep = sum(r['asym_v'] > 0 for r in rows)
        nout = sum(r['asym_v'] > r['down_v'] for r in rows)
        nrat = sum(r['newratio'] >= 0.5 for r in rows)
        print(f"\n  SUMMARY {kind} d={d} seed={seed}: kappa in [{min(kap):.2f},{max(kap):.2f}] "
              f"1/kappa_min={min(inv_k):.3e}", flush=True)
        print(f"    ASYM injected (>0) in {nrep}/{len(rows)} cuts; "
              f"ASYM out-paced DOWN in {nout}/{len(rows)}; "
              f"newvar/old>=0.5 along v_min in {nrat}/{len(rows)}", flush=True)
        # geomean of newvar ratio along vmin (per-cut lam_min-axis survival)
        rr = np.array([max(r['newratio'], 1e-6) for r in rows])
        print(f"    per-cut newvar/old(v_min) geomean={np.exp(np.mean(np.log(rr))):.3f} "
              f"min={rr.min():.3f}", flush=True)
        # Target 3 worst-case: min c margin over all cuts (want > 0, bdd away)
        cm = np.array([r['c_margin'] for r in rows])
        nhold = int((cm > 0).sum())
        print(f"    T3 inequality [VarR+.5(vD)^2 <= (2-c)VarX]: holds(c>0) in "
              f"{nhold}/{len(rows)}; WORST c={cm.min():+.4f} (median={np.median(cm):+.4f})",
              flush=True)
        # ACTUAL lam_min ratio (full new spectrum) vs along-OLD-axis c: gap = migration
        lr = np.array([r['lammin_ratio'] for r in rows])
        print(f"    ACTUAL lam_min'/lam_min (min eigval): geomean={np.exp(np.mean(np.log(lr))):.3f} "
              f"min={lr.min():.3f}  <-- vs along-old-axis c-geomean above "
              f"(gap = thin-axis MIGRATION)", flush=True)
        # per-cut kappa ratio (kept-half kappa vs current): <1 self-correct, >1 degrade
        kr = np.array([r['kappa_new'] / max(r['kappa'], 1e-18) for r in rows])
        print(f"    per-cut kappa'/kappa: geomean={np.exp(np.mean(np.log(kr))):.3f} "
              f"max={kr.max():.3f}  ({int((kr<1).sum())}/{len(rows)} contract)", flush=True)
    return rows


if __name__ == '__main__':
    d = int(sys.argv[1]); delta = float(sys.argv[2]); R = int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    kind = sys.argv[5] if len(sys.argv) > 5 else 'ssg'
    run(d, delta, R, seed, kind)
