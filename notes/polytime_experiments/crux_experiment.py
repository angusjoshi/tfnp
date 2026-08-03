r"""crux-prover's decisive experiment (notes/crux_scalefree.md §6).

(A) VALIDATE the exact identities on exact-rejection samples of X_t:
  Identity 1':  delta(v) := v'Sigma(K')v - v'Sigma(X)v  ==  sig_v^2 (a(v) - rho(v)^2)
     where, with t=v.y, tbar=t-E[t], s=tbar/sig_v (sig_v^2=v'Sigma v), sigma=+1 on
     kept K' / -1 on removed R (the balanced cut split), a(v)=E[s^2 sigma],
     rho(v)=E[s sigma]=Cov(s,sigma).
  T3 factor:   c(v) := v'Sigma(K')v / v'Sigma(X)v == 1 + a(v) - rho(v)^2.
  Lemma 2:     Delta' Sigma^{-1} Delta <= 4   (Delta = m_K - m_R). Report MAX.
  Also: sign-fold sigma_fold = sgn(max_i w_i + min_i w_i), w=s*(y-c); report its
  agreement with the actual K_ok split (they coincide when all coords active).

  Projected variances are along the FIXED eigenvectors of the full-sample cov, so
  they are UNBIASED at any n (unlike a min-eigenvalue) -> no Marchenko-Pastur
  confound on the identity checks or on rho/a.

(B) MEAN-REVERSION LINCHPIN. Per round record kappa, rho(v_max), rho(v_min),
  a(v_min), c(v_min); track FRESH next-round kappa (reliable) for Delta_kappa.
  Question: is high kappa associated with LARGE |rho(v_max)| (long axis SENSED)
  followed by a kappa DROP next round (mean-reversion real)? OR does high kappa
  co-occur with rho(v_max)~0 (long axis BLIND) PERSISTING >=2 consecutive rounds
  (the counterexample shape)?

Usage: python crux_experiment.py <d> <delta> <R> [seed] [kind]   kind: ssg|topical
CAPS: d<=6, R<=10, N>=400, batch 50k, 3M draws/round, one foreground job.
"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import (make_ssg, make_topical, fixed_point, make_cut, in_X,
                    balanced, K_ok)

BLIND = 0.15      # |rho| below this = long axis BLIND to the cut
SENSED = 0.30     # |rho| above this = long axis SENSED


def rej_sample(cuts, d, want, rng, cap=3_000_000, batch=50_000):
    out = []; tries = 0
    while len(out) < want and tries < cap:
        P = rng.uniform(0, 1, size=(batch, d)); tries += batch
        out.extend(P[in_X(P, cuts)])
    return (np.array(out[:want]) if out else np.zeros((0, d))), len(out) / max(tries, 1)


def dir_stats(S, v, SX, keep):
    """a(v), rho(v), sig_v^2, and the identity LHS/RHS along fixed direction v."""
    t = S @ v
    tbar = t - t.mean()
    sigv2 = float(v @ SX @ v)
    sigv = np.sqrt(max(sigv2, 1e-18))
    sstd = tbar / sigv
    sigma = np.where(keep, 1.0, -1.0)
    rho = float(np.mean(sstd * sigma))
    a = float(np.mean(sstd * sstd * sigma))
    # identity: delta(v) = v'cov(K')v - sigv2  ==  sigv2*(a - rho^2)
    Kp = S[keep]
    vKv = float(v @ np.cov(Kp.T) @ v)
    delta_v = vKv - sigv2
    rhs = sigv2 * (a - rho * rho)
    c_v = vKv / max(sigv2, 1e-18)              # T3 factor, actual
    c_pred = 1.0 + a - rho * rho               # T3 factor, from a,rho
    return dict(a=a, rho=rho, sigv2=sigv2, delta_v=delta_v, rhs=rhs,
                c_v=c_v, c_pred=c_pred, id_resid=delta_v - rhs)


def run(d, delta, R, seed, kind):
    rng = np.random.default_rng(seed)
    f, _ = (make_ssg if kind == 'ssg' else make_topical)(d, delta, seed)
    xstar = fixed_point(f, d)
    cuts = []
    print(f"[{kind} d={d} delta={delta} seed={seed}] x*={np.round(xstar,3)}", flush=True)
    rows = []
    max_mah = 0.0
    max_idresid = 0.0
    fold_agree = []
    for t in range(R):
        want = 500                                   # N>=400
        S, acc = rej_sample(cuts, d, want, rng)
        if len(S) < 200:
            print(f"  r{t:2d}: acc={acc:.1e} n={len(S)} too low; stop", flush=True); break
        SX = np.cov(S.T)
        w, V = np.linalg.eigh(SX)
        lam_min, lam_max = float(w[0]), float(w[-1])
        kappa = lam_max / max(lam_min, 1e-18)
        vmin, vmax = V[:, 0], V[:, -1]
        bp = balanced(S, d)
        c_, s_, vmag = make_cut(f, bp)
        keep = K_ok(S, c_, s_)
        fk = float(keep.mean())
        nact = int((s_ != 0).sum())
        if keep.sum() < d + 2 or (~keep).sum() < d + 2 or vmag < 1e-11:
            print(f"  r{t:2d} acc={acc:.1e} n={len(S)} kappa={kappa:7.2f} "
                  f"(converged/degenerate: vmag={vmag:.1e})", flush=True)
            if vmag < 1e-11:
                break
            cuts.append((c_, s_)); continue
        # sign-fold agreement
        wf = s_[None, :] * (S - c_[None, :])
        g = wf.max(1) + wf.min(1)
        sigma_fold = g >= 0
        agree = float(np.mean(sigma_fold == keep))
        fold_agree.append(agree)
        # per-direction stats
        smin = dir_stats(S, vmin, SX, keep)
        smax = dir_stats(S, vmax, SX, keep)
        # Lemma 2
        Delta = S[keep].mean(0) - S[~keep].mean(0)
        mah = float(Delta @ np.linalg.solve(SX, Delta))
        max_mah = max(max_mah, mah)
        max_idresid = max(max_idresid, abs(smin['id_resid']), abs(smax['id_resid']))
        rows.append(dict(t=t, kappa=kappa, lam_min=lam_min,
                         rho_vmax=smax['rho'], rho_vmin=smin['rho'],
                         a_vmin=smin['a'], c_vmin=smin['c_v'],
                         c_vmin_pred=smin['c_pred'], mah=mah, fk=fk, nact=nact))
        print(f"  r{t:2d} acc={acc:.1e} n={len(S)} kappa={kappa:7.3f} fk={fk:.3f} nact={nact} "
              f"agree={agree:.2f}\n"
              f"       |rho(vmax)|={abs(smax['rho']):.3f} rho(vmin)={smin['rho']:+.3f} "
              f"a(vmin)={smin['a']:+.3f} c(vmin)={smin['c_v']:.3f}(pred {smin['c_pred']:.3f}) "
              f"mah(D'S^-1 D)={mah:.3f}\n"
              f"       ID resid: vmin={smin['id_resid']:+.2e} vmax={smax['id_resid']:+.2e}",
              flush=True)
        cuts.append((c_, s_))
    # ---- summary + mean-reversion analysis ----
    if len(rows) >= 2:
        kap = np.array([r['kappa'] for r in rows])
        rvmax = np.array([abs(r['rho_vmax']) for r in rows])
        rvmin = np.array([abs(r['rho_vmin']) for r in rows])
        avmin = np.array([r['a_vmin'] for r in rows])
        dkap = np.diff(kap)                        # next-round change (fresh kappa)
        kmed = np.median(kap)
        print(f"\n  SUMMARY {kind} d={d} seed={seed}: kappa [{kap.min():.2f},{kap.max():.2f}] "
              f"median={kmed:.2f}", flush=True)
        print(f"    Identity 1' max |resid| = {max_idresid:.2e}; "
              f"Lemma2 MAX D'S^-1 D = {max_mah:.3f} (bound 4); "
              f"c(vmin) pred-vs-actual max|err|="
              f"{max(abs(r['c_vmin']-r['c_vmin_pred']) for r in rows):.2e}; "
              f"fold-agree min={min(fold_agree):.2f}", flush=True)
        # association: high kappa <-> |rho(vmax)| ?
        if len(kap) >= 3:
            cc_kr = np.corrcoef(kap, rvmax)[0, 1]
            print(f"    corr(kappa, |rho(vmax)|) = {cc_kr:+.2f}  "
                  f"(>0: high kappa => long axis SENSED)", flush=True)
        # does high kappa predict a DROP next round? corr(kappa_t, dkappa_t)
        if len(dkap) >= 2:
            cc_kd = np.corrcoef(kap[:-1], dkap)[0, 1]
            print(f"    corr(kappa_t, Delta_kappa_next) = {cc_kd:+.2f}  "
                  f"(<0: mean-reversion — high kappa followed by drop)", flush=True)
            # when |rho(vmax)| large at high kappa, does kappa drop next?
            hi = kap[:-1] >= kmed
            sensed_hi = hi & (rvmax[:-1] >= SENSED)
            blind_hi = hi & (rvmax[:-1] <= BLIND)
            if sensed_hi.any():
                print(f"    high-kappa & SENSED vmax rounds: {int(sensed_hi.sum())}, "
                      f"mean Delta_kappa_next={dkap[sensed_hi].mean():+.3f}", flush=True)
            if blind_hi.any():
                print(f"    high-kappa & BLIND  vmax rounds: {int(blind_hi.sum())}, "
                      f"mean Delta_kappa_next={dkap[blind_hi].mean():+.3f}", flush=True)
        # PERSISTENCE of the counterexample shape: consecutive rounds with
        # long axis BLIND while kappa elevated (>= median)
        bad = (rvmax <= BLIND) & (kap >= kmed)
        run_len = mx = 0
        for b in bad:
            run_len = run_len + 1 if b else 0
            mx = max(mx, run_len)
        print(f"    PERSISTENCE: max consecutive rounds [vmax BLIND & kappa>=median] = {mx} "
              f"({'>1 => counterexample shape present' if mx > 1 else '<=1 => not persistent'})",
              flush=True)
        # also: is vmin (thin axis) sensed when kappa high? (danger per Cor 2')
        thin_sensed_hi = (kap >= kmed) & (rvmin >= SENSED)
        print(f"    thin-axis (vmin) SENSED while kappa>=median: "
              f"{int(thin_sensed_hi.sum())}/{int((kap>=kmed).sum())} rounds", flush=True)
    return rows


if __name__ == '__main__':
    d = int(sys.argv[1]); delta = float(sys.argv[2]); R = int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    kind = sys.argv[5] if len(sys.argv) > 5 else 'ssg'
    run(d, delta, R, seed, kind)
