r"""mu_W experiment: local stability of the shape map at the equicorrelation fixed
point (crux_scalefree.md sec 8.5). THE decisive number for the conditioning route.

Model one round as the SHAPE map F(Sigma) = renorm(Sigma(X cap K)). Linearize at
the near-fixed-point body via point-cloud SHEAR finite differences (no per-
perturbation resampling): shear the cloud by (I +- eps H), recompute the FW
balanced center, apply the canonical cut {max_i w_i + min_i w_i >= 0}, renorm the
kept-cloud covariance to fixed det, central-difference, and read the Schur scalar
on each S_d isotypic component.

By S_d-representation theory (sec 8.2) the Jacobian is 4 scalars: mu_triv, the two
std eigenvalues, and mu_W (multiplicity-1, the anti-diagonal BLIND mode, sec 8.4).
Decisive: mu_W <= 1  => neutral/random-walk drift (sqrt(t), poly, route alive);
mu_W > 1 => local instability on the blind mode (route in danger).

The symmetric part gives mu_std=mu_W=1 exactly (sec 8.3); the sign of the ASYMMETRIC
correction is what this measures, so it MUST be run on the real (rho-asymmetric)
SSG cut body, not a Gaussian/ellipsoid (which are symmetric => trivially 1).

Usage: python crux_muW.py <d> <delta> <t_round> <seeds_csv> [Nkeep] [Nlp]
CAPS: relaxed N for THIS run (one rejection sample, rest is linear algebra),
      batch 50k, <=3M draws, shallow t so d up to 8 is rejection-cheap.
"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import make_ssg, fixed_point, make_cut, in_X, K_ok, balanced

FRO = lambda A, B: float(np.sum(A * B))          # Frobenius inner product


# ---------- S_d isotypic projections on symmetric matrices ----------
def proj_triv(A):
    d = A.shape[0]
    md = np.mean(np.diag(A))
    off = A - np.diag(np.diag(A))
    mo = np.sum(off) / (d * (d - 1))
    return (md - mo) * np.eye(d) + mo * np.ones((d, d))


def proj_std(A):
    """std isotypic: diagonal (x_i - xbar) + off-diag (u_i+u_j)."""
    d = A.shape[0]
    x = np.diag(A).copy()
    xd = np.diag(x - x.mean())
    off = A - np.diag(np.diag(A))
    s = off.sum(1)                                # row sums of off-diagonal
    abar = off.sum() / (d * (d - 1))
    u = (s - (d - 1) * abar) / (d - 2)
    U = np.add.outer(u, u)                        # u_i + u_j
    np.fill_diagonal(U, 0.0)
    return xd + U


def proj_W(A):
    """W isotypic (pure off-diagonal remainder) = A_off - triv_off - std_off."""
    d = A.shape[0]
    off = A - np.diag(np.diag(A))
    mo = off.sum() / (d * (d - 1))
    s = off.sum(1)
    abar = mo
    u = (s - (d - 1) * abar) / (d - 2)
    U = np.add.outer(u, u); np.fill_diagonal(U, 0.0)
    W = off - mo * (np.ones((d, d)) - np.eye(d)) - U
    return W


def renorm_det(S):
    d = S.shape[0]
    sign, logdet = np.linalg.slogdet(S)
    return S / np.exp(logdet / d)


def rej_sample(cuts, d, want, rng, cap=3_000_000, batch=50_000):
    out = []; tries = 0
    while len(out) < want and tries < cap:
        P = rng.uniform(0, 1, size=(batch, d)); tries += batch
        out.extend(P[in_X(P, cuts)])
    return np.array(out[:want]), len(out) / max(tries, 1)


def cut_cov_renorm(Y, idx, Nlp):
    """recompute FW center on fixed subsample idx, apply canonical cut, renorm cov."""
    c = balanced(Y[idx][:Nlp], Y.shape[1])
    w = Y - c
    keep = (w.max(1) + w.min(1)) >= 0
    Sk = np.cov(Y[keep].T)
    return renorm_det(Sk)


def jacobian_response(Y, H, eps, idx, Nlp):
    """central difference of the shape map along shear H; returns (J_out, J_in)."""
    d = Y.shape[1]
    Yp = Y @ (np.eye(d) + eps * H)
    Ym = Y @ (np.eye(d) - eps * H)
    Sop = cut_cov_renorm(Yp, idx, Nlp)
    Som = cut_cov_renorm(Ym, idx, Nlp)
    Sip = renorm_det(np.cov(Yp.T))
    Sim = renorm_det(np.cov(Ym.T))
    Jout = (Sop - Som) / (2 * eps)
    Jin = (Sip - Sim) / (2 * eps)
    return Jout, Jin


def schur(Jout, Jin, U, proj):
    """Schur scalar on the isotypic of reference direction U (mult-1 exact)."""
    PU = proj(U)
    num = FRO(proj(Jout), PU)
    den = FRO(proj(Jin), PU)
    return num / den if abs(den) > 1e-12 else float('nan')


def run_instance(d, delta, t_round, seed, Nkeep, Nlp, rng):
    f, _ = make_ssg(d, delta, seed)
    xstar = fixed_point(f, d)
    cuts = []
    # build body X_t
    for t in range(t_round):
        S, _ = rej_sample(cuts, d, 2000, rng)
        c = balanced(S[:800], d); cc, s, vm = make_cut(f, c)
        cuts.append((cc, s))
    S, acc = rej_sample(cuts, d, Nkeep, rng)
    if len(S) < 1000:
        print(f"  d={d} seed={seed}: acc={acc:.1e} n={len(S)} too low; skip", flush=True)
        return None
    # the next (studied) cut: FW center + sign; sign-fold to canonical frame
    c = balanced(S[:800], d); cc, s, vm = make_cut(f, c)
    nact = int((s != 0).sum())
    if nact < d:
        print(f"  d={d} seed={seed}: nact={nact}<{d} (not all-active); "
              f"isotypic frame invalid; skip", flush=True)
        return None
    Y = s[None, :] * (S - cc[None, :])           # sign-folded, apex-centered cloud
    Sig = np.cov(Y.T); w = np.linalg.eigvalsh(Sig)
    kappa = w[-1] / w[0]
    idx = np.arange(len(Y))                       # fixed index set for the FW LP
    rng.shuffle(idx)
    # isotypic test perturbations
    Htriv = np.ones((d, d)) - np.eye(d)           # traceless trivial (off-diag ones)
    Hstd = np.zeros((d, d)); Hstd[0, 0] = 1; Hstd[1, 1] = -1        # diag std
    uso = np.zeros(d); uso[0] = 1; uso[1] = -1
    Hso = np.add.outer(uso, uso); np.fill_diagonal(Hso, 0.0)        # off-diag std
    Hoff = np.zeros((d, d)); Hoff[0, 1] = Hoff[1, 0] = 1            # E12 (has W part)

    out = {}
    for eps in (0.05, 0.02):
        Jt_o, Jt_i = jacobian_response(Y, Htriv, eps, idx, Nlp)
        Jsd_o, Jsd_i = jacobian_response(Y, Hstd, eps, idx, Nlp)
        Jso_o, Jso_i = jacobian_response(Y, Hso, eps, idx, Nlp)
        Jw_o, Jw_i = jacobian_response(Y, Hoff, eps, idx, Nlp)
        mu_triv = schur(Jt_o, Jt_i, Htriv, proj_triv)
        mu_W = schur(Jw_o, Jw_i, Hoff, proj_W)
        # std 2x2 block in basis {Hstd(diag), Hso(off)}: rows=output proj, cols=input
        def stdscal(Jo, Ji, Uref):
            return FRO(proj_std(Jo), proj_std(Uref)) / max(FRO(proj_std(Ji), proj_std(Uref)), 1e-12)
        mu_std_diag = stdscal(Jsd_o, Jsd_i, Hstd)
        # leakage: for Hoff input, fraction of output energy outside W
        eW = FRO(proj_W(Jw_o), proj_W(Jw_o))
        eS = FRO(proj_std(Jw_o), proj_std(Jw_o))
        eT = FRO(proj_triv(Jw_o), proj_triv(Jw_o))
        leak = (eS + eT) / max(eW + eS + eT, 1e-18)
        out[eps] = dict(mu_triv=mu_triv, mu_W=mu_W, mu_std=mu_std_diag, leak=leak)
    # Richardson to eps->0 (central diff error O(eps^2))
    e1, e2 = 0.05, 0.02
    def rich(key):
        a, b = out[e1][key], out[e2][key]
        return (e1**2 * b - e2**2 * a) / (e1**2 - e2**2)
    mW0, mstd0, mtriv0 = rich('mu_W'), rich('mu_std'), rich('mu_triv')
    print(f"  d={d} seed={seed} t={t_round}: n={len(S)} acc={acc:.1e} kappa={kappa:.2f} nact={nact}\n"
          f"     mu_W:  eps.05={out[e1]['mu_W']:+.3f} eps.02={out[e2]['mu_W']:+.3f} "
          f"-> Richardson={mW0:+.3f}   (leak={out[e2]['leak']:.2f})\n"
          f"     mu_std(diag): {out[e2]['mu_std']:+.3f}   mu_triv: {out[e2]['mu_triv']:+.3f}",
          flush=True)
    return dict(d=d, seed=seed, kappa=kappa, mu_W=mW0, mu_std=mstd0, mu_triv=mtriv0,
                mu_W_e05=out[e1]['mu_W'], mu_W_e02=out[e2]['mu_W'], leak=out[e2]['leak'])


def main():
    d = int(sys.argv[1]); delta = float(sys.argv[2]); t_round = int(sys.argv[3])
    seeds = [int(x) for x in sys.argv[4].split(',')]
    Nkeep = int(sys.argv[5]) if len(sys.argv) > 5 else 6000
    Nlp = int(sys.argv[6]) if len(sys.argv) > 6 else 1000
    rng = np.random.default_rng(2024)
    rows = []
    print(f"=== mu_W: d={d} delta={delta} t={t_round} seeds={seeds} N={Nkeep} Nlp={Nlp} ===", flush=True)
    for s in seeds:
        r = run_instance(d, delta, t_round, s, Nkeep, Nlp, rng)
        if r: rows.append(r)
    if rows:
        mW = np.array([r['mu_W'] for r in rows])
        print(f"  SUMMARY d={d}: mu_W mean={mW.mean():+.3f} range[{mW.min():+.3f},{mW.max():+.3f}] "
              f"| #(mu_W>1)={int((mW>1).sum())}/{len(rows)}", flush=True)


if __name__ == '__main__':
    main()
