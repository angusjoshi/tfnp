"""C2: per-cut growth of the covariance condition number κ(X_t).

Exact rejection sampling (ground-truth covariance, no Markov chain), realizable
cuts from SSG / topical contractions. Measures κ_t over rounds and the per-cut
ratio κ_{t+1}/κ_t — the quantity that decides whether κ stays poly (bounded
ratio) or blows up (ratio > const consistently).

Usage: python conditioning.py <d> <delta> <R> [seed] [kind]  (kind: ssg|topical)
"""
import sys, numpy as np
from common import make_ssg, make_topical, fixed_point, make_cut, in_X, balanced

def rej_sample(cuts, d, want, rng, cap=40_000_000, batch=200_000):
    out = []; tries = 0
    while len(out) < want and tries < cap:
        P = rng.uniform(0, 1, size=(batch, d)); tries += batch
        keep = P[in_X(P, cuts)]
        out.extend(keep)
    acc = len(out) / max(tries, 1)
    return (np.array(out[:want]) if out else np.zeros((0, d))), acc

def kappa(S):
    if len(S) < 5: return float('nan')
    C = np.cov(S.T) + 1e-12 * np.eye(S.shape[1])
    w = np.linalg.eigvalsh(C)
    w = np.clip(w, 1e-15, None)
    return float(w.max() / w.min())

def run(d, delta, R, seed, kind):
    rng = np.random.default_rng(seed)
    f, _ = (make_ssg if kind == 'ssg' else make_topical)(d, delta, seed)
    xstar = fixed_point(f, d)
    cuts = []; kappas = []; ratios = []
    print(f"[{kind} d={d} δ={delta} seed={seed}] x*={np.round(xstar,3)}", flush=True)
    for t in range(R):
        want = 3000 if t <= 8 else 1500
        S, acc = rej_sample(cuts, d, want, rng)
        if len(S) < 200:
            print(f"  r{t:2d}: acc={acc:.1e} too low; stop", flush=True); break
        k = kappa(S); kappas.append(k)
        rat = (k / kappas[-2]) if len(kappas) >= 2 else float('nan')
        if not np.isnan(rat): ratios.append(rat)
        bp = balanced(S, d)
        c_, s_, vmag = make_cut(f, bp)
        print(f"  r{t:2d} acc={acc:.1e} n={len(S)} κ={k:8.2f} ratio={rat:6.3f} "
              f"||f(bp)-bp||={vmag:.2e} nact={int((s_!=0).sum())}", flush=True)
        if vmag < 1e-11: break
        cuts.append((c_, s_))
    if ratios:
        print(f"  => κ range [{min(kappas):.1f}, {max(kappas):.1f}], "
              f"per-cut ratio: max={max(ratios):.3f} mean={np.mean(ratios):.3f} "
              f"geomean={np.exp(np.mean(np.log(ratios))):.3f}", flush=True)
    return kappas, ratios

if __name__ == '__main__':
    d = int(sys.argv[1]); delta = float(sys.argv[2]); R = int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    kind = sys.argv[5] if len(sys.argv) > 5 else 'ssg'
    run(d, delta, R, seed, kind)
