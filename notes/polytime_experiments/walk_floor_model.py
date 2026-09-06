"""Monte-Carlo check of the cycle-41 no-go: a fair-coin near-flat walk
(steps mu_t = (1 - 1/(4n))^t ~ flat over n rounds, generic level ell = 0.37*mu)
has Theta(sqrt(n)) expected strict crossings + step-band residence."""
import numpy as np
rng = np.random.default_rng(41)
for n in (16, 64, 256, 1024):
    q = 1.0 - 1.0/(4*n)          # geometric envelope, flat window ~ 4n >> n
    mu = q ** np.arange(n)
    R = 4000
    eps = rng.choice([-1.0, 1.0], size=(R, n))
    steps = eps * mu
    pos = np.cumsum(steps, axis=1)
    v = np.hstack([np.zeros((R, 1)), pos])   # v_0..v_n
    ell = 0.37 * mu[0]                        # generic level in range
    w = v - ell
    cross = np.mean(np.sum(w[:, :-1] * w[:, 1:] < 0, axis=1))
    band = np.mean(np.sum((np.abs(w[:, :-1]) > 0) & (np.abs(w[:, :-1]) < mu), axis=1))
    print(f"n={n:5d}  E[cross]={cross:6.2f}  E[band]={band:6.2f}  "
          f"2*cross/band={2*cross/band:.3f}  cross/sqrt(n)={cross/np.sqrt(n):.3f}",
          flush=True)
