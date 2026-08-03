"""Verify Theorem A: if w_i(x*)=s_i(x*_i-c_i) >= 0 for all i (cuts point toward
x*), then x* sees all of K(c,s) (segment [x*,y] in K for every y in K), i.e.
X_t is star-shaped about x*. Also verify it can FAIL when some w_i(x*)<0."""
import numpy as np
rng = np.random.default_rng(0)

def inK(Y, c, s):   # membership max+min>=0 in w-coords, full support
    W = s * (Y - c)
    return W.max(axis=-1) + W.min(axis=-1) >= -1e-12

def test(d, toward, trials=4000):
    fails = 0; tested = 0
    for _ in range(trials):
        c = rng.uniform(-1, 1, d)
        xs = rng.uniform(-1, 1, d)
        if toward:
            s = np.sign(xs - c); s[s == 0] = 1
        else:
            s = rng.choice([-1., 1.], d)          # arbitrary -> may point away
        if not inK(xs[None], c, s)[0]:            # need x* in K
            continue
        # sample y in K, check segment
        for _ in range(6):
            y = rng.uniform(-1.5, 1.5, d)
            if not inK(y[None], c, s)[0]:
                continue
            tested += 1
            lam = rng.uniform(0, 1, 40)
            Q = (1 - lam)[:, None] * xs[None] + lam[:, None] * y[None]
            if not inK(Q, c, s).all():
                fails += 1
    return tested, fails

for d in [3, 5, 8, 12]:
    t1, f1 = test(d, toward=True)
    t2, f2 = test(d, toward=False)
    print(f"d={d}: TOWARD (w(x*)>=0): tested={t1} segment-failures={f1}   "
          f"ARBITRARY sign: tested={t2} segment-failures={f2}")
print("Theorem A holds iff TOWARD failures == 0 for all d.")
