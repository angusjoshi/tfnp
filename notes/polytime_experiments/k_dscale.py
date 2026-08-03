import numpy as np, common as C
from conditioning import rej_sample
from sigma_verdict import build_controlled, kcover, spread_signs
print("k vs d at FIXED small sigma (gap A: is k poly in d?)  t=2d, spread signs",flush=True)
print(f"{'sigma':>6}{'d':>3}{'t':>4}{'sd':>3}{'acc':>8}{'k':>4}{'kappa':>7}",flush=True)
for sigma in [2,3]:
    for d in [3,4,5,6]:
        t=2*d
        for seed in [0,1]:
            r2=np.random.default_rng(200+seed*7+d)
            signs=spread_signs(d,min(sigma,2**d),r2)
            cuts,ok=build_controlled(d,t,signs,r2)
            if not ok or len(cuts)<t:
                print(f"{sigma:>6}{d:>3}{t:>4}{seed:>3}   vol-collapse(cuts={len(cuts)})",flush=True);continue
            Y,acc=rej_sample(cuts,d,400,r2)
            if len(Y)<60:
                print(f"{sigma:>6}{d:>3}{t:>4}{seed:>3}{acc:>8.1e} undersampled",flush=True);continue
            cand=np.vstack([np.array([c for c,_ in cuts]), rej_sample(cuts,d,30,r2)[0]])
            k=kcover(Y,cand,cuts)
            Cov=np.cov(Y.T)+1e-12*np.eye(d);ev=np.linalg.eigvalsh(Cov);kap=ev.max()/max(ev.min(),1e-15)
            print(f"{sigma:>6}{d:>3}{t:>4}{seed:>3}{acc:>8.1e}{k:>4}{kap:>7.1f}",flush=True)
