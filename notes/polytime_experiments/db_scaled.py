import numpy as np, common as C
from conditioning import rej_sample
from sigma_verdict import build_controlled, spread_signs
from doublebind import group_by_sign, class_margins
d,t=5,10
for sigma in [3,5,8]:
    r2=np.random.default_rng(600); signs=spread_signs(d,sigma,r2)
    cuts,ok=build_controlled(d,t,signs,r2)
    if not ok or len(cuts)<t: print(f"sigma={sigma} collapse");continue
    Y,_=rej_sample(cuts,d,400,r2)
    if len(Y)<60: print(f"sigma={sigma} undersampled");continue
    cl=group_by_sign(cuts)
    M=np.array([class_margins(y,cl) for y in Y])  # (n, sigma)
    med=np.median(M); mx=M.max()
    print(f"sigma={sigma}: margin median={med:.3f} mean={M.mean():.3f} p10={np.percentile(M,10):.3f} max={mx:.3f}",flush=True)
    # DoubleBind with Delta as FRACTION of median margin
    for frac in [0.1,0.25,0.5]:
        Delta=frac*med
        binding=(M<=Delta).sum(1)
        print(f"   Delta={frac}*med={Delta:.4f}: deep0={np.mean(binding==0):.2f} bind1={np.mean(binding==1):.2f} DBIND>=2={np.mean(binding>=2):.3f}",flush=True)
