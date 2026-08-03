import numpy as np, common as C
from conditioning import rej_sample
from cellcount import build_ssg, cellcount
# Does k'_lb grow with nsamp (=> near-singleton cells => k' huge/exp) or plateau (=> k' ~ that)?
for d in [4,5]:
    cuts,sig=build_ssg(d,0,2*d)
    print(f"d={d} sigma={sig}:",flush=True)
    for nsamp in [200,500,1000,2000]:
        Y,acc=rej_sample(cuts,d,nsamp,np.random.default_rng(11))
        if len(Y)<nsamp*0.5: print(f"  nsamp={nsamp}: only got {len(Y)} (acc {acc:.1e})"); continue
        kp=cellcount(cuts,Y)
        print(f"  nsamp={len(Y):>4}  k'_lb={kp:>4}  ratio={kp/len(Y):.2f}",flush=True)
