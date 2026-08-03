import sys, numpy as np
from common import make_ssg, fixed_point, make_cut, in_X, balanced
from conditioning import rej_sample, kappa
d=int(sys.argv[1]); delta=float(sys.argv[2]); R=int(sys.argv[3]); mode=sys.argv[4]
rng=np.random.default_rng(0)
f,_=make_ssg(d,delta,0); xstar=fixed_point(f,d)
cuts=[]; ks=[]
print(f"[mode={mode} d={d}]",flush=True)
for t in range(R):
    S,acc=rej_sample(cuts,d,2000,rng)
    if len(S)<150: print(f"  r{t}: acc={acc:.1e} collapse/stop"); break
    k=kappa(S); ks.append(k)
    mu=S.mean(0)
    if mode=='balanced': c=balanced(S,d)
    elif mode=='extreme':  c=S[np.argmax(np.linalg.norm(S-mu,axis=1))]      # peripheral
    else:                  c=S[np.argmax(S@rng.normal(size=d))]            # random vertex
    rat = k/ks[-2] if len(ks)>=2 else float('nan')
    print(f"  r{t:2d} acc={acc:.1e} κ={k:7.2f} ratio={rat:6.3f}",flush=True)
    c_,s_,v=make_cut(f,c)
    if v<1e-11: break
    cuts.append((c_,s_))
if len(ks)>=2:
    rs=[ks[i+1]/ks[i] for i in range(len(ks)-1)]
    print(f"  => κ[{min(ks):.1f},{max(ks):.1f}] ratio max={max(rs):.2f} geomean={np.exp(np.mean(np.log(rs))):.3f} rounds_survived={len(ks)}")
