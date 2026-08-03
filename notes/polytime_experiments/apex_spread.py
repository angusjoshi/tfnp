import numpy as np, common as C
from conditioning import rej_sample
from sigma_verdict import kcover, spread_signs
def build_spread(d,t,signs,s_scale,rng):
    cuts=[]; ctr=np.full(d,0.5)
    for r in range(t):
        s=signs[r%len(signs)].astype(float)
        S,_=rej_sample(cuts,d,300,rng)
        if len(S)<40: return cuts,False
        bp=C.balanced(S,d); apex=ctr+s_scale*(bp-ctr)
        cuts.append((apex,s))
    return cuts,True
def apex_spread(cuts):
    A=np.array([c for c,_ in cuts])
    if len(A)<2: return 0.0
    return float(max(np.linalg.norm(A[i]-A[j]) for i in range(len(A)) for j in range(i+1,len(A))))
print("PART 2: k vs apex-spread s (fixed d=5, sigma=3, t=10). s=0 => common apex => predict k=1",flush=True)
print(f"{'s':>5}{'sd':>3}{'acc':>8}{'apexspread':>11}{'k':>4}{'kappa':>7}",flush=True)
d,sigma,t=5,3,10
for s_scale in [0.0,0.25,0.5,1.0]:
    for seed in [0,1]:
        r2=np.random.default_rng(300+seed)
        signs=spread_signs(d,sigma,r2)
        cuts,ok=build_spread(d,t,signs,s_scale,r2)
        if not ok or len(cuts)<t:
            print(f"{s_scale:>5.2f}{seed:>3}   vol-collapse(cuts={len(cuts)})",flush=True);continue
        Y,acc=rej_sample(cuts,d,400,r2)
        if len(Y)<60: print(f"{s_scale:>5.2f}{seed:>3}{acc:>8.1e} undersampled asp={apex_spread(cuts):.2f}",flush=True);continue
        cand=np.vstack([np.array([c for c,_ in cuts]), rej_sample(cuts,d,30,r2)[0]])
        k=kcover(Y,cand,cuts)
        Cov=np.cov(Y.T)+1e-12*np.eye(d);ev=np.linalg.eigvalsh(Cov);kap=ev.max()/max(ev.min(),1e-15)
        print(f"{s_scale:>5.2f}{seed:>3}{acc:>8.1e}{apex_spread(cuts):>11.2f}{k:>4}{kap:>7.1f}",flush=True)
