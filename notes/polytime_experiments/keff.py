import numpy as np, common as C
from conditioning import rej_sample
from cellcount import build_ssg
def assign(y,cuts):  # convex-cell's assignment vector: argmax_i |w_i^r| per cut
    return tuple(int(np.argmax(np.abs(s*(y-c)))) for (c,s) in cuts)
def k_eff(cuts, Y, cover=0.99):
    from collections import Counter
    cnt=Counter(assign(y,cuts) for y in Y)
    freqs=sorted(cnt.values(),reverse=True); tot=sum(freqs); c=0
    for i,f in enumerate(freqs):
        c+=f
        if c>=cover*tot: return i+1
    return len(freqs)
print("k_eff SATURATION: #cells for 99% of MASS vs N (saturate=poly) vs k'_lb (tail grows)",flush=True)
for d in [4,5,6]:
    cuts,sig=build_ssg(d,0,2*d)
    if len(cuts)<2: print(f"d={d} collapse");continue
    print(f"d={d} sigma={sig}:",flush=True)
    for N in [200,500,1000,2000]:
        Y,acc=rej_sample(cuts,d,N,np.random.default_rng(31))
        if len(Y)<N*0.5: print(f"  N={N}: only {len(Y)} (acc {acc:.1e})");continue
        ke=k_eff(cuts,Y); kp=len(set(assign(y,cuts) for y in Y))
        print(f"  N={len(Y):>4}  k_eff(99%mass)={ke:>4}  k'_lb(allcells)={kp:>4}  ratio={ke/kp:.2f}",flush=True)
