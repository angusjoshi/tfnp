import numpy as np, common as C
from conditioning import rej_sample
from sigma_verdict import build_controlled, spread_signs
from doublebind import group_by_sign
# sub-lemma 1: points DEEP in class l' (margin>Δ) lie in ker(K_l') = {w_i+w_j>=0 all pairs}.
def in_ker(y, cl_cuts):  # in kernel of every cut of this class
    for (c,s) in cl_cuts:
        w=np.sort(s*(y-c))
        if w[0]+w[1] < -1e-9: return False
    return True
def margin(y, cl_cuts):
    return min((s*(y-c)).max()+(s*(y-c)).min() for (c,s) in cl_cuts)
print("sub-lemma 1: deep-in-class(margin>Δ·med) => in that class's convex kernel?  (predict ->1)",flush=True)
print(f"{'d':>2}{'sigma':>6}{'Dfrac':>6}{'deepKerFrac':>12}{'nDeep':>7}",flush=True)
for (d,sigma) in [(5,3),(5,5),(5,8),(4,3),(6,4)]:
    r2=np.random.default_rng(600); signs=spread_signs(d,sigma,r2)
    cuts,ok=build_controlled(d,min(2*d,10),signs,r2)
    if not ok: print(f"d={d} s={sigma} collapse");continue
    Y,_=rej_sample(cuts,d,400,r2)
    if len(Y)<60: print(f"d={d} s={sigma} undersampled");continue
    cl=group_by_sign(cuts)
    allm=[margin(y,c) for y in Y for c in cl]; med=np.median(allm)
    for frac in [0.5,1.0,2.0]:
        Delta=frac*med; ok_cnt=0; deep_cnt=0
        for y in Y:
            for c in cl:
                if margin(y,c)>Delta:
                    deep_cnt+=1
                    if in_ker(y,c): ok_cnt+=1
        fr=ok_cnt/deep_cnt if deep_cnt else float('nan')
        print(f"{d:>2}{sigma:>6}{frac:>6.1f}{fr:>12.3f}{deep_cnt:>7}",flush=True)
