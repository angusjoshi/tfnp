import numpy as np, common as C
from conditioning import rej_sample
from sigma_verdict import build_controlled, spread_signs
# margin_l(y) for a class = min over that class's cuts of g = max_i w_i + min_i w_i.
def class_margins(y, cuts_by_class):
    return [min((s*(y-c)).max()+(s*(y-c)).min() for (c,s) in cl) for cl in cuts_by_class]
def group_by_sign(cuts):
    d={}
    for (c,s) in cuts: d.setdefault(tuple(s.astype(int)),[]).append((c,s))
    return list(d.values())
def analyze(cuts, Y, sigma):
    cl=group_by_sign(cuts)
    rows={}
    for Delta in [0.02,0.05,0.1]:
        binding=np.array([sum(1 for m in class_margins(y,cl) if m<=Delta) for y in Y])
        n=len(Y)
        rows[Delta]=( (binding==0).mean(), (binding==1).mean(), (binding>=2).mean() )
    return rows, len(cl)
print("DoubleBind fraction (binding>=2 classes) — the ONE lemma. Predict ~Delta^2, flat in d",flush=True)
print("[A] controlled sigma, d=5,t=10 spread",flush=True)
print(f"{'sigma':>6}{'D':>6}{'deep0':>7}{'bind1':>7}{'DBIND2+':>8}",flush=True)
d,t=5,10
for sigma in [2,3,5,8]:
    r2=np.random.default_rng(600); signs=spread_signs(d,sigma,r2)
    cuts,ok=build_controlled(d,t,signs,r2)
    if not ok or len(cuts)<t: print(f"{sigma}: collapse");continue
    Y,acc=rej_sample(cuts,d,400,r2)
    if len(Y)<60: print(f"{sigma}: undersampled");continue
    rows,nc=analyze(cuts,Y,sigma)
    for Delta,(a,b,c) in rows.items():
        print(f"{sigma:>6}{Delta:>6.2f}{a:>7.2f}{b:>7.2f}{c:>8.3f}",flush=True)
print("[B] real SSG, d-scaling (Delta=0.05, DoubleBind flat in d?)",flush=True)
print(f"{'d':>2}{'sd':>3}{'sigma':>6}{'DBIND2+':>8}",flush=True)
for d in [3,4,5,6]:
    for seed in [0,1]:
        f,_=C.make_ssg(d,1e-3,seed); r=np.random.default_rng(seed); cuts=[];start=np.full(d,0.5)
        for tt in range(2*d):
            S,_=rej_sample(cuts,d,300,r)
            if len(S)<40: break
            bp=C.balanced(S,d);c_,s_,vm=C.make_cut(f,bp)
            if vm<1e-11: break
            cuts.append((c_,s_));start=bp
        if len(cuts)<2: print(f"{d} {seed} collapse");continue
        Y,_=rej_sample(cuts,d,300,np.random.default_rng(70+seed))
        if len(Y)<60: print(f"{d} {seed} undersampled");continue
        cl=group_by_sign(cuts)
        db=np.mean([sum(1 for m in class_margins(y,cl) if m<=0.05)>=2 for y in Y])
        print(f"{d:>2}{seed:>3}{len(cl):>6}{db:>8.3f}",flush=True)
