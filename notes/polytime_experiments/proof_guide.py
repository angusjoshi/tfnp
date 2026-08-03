import numpy as np, common as C
from conditioning import rej_sample
from sigma_verdict import build_controlled, spread_signs
def vis(z,Y,cuts,nseg=40):
    ts=np.linspace(1/(nseg+1),nseg/(nseg+1),nseg); ok=np.ones(len(Y),bool)
    for k,y in enumerate(Y): ok[k]=C.in_X(z[None,:]+ts[:,None]*(y-z)[None,:],cuts).all()
    return ok
def greedy_guards(Y,cand,cuts,tgt=0.99):
    cov=np.zeros(len(Y),bool);V=[vis(c,Y,cuts) for c in cand];chosen=[]
    while cov.mean()<tgt and len(chosen)<len(cand):
        g=[(v&~cov).sum() for v in V];b=int(np.argmax(g))
        if g[b]==0:break
        cov|=V[b];chosen.append(cand[b])
    return chosen
def corners(signs): return [np.where(s>0,1.0,0.0) for s in signs]  # ĉ_ℓ
# ---- 1 & 3: guards + nonempty F-cells vs sigma (d=5,t=10) ----
print("[1] guards vs sigma (d=5,t=10 spread): k, guard-interiorness, nearest-corner align",flush=True)
d,t=5,10
for sigma in [2,3,5,8]:
    r2=np.random.default_rng(400)
    signs=spread_signs(d,sigma,r2); cor=corners(signs)
    cuts,ok=build_controlled(d,t,signs,r2)
    if not ok or len(cuts)<t: print(f"  sigma={sigma}: collapse"); continue
    Y,acc=rej_sample(cuts,d,400,r2)
    if len(Y)<60: print(f"  sigma={sigma}: undersampled"); continue
    cand=np.vstack([np.array([c for c,_ in cuts]), rej_sample(cuts,d,40,r2)[0]])
    G=greedy_guards(Y,cand,cuts)
    interior=np.mean([ (g.min()>0.02 and g.max()<0.98) for g in G])
    # nearest corner alignment: for each guard, max cosine to a corner-direction (ĉ-center)
    ctr=np.full(d,0.5); aligns=[max(np.dot((g-ctr)/(np.linalg.norm(g-ctr)+1e-9),(c-ctr)/(np.linalg.norm(c-ctr)+1e-9)) for c in cor) for g in G]
    # [3] nonempty F-cell count = distinct (argmax_r,argmin_r) over sample
    labs=set(tuple((int(np.argmax(s*(y-c))),int(np.argmin(s*(y-c)))) for (c,s) in cuts) for y in Y)
    print(f"  sigma={sigma}: k={len(G)} interiorFrac={interior:.2f} meanCornerAlign={np.mean(aligns):.2f} nonemptyFcells={len(labs)} (worst d^2sigma={d**(2*sigma):.0e})",flush=True)
# ---- 2: min-tie multiplicity vs d (fixed sigma=3) ----
print("[2] min-tie multiplicity (coords within eps of class-min) vs d, sigma=3",flush=True)
for d in [3,4,5,6]:
    r2=np.random.default_rng(500+d); signs=spread_signs(d,3,r2)
    cuts,ok=build_controlled(d,2*d,signs,r2)
    if not ok or len(cuts)<2*d: print(f"  d={d}: collapse"); continue
    Y,_=rej_sample(cuts,d,300,r2)
    if len(Y)<60: print(f"  d={d}: undersampled"); continue
    mults=[]
    for y in Y:
        for (c,s) in cuts:
            w=s*(y-c); mn=w.min(); mults.append(int(np.sum(w<=mn+0.02)))
    mults=np.array(mults)
    print(f"  d={d}: min-tie mult mean={mults.mean():.2f} p90={np.percentile(mults,90):.0f} max={mults.max()}",flush=True)
