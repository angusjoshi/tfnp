"""C3: the block-restart exact (ray-shooting) sampler.
Exact sampling works whenever X_t is star-shaped about a FINDABLE point p:
ray-shoot from p. Two notions of 'kernel' (set of valid centers p):
  - LP-kernel  = box ∩ ⋂_r ker(K_r)  (all pairwise w-sums >=0): poly-CERTIFIABLE,
    but MONOTONE SHRINKING in t (adding a cut only adds constraints) -> once empty,
    never recovers via this certificate.
  - TRUE kernel = {p : p sees all of X_t}: NOT monotone (cutting a hard-to-see
    region can RESTORE star-shapedness), so it CAN recover. But is it findable/poly?
We measure both over the real trajectory: does the true kernel recover after the
LP-kernel empties, and how often?
"""
import os, sys
import numpy as np
from scipy.optimize import linprog
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import make_ssg, fixed_point, in_X, balanced, make_cut, hitrun

def lp_kernel(cuts, d):
    """Chebyshev center of box ∩ ⋂_r {s_i(z_i-c_i)+s_j(z_j-c_j)>=0}. Returns
    (point, margin); margin>0 => LP-kernel has nonempty interior."""
    A=[]; b=[]
    for (c,s) in cuts:
        for i in range(d):
            for j in range(i+1,d):
                row=np.zeros(d); row[i]-=s[i]; row[j]-=s[j]
                A.append(row); b.append(-(s[i]*c[i]+s[j]*c[j]))
    if not A:
        return np.full(d,0.5), 1.0
    A=np.array(A); b=np.array(b); rn=np.linalg.norm(A,axis=1,keepdims=True)
    A2=np.hstack([A,rn]); cobj=np.zeros(d+1); cobj[-1]=-1
    res=linprog(cobj,A_ub=A2,b_ub=b,bounds=[(0,1)]*d+[(0,None)],method='highs')
    if res.success: return res.x[:d], -res.fun
    return None, 0.0

def visible_frac(p, pts, cuts, nt=150):
    vis=0
    for q in pts:
        ts=np.linspace(0,1,nt)[:,None]
        seg=p[None,:]*(1-ts)+q[None,:]*ts
        if in_X(seg,cuts).all(): vis+=1
    return vis/len(pts)

def true_kernel_proxy(cuts, d, rng, samples):
    """max over candidate centers of the fraction of samples visible from it.
    ~1.0 => X_t is (approx) star-shaped about that center (true kernel nonempty)."""
    cands=[samples.mean(0)]
    idx=rng.choice(len(samples), size=min(8,len(samples)), replace=False)
    cands+=[samples[i] for i in idx]
    best=0.0; bestp=None
    for p in cands:
        v=visible_frac(p, samples, cuts)
        if v>best: best=v; bestp=p
    return best, bestp

def main():
    for (d,delta,seed) in [(6,1e-3,1),(8,1e-3,2),(10,1e-3,3)]:
        rng=np.random.default_rng(seed); f,_=make_ssg(d,delta,seed); xstar=fixed_point(f,d)
        cuts=[]; start=np.full(d,0.5)
        lp_empty_at=None; recoveries=0; lp_hist=[]; tk_hist=[]
        print(f"[SSG d={d}] round: LPkerMargin  trueKernelVisMax")
        for t in range(2*d):
            S=hitrun(cuts,d,start,nsamp=60,thin=15,burn=1000,rng=rng,nt=2000)
            _,margin=lp_kernel(cuts,d)
            tk,_=true_kernel_proxy(cuts,d,rng,S) if len(S)>=20 else (float('nan'),None)
            lp_hist.append(margin); tk_hist.append(tk)
            if margin<=1e-6 and lp_empty_at is None: lp_empty_at=t
            if lp_empty_at is not None and tk>=0.999: recoveries+=1
            flag=""
            if margin<=1e-6: flag+=" LPempty"
            if tk>=0.999: flag+=" TKfull"
            print(f"  t={t:2d}  {margin:7.4f}   {tk:.3f}{flag}")
            bp=balanced(S,d); c_,s_,vmag=make_cut(f,bp)
            if vmag<1e-11: break
            cuts.append((c_,s_)); start=bp.copy()
        print(f"  => LP-kernel emptied at round {lp_empty_at}; "
              f"true-kernel-full rounds AFTER that: {recoveries}")
    print("done")

if __name__=="__main__":
    main()
