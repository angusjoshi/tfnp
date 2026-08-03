import numpy as np, common as C
from conditioning import rej_sample
rng=np.random.default_rng(13)
def seg_in(a,b,cuts,ns=12):
    ts=np.linspace(1/(ns+1),ns/(ns+1),ns)
    return C.in_X(a[None,:]+ts[:,None]*(b-a)[None,:],cuts).all()
def convex_ok(Q,cuts,nc=16,rng=None):
    # test random convex combos of Q are in X_t
    if len(Q)<=1: return True
    P=np.array(Q); 
    for _ in range(nc):
        w=rng.random(len(P)); w/=w.sum()
        if not C.in_X((w[:,None]*P).sum(0)[None,:],cuts)[0]: return False
    return True
def cc_cover(Y,cuts,rng,tgt=0.95):
    n=len(Y); covered=np.zeros(n,bool); pieces=0
    idx=np.arange(n)
    while covered.mean()<tgt and pieces<n:
        unc=idx[~covered]
        seed=unc[0]; Q=[Y[seed]]; members=[seed]
        for q in unc[1:]:
            if seg_in(Y[seed],Y[q],cuts) and convex_ok(Q+[Y[q]],cuts,rng=rng):
                Q.append(Y[q]); members.append(q)
        covered[members]=True; pieces+=1
    return pieces, covered.mean()
def build(d,seed,T):
    f,_=C.make_ssg(d,1e-3,seed); r=np.random.default_rng(seed); cuts=[];start=np.full(d,0.5); sigs=set()
    for t in range(T):
        S,_=rej_sample(cuts,d,300,r)
        if len(S)<40: break
        bp=C.balanced(S,d);c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        sigs.add(tuple(s_.astype(int)));cuts.append((c_,s_));start=bp
    return cuts,len(sigs)
print("CC (convex-cover number) vs d — the TRUE driver (k <= CC <= k')  [SSG t=2d]",flush=True)
print(f"{'d':>2}{'sd':>3}{'sigma':>6}{'CC':>4}{'cov':>6}",flush=True)
for d in [3,4,5]:
    for seed in [0,1]:
        cuts,sig=build(d,seed,2*d)
        if len(cuts)<2: print(f"{d} {seed} collapse");continue
        Y,acc=rej_sample(cuts,d,250,np.random.default_rng(50+seed))
        if len(Y)<60: print(f"{d} {seed} undersampled");continue
        cc,cov=cc_cover(Y,cuts,rng)
        print(f"{d:>2}{seed:>3}{sig:>6}{cc:>4}{cov:>6.2f}",flush=True)
