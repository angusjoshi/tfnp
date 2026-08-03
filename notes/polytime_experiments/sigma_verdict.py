import numpy as np, common as C
from conditioning import rej_sample
rng=np.random.default_rng(7)
def build_controlled(d,t,signs,rng):
    cuts=[]
    for r in range(t):
        s=signs[r%len(signs)].astype(float)
        S,_=rej_sample(cuts,d,300,rng)
        if len(S)<40: return cuts,False
        c=C.balanced(S,d); cuts.append((c,s))
    return cuts,True
def vis(z,Y,cuts,nseg=60):
    ts=np.linspace(1/(nseg+1),nseg/(nseg+1),nseg)
    ok=np.ones(len(Y),bool)
    for k,y in enumerate(Y):
        ok[k]=C.in_X(z[None,:]+ts[:,None]*(y-z)[None,:],cuts).all()
    return ok
def kcover(Y,cand,cuts,tgt=0.99):
    cov=np.zeros(len(Y),bool);k=0;V=[vis(c,Y,cuts) for c in cand]
    while cov.mean()<tgt and k<len(cand):
        g=[(v&~cov).sum() for v in V];b=int(np.argmax(g))
        if g[b]==0:break
        cov|=V[b];k+=1
    return k
def spread_signs(d,sigma,rng):
    # greedily maximize pairwise Hamming distance
    S=[rng.choice([-1,1],d)]
    while len(S)<sigma:
        best=None;bd=-1
        for _ in range(200):
            c=rng.choice([-1,1],d);md=min(np.sum(c!=x) for x in S)
            if md>bd:bd=md;best=c
        S.append(best)
    return np.array(S)
if __name__=="__main__":
    import numpy as np
    print("k, h_iso, kappa vs sigma at FIXED d=5,t=10 (poly-vs-exp verdict). mode=spread",flush=True)
    print(f"{'sigma':>6}{'sd':>3}{'acc':>8}{'k':>4}{'h_iso':>7}{'kappa':>7}",flush=True)
    d,t=5,10
    for sigma in [1,2,3,5,8]:
        for seed in [0,1]:
            r2=np.random.default_rng(100+seed)
            signs=spread_signs(d,sigma,r2)
            cuts,ok=build_controlled(d,t,signs,r2)
            if not ok or len(cuts)<t:
                print(f"{sigma:>6}{seed:>3}   vol-collapse (cuts={len(cuts)})",flush=True);continue
            Y,acc=rej_sample(cuts,d,400,r2)
            if len(Y)<60: print(f"{sigma:>6}{seed:>3}{acc:>8.1e} undersampled",flush=True);continue
            cand=np.vstack([np.array([c for c,_ in cuts]), rej_sample(cuts,d,30,r2)[0]])
            k=kcover(Y,cand,cuts)
            hi,_,_=C.marginal_cheeger(Y,C.candidate_directions(Y),isotropic=True)
            Cov=np.cov(Y.T)+1e-12*np.eye(d);ev=np.linalg.eigvalsh(Cov);kap=ev.max()/max(ev.min(),1e-15)
            print(f"{sigma:>6}{seed:>3}{acc:>8.1e}{k:>4}{hi:>7.3f}{kap:>7.1f}",flush=True)
    