import numpy as np, sys, time
from scipy.optimize import linprog
rng=np.random.default_rng(int(sys.argv[4]) if len(sys.argv)>4 else 2)
d=int(sys.argv[1]); R=int(sys.argv[2]); delta=float(sys.argv[3])
types=rng.integers(0,3,size=d); nbrs=[rng.choice(d,size=rng.integers(2,min(5,d)+1),replace=False) for _ in range(d)]
r=rng.uniform(0,1,size=d)
def G(x):
    out=np.empty(d)
    for i in range(d):
        xs=x[nbrs[i]]; out[i]=xs.max() if types[i]==0 else xs.min() if types[i]==1 else xs.mean()
    return out
def f(x): return np.clip((1-delta)*G(x)+delta*r,0,1)
def fp():
    x=np.full(d,0.5)
    for _ in range(3000000):
        y=f(x)
        if np.max(np.abs(y-x))<1e-13: return y
        x=y
    return x
xstar=fp()
TOL=1e-9
def cut(c):
    v=f(c)-c; s=np.sign(v); s[np.abs(v)<=TOL]=0   # TERNARY: inactive coords excluded
    return c.copy(),s,np.max(np.abs(v))
def K_ok(P,c,s):        # P:(n,d). y in K iff max_{active} s_i(y_i-c_i) >= ||y-c||inf
    act=s!=0
    if not act.any(): return np.ones(len(P),bool)   # vacuous cut (shouldn't happen away from x*)
    D=P-c[None,:]; W=s[None,:]*D
    lhs=np.where(act[None,:],W,-np.inf).max(1); rhs=np.abs(D).max(1)
    return lhs>=rhs-1e-9
def chord_ts(p,u,cuts,nt=500):
    ts=np.linspace(-2.5,2.5,nt);P=p[None,:]+ts[:,None]*u[None,:]
    ok=(P.min(1)>=-1e-9)&(P.max(1)<=1+1e-9)
    for c,s in cuts: ok&=K_ok(P,c,s)
    return ts[ok]
def hitrun(cuts,start,nsamp=60,thin=20,burn=600):
    p=start.copy();out=[];k=0;cap=burn+thin*nsamp*5
    while len(out)<nsamp and k<cap:
        u=rng.normal(size=d);u/=np.linalg.norm(u)
        fts=chord_ts(p,u,cuts)
        if len(fts)>0:p=p+rng.choice(fts)*u
        k+=1
        if k>=burn and k%thin==0: out.append(p.copy())
    return np.array(out) if out else start[None,:]
def balanced(S):
    N=len(S);cobj=np.concatenate([np.zeros(d),np.ones(N)]);A=[];b=[]
    for j,y in enumerate(S):
        for i in range(d):
            row=np.zeros(d+N);row[i]=1;row[d+j]=-1;A.append(row);b.append(y[i])
            row=np.zeros(d+N);row[i]=-1;row[d+j]=-1;A.append(row);b.append(-y[i])
    res=linprog(cobj,A_ub=np.array(A),b_ub=np.array(b),bounds=[(0,1)]*d+[(0,None)]*N,method='highs')
    return res.x[:d] if res.success else S.mean(0)
print(f"d={d} delta={delta} (VI~{int(1/delta)} iters) x*={np.round(xstar,3)} types={types}",flush=True)
cuts=[];start=np.full(d,0.5);t0=time.time()
for t in range(R):
    S=hitrun(cuts,start); bp=balanced(S)
    err=np.max(np.abs(bp-xstar)); spread=(np.max(S,0)-np.min(S,0)).max()
    c_,s_,vmag=cut(bp)
    if t%3==0 or t>=R-3:
        print(f"  r{t:3d} ||bp-x*||={err:.2e} spread={spread:.2e} ||f(bp)-bp||={vmag:.2e} #active={int((s_!=0).sum())} t={time.time()-t0:.0f}s",flush=True)
    if vmag<1e-11: print("  stop: bp is fixed point"); break
    cuts.append((c_,s_)); start=bp.copy()
