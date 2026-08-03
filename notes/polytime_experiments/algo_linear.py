import numpy as np, sys, time
from scipy.optimize import linprog
rng=np.random.default_rng(11)
def make_f(d,lam,rng):
    M=rng.normal(size=(d,d)); M/=(np.abs(M).sum(1,keepdims=True)+1e-9); b=rng.uniform(0,1,d)
    return lambda x: np.clip(lam*(M@x)+b,0,1)
def fp(f,d):
    x=np.full(d,0.5)
    for _ in range(120000):
        y=f(x)
        if np.max(np.abs(y-x))<1e-13: return y
        x=y
    return x
def cut(f,c):
    v=f(c)-c; s=np.sign(v); s[s==0]=1; return c.copy(),s
def chord_ts(p,u,cuts,nt=500):
    ts=np.linspace(-2.5,2.5,nt); P=p[None,:]+ts[:,None]*u[None,:]
    ok=(P.min(1)>=-1e-9)&(P.max(1)<=1+1e-9)
    for c,s in cuts:
        W=s[None,:]*(P-c[None,:]); ok&=(W.max(1)+W.min(1)>=-1e-9)
    return ts[ok]
def hitrun(cuts,d,start,nsamp=50,thin=6,burn=120):
    p=start.copy(); out=[]; k=0; cap=burn+thin*nsamp*4
    while len(out)<nsamp and k<cap:
        u=rng.normal(size=d); u/=np.linalg.norm(u)
        fts=chord_ts(p,u,cuts)
        if len(fts)>0: p=p+rng.choice(fts)*u
        k+=1
        if k>=burn and k%thin==0: out.append(p.copy())
    return np.array(out) if out else start[None,:]
def balanced(S,d):
    N=len(S); cobj=np.concatenate([np.zeros(d),np.ones(N)]); A=[];b=[]
    for j,y in enumerate(S):
        for i in range(d):
            r=np.zeros(d+N);r[i]=1;r[d+j]=-1;A.append(r);b.append(y[i])
            r=np.zeros(d+N);r[i]=-1;r[d+j]=-1;A.append(r);b.append(-y[i])
    res=linprog(cobj,A_ub=np.array(A),b_ub=np.array(b),bounds=[(0,1)]*d+[(0,None)]*N,method='highs')
    return res.x[:d] if res.success else S.mean(0)

d=int(sys.argv[1]); R=int(sys.argv[2])
f=make_f(d,float(sys.argv[3]),rng); xstar=fp(f,d)
cuts=[]; start=np.full(d,0.5); t0=time.time()
print(f"d={d} x*={np.round(xstar,3)}",flush=True)
for t in range(R):
    S=hitrun(cuts,d,start,nsamp=50)
    bp=balanced(S,d); err=np.max(np.abs(bp-xstar)); spread=(np.max(S,0)-np.min(S,0)).max()
    print(f"  r{t:3d} ||bp-x*||={err:.2e} spread={spread:.2e} nS={len(S)} t={time.time()-t0:.0f}s",flush=True)
    cuts.append(cut(f,bp)); start=bp.copy()
