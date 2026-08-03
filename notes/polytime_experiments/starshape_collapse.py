import numpy as np
from scipy.optimize import linprog
rng = np.random.default_rng(0)

def make_contraction(d, lam, rng):
    M = rng.normal(size=(d,d)); M/=(np.abs(M).sum(1,keepdims=True)+1e-9)
    b = rng.uniform(0,1,size=d)
    return lambda x: np.clip(lam*(M@x)+b,0,1)
def fixed_point(f,d,it=100000):
    x=np.full(d,0.5)
    for _ in range(it):
        y=f(x)
        if np.max(np.abs(y-x))<1e-13: return y
        x=y
    return x
def cut(f,c):
    v=f(c)-c; s=np.sign(v); s[s==0]=1.0; return c.copy(),s
def inX(y,cuts):
    if y.min()<-1e-12 or y.max()>1+1e-12: return False
    for (c,s) in cuts:
        w=s*(y-c)
        if w.max()+w.min()<-1e-12: return False
    return True

def kernel_cheby(cuts,d):
    A=[]; bub=[]
    for (c,s) in cuts:
        for i in range(d):
            for j in range(i+1,d):
                row=np.zeros(d); row[i]-=s[i]; row[j]-=s[j]
                A.append(row); bub.append(-(s[i]*c[i]+s[j]*c[j]))
    if not A: return np.full(d,0.5), 1.0
    A=np.array(A); bub=np.array(bub); rn=np.linalg.norm(A,axis=1,keepdims=True)
    A2=np.hstack([A,rn]); cobj=np.zeros(d+1); cobj[-1]=-1
    res=linprog(cobj,A_ub=A2,b_ub=bub,bounds=[(0,1)]*d+[(0,None)],method='highs')
    if res.success: return res.x[:d], -res.fun
    return None,0.0

def kernel_constraints(cuts,d):
    A=[]; b=[]
    for (c,s) in cuts:
        for i in range(d):
            for j in range(i+1,d):
                row=np.zeros(d); row[i]-=s[i]; row[j]-=s[j]
                A.append(row); b.append(-(s[i]*c[i]+s[j]*c[j]))
    return (np.array(A),np.array(b)) if A else (None,None)

def rayshoot(p0,u,cuts,Rmax):        # star-shaped: last r with p0+r u in X
    lo,hi=0.0,Rmax
    if not inX(p0+lo*u,cuts): return 0.0
    if inX(p0+hi*u,cuts): return hi
    for _ in range(40):
        mid=(lo+hi)/2
        if inX(p0+mid*u,cuts): lo=mid
        else: hi=mid
    return lo

def sample_star(p0,cuts,d,N=250):
    U=rng.normal(size=(N,d)); U/=np.linalg.norm(U,axis=1,keepdims=True)
    R=np.array([rayshoot(p0,U[k],cuts,d*1.8) for k in range(N)])
    w=R**d                                   # importance weight for uniform
    r=R*rng.uniform(0,1,size=N)**(1.0/d)
    P=p0[None,:]+r[:,None]*U
    return P,w,R

def balanced_kernel(samples,w,cuts,d):
    N=len(samples); wn=w/ (w.mean()+1e-12)
    cobj=np.concatenate([np.zeros(d), wn])
    A=[]; b=[]
    for j,y in enumerate(samples):
        for i in range(d):
            r=np.zeros(d+N); r[i]=1;  r[d+j]=-1; A.append(r); b.append(y[i])
            r=np.zeros(d+N); r[i]=-1; r[d+j]=-1; A.append(r); b.append(-y[i])
    Ak,bk=kernel_constraints(cuts,d)
    if Ak is not None:
        Ak2=np.hstack([Ak, np.zeros((len(Ak),N))]); A=np.vstack([A,Ak2]); b=np.concatenate([b,bk])
    res=linprog(cobj,A_ub=np.array(A),b_ub=np.array(b),bounds=[(0,1)]*d+[(0,None)]*N,method='highs')
    return res.x[:d] if res.success else None

for d in [3,4,5,6]:
  print(f"\n##### d={d} #####")
  for trial in range(2):
    f=make_contraction(d,0.9995,rng); xstar=fixed_point(f,d)
    cuts=[]; volprev=None
    print(f"-- trial {trial}  x*={np.round(xstar,2)}")
    for t in range(40):
        p0,margin=kernel_cheby(cuts,d)
        if p0 is None: print(f"  r{t}: KERNEL EMPTY (should not happen w/ constrained queries!)"); break
        P,w,R=sample_star(p0,cuts,d,N=200)
        vol=w.mean()                     # ∝ E[R^d] ∝ vol(X_t)
        ratio = vol/volprev if volprev else float('nan'); volprev=vol
        bp=balanced_kernel(P,w,cuts,d)
        if bp is None: print(f"  r{t}: balanced LP infeasible"); break
        xin=inX(xstar,cuts)
        if t%4==0 or t>=36:
            print(f"  r{t:2d} vol~{vol:.3e} shrink={ratio:.3f} kerMargin={margin:.3f} x*inX={xin}")
        cuts.append(cut(f,bp))
    # summary: geometric shrink over the run
