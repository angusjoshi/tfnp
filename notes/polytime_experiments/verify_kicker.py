import numpy as np, common as C
from scipy.optimize import linprog
from conditioning import rej_sample
# KICKER: on a PURE MDP (all MAX), x* = convex LP over R, yet the CLY pyramid cut
# manufactures non-convexity (|support|>=3) — the abstraction is operator-blind.
def make_mdp(d, delta, seed, kind=0):  # kind 0=all MAX, 1=all MIN
    rng=np.random.default_rng(seed); gamma=1-delta
    rew=rng.uniform(0,1,d); succ=[]
    for i in range(d):
        k=int(rng.integers(2,min(5,d+2)+1)); cand=list(range(d))+[-1,-2]
        succ.append(rng.choice(cand,size=k,replace=False))
    def val(x,j): return x[j] if j>=0 else (0.0 if j==-1 else 1.0)
    def f(x):
        out=np.empty(d)
        for i in range(d):
            vs=np.array([val(x,j) for j in succ[i]])
            op=vs.max() if kind==0 else vs.min()
            out[i]=min(1,max(0,(1-gamma)*rew[i]+gamma*op))
        return out
    return f,rew,succ,gamma
def mdp_lp(rew,succ,gamma,d,kind=0):
    # one-sided value = LP over convex R. MAX-MDP: min sum x  s.t. x_i >= (1-g)r_i+g*val(succ) for each successor.
    A=[];b=[]
    for i in range(d):
        for j in succ[i]:
            row=np.zeros(d); row[i]=-1
            const=(1-gamma)*rew[i]
            if j>=0: row[j]+=gamma
            else: const+=gamma*(0.0 if j==-1 else 1.0)
            # x_i >= const + g x_j  =>  -x_i + g x_j <= -const
            A.append(row); b.append(-const)
    c=np.ones(d) if kind==0 else -np.ones(d)  # MAX: minimize sum (least fixed pt); MIN: maximize
    res=linprog(c,A_ub=np.array(A),b_ub=np.array(b),bounds=[(0,1)]*d,method='highs')
    return res.x
for kind,name in [(0,"MAX-MDP"),(1,"MIN-MDP")]:
    print(f"=== {name} (one-sided, should be convex/poly) ===",flush=True)
    for d in [5,8]:
        for seed in [0,1]:
            f,rew,succ,gamma=make_mdp(d,1e-3,seed,kind)
            xstar=C.fixed_point(f,d); xlp=mdp_lp(rew,succ,gamma,d,kind)
            lp_err=np.max(np.abs(xstar-xlp))
            # CLY cut at a balanced point of X_1
            r=np.random.default_rng(seed+7); cuts=[]
            S,_=rej_sample(cuts,d,200,r); bp=C.balanced(S,d)
            v=f(bp)-bp; s=np.sign(v); s[np.abs(v)<=1e-9]=0
            supp=int(np.sum(s!=0))
            print(f"  d={d} sd={seed}: |x*_VI - x*_LP|={lp_err:.2e} (LP==value)   CLY cut |support|={supp} (d={d}; >=3 => non-convex manufactured)",flush=True)
