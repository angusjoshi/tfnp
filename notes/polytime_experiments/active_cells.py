import numpy as np, common as C
from conditioning import rej_sample
# A(t) = # distinct STRATEGY patterns (argmax/argmin successor at each max/min node)
# spanned by samples of X_t, along the trajectory. Compare to 2^{#tied}, and vs delta.
def strat_pattern(y, types, succ):
    pat=[]
    for i in range(len(types)):
        if types[i] in (0,1):
            vals=np.array([y[j] if j>=0 else (0.0 if j==-1 else 1.0) for j in succ[i]])
            pat.append(int(np.argmax(vals)) if types[i]==0 else int(np.argmin(vals)))
    return tuple(pat)
def ntied(xstar,types,succ,tol=1e-6):
    c=0
    for i in range(len(types)):
        if types[i] in (0,1):
            vals=sorted([xstar[j] if j>=0 else (0.0 if j==-1 else 1.0) for j in succ[i]],reverse=(types[i]==0))
            if len(vals)>=2 and abs(vals[0]-vals[1])<tol: c+=1
    return c
def run(d,seed,delta,T):
    f,types,succ,rew,gamma=C.make_ssg_full(d,delta,seed); xstar=C.fixed_point(f,d)
    # delta_gap = min over non-tied max/min nodes of |top - runnerup| at x*
    gaps=[]
    for i in range(d):
        if types[i] in (0,1):
            vals=sorted([xstar[j] if j>=0 else (0.0 if j==-1 else 1.0) for j in succ[i]],reverse=(types[i]==0))
            if len(vals)>=2: gaps.append(abs(vals[0]-vals[1]))
    dgap=min([g for g in gaps if g>1e-9], default=1.0)
    nt=ntied(xstar,types,succ)
    r=np.random.default_rng(seed);cuts=[];start=np.full(d,0.5); traj=[]
    for t in range(T):
        S,_=rej_sample(cuts,d,300,r)
        if len(S)<40: break
        diam=float((S.max(0)-S.min(0)).max())
        A=len(set(strat_pattern(y,types,succ) for y in S))
        traj.append((t,A,diam))
        bp=C.balanced(S,d);c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        cuts.append((c_,s_));start=bp
    return dgap,nt,traj
print("A(t)=#strategy cells X_t spans, along trajectory. delta=value gap, tied=#tied nodes",flush=True)
for d in [5,6]:
    for seed in [0,1]:
        for delta in [1e-2,1e-4]:
            dgap,nt,traj=run(d,seed,delta,2*d)
            Amax=max(a for _,a,_ in traj); Alast=traj[-1][1]
            print(f"d={d} sd={seed} δin={delta}: value-gap={dgap:.3f} #tied={nt}  A(t) max={Amax} last={Alast}  2^tied={2**nt}  A-traj={[a for _,a,_ in traj]}",flush=True)
