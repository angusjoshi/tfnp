import numpy as np, common as C
from conditioning import rej_sample
# Does diam(X_t) shrink geometrically with EXACT-REJECTION balanced centers (accurate)?
# CLY predicts yes (diam→ε in O(d log 1/ε) rounds). Plateau with cheap centers = artifact?
def dgap(xstar,types,succ):
    gaps=[]
    for i in range(len(types)):
        if types[i] in (0,1):
            vals=sorted([xstar[j] if j>=0 else (0.0 if j==-1 else 1.0) for j in succ[i]],reverse=(types[i]==0))
            if len(vals)>=2: gaps.append(abs(vals[0]-vals[1]))
    return min([g for g in gaps if g>1e-9],default=1.0)
def run(d,seed,T):
    f,types,succ,rew,gamma=C.make_ssg_full(d,1e-3,seed); xstar=C.fixed_point(f,d)
    dg=dgap(xstar,types,succ)
    r=np.random.default_rng(seed); cuts=[]; diams=[]
    for t in range(T):
        S,acc=rej_sample(cuts,d,400,r)
        if len(S)<60: break
        diam=float((S.max(0)-S.min(0)).max()); diams.append(diam)
        bp=C.balanced(S,d)  # EXACT-rejection-sample balanced center (accurate)
        c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        cuts.append((c_,s_))
    return dg,diams
print("diam(X_t) with EXACT-rejection accurate balanced centers. δ_gap = value gap.",flush=True)
for d in [4,5,6]:
    for seed in [0,1,2]:
        dg,diams=run(d,seed,2*d)
        # geometric rate estimate
        rate=(diams[-1]/diams[0])**(1/max(len(diams)-1,1)) if diams[0]>0 else float('nan')
        print(f"d={d} sd={seed} δ_gap={dg:.4f}: diam/round rate={rate:.3f} diam0={diams[0]:.2f} diamT={diams[-1]:.3f} reached_δ?={'Y' if diams[-1]<=dg else 'N'} traj={[round(x,2) for x in diams]}",flush=True)
