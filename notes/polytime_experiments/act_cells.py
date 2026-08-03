import numpy as np
from common import hitrun, balanced, make_cut, in_X, ssg_value_gap
from friedmann import make_operator
from ssg_strategy_check import rand_instance, val_iter, strategy_cloud
def run(seed, d=6, R=16):
    types,succ,rew,gamma=rand_instance(d,1e-3,seed)
    if not((types==0).any() and (types==1).any()): return None
    cloud,m=strategy_cloud(types,succ,rew,gamma)
    if m>9 or m==0: return None
    xstar=val_iter(types,succ,rew,gamma); dgap,_=ssg_value_gap(xstar,types,succ)
    f=make_operator(types,succ,rew,gamma); rng=np.random.default_rng(seed)
    cuts=[]; start=np.full(d,0.5); rows=[]
    for t in range(R):
        S=hitrun(cuts,d,start,nsamp=30,thin=15,burn=800,rng=rng)
        bp=balanced(S,d); inx=in_X(cloud,cuts); surv=cloud[inx]
        cdiam=float(np.max(np.max(surv,0)-np.min(surv,0))) if len(surv)>1 else 0.0
        dis=len({tuple(np.round(y,8)) for y in surv})
        rows.append((t,int(inx.sum()),dis,cdiam))
        c_,s_,vmag=make_cut(f,bp)
        if vmag<1e-9: break
        cuts.append((c_,s_)); start=bp.copy()
    return m,len(cloud),dgap,rows
for seed in range(6):
    r=run(seed)
    if r is None: continue
    m,nc,dgap,rows=r
    print(f'seed{seed} m={m} |cloud|={nc} dgap={dgap:.2e}',flush=True)
    for (t,ins,dis,cd) in rows[::2]:
        print(f'   t={t:2d} #inX={ins:4d} #distinct={dis:4d} survdiam={cd:.2e} dgap={dgap:.1e}',flush=True)
