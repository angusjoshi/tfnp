import numpy as np, common as C, friedmann as F
from conditioning import rej_sample
from active_cells import strat_pattern
# A(t) on the ADVERSARIAL Melekopoglou-Condon instance (many contested nodes, PI=2^n).
# Also report #max/min nodes and how many are "contested" over the box (argmax varies).
def build_and_measure(n):
    types,succ,rew,gamma,meta=F.mc_basic(n)
    d=len(types)
    f=F.make_operator(types,succ,rew,gamma)
    xstar=C.fixed_point(f,d)
    nmm=sum(1 for t in types if t in (0,1))
    r=np.random.default_rng(0); cuts=[]; start=np.full(d,0.5); traj=[]
    # contested over box:
    Sbox,_=rej_sample([],d,300,r)
    Abox=len(set(strat_pattern(y,types,succ) for y in Sbox))
    for t in range(2*d):
        S,_=rej_sample(cuts,d,250,r)
        if len(S)<40: break
        A=len(set(strat_pattern(y,types,succ) for y in S))
        traj.append(A)
        bp=C.balanced(S,d); c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        cuts.append((c_,s_)); start=bp
    return d,nmm,Abox,traj
print("A(t) on Melekopoglou-Condon (adversarial, PI=2^n switches). #mm=max/min nodes",flush=True)
print(f"{'n':>2}{'d':>3}{'#mm':>5}{'A(box)':>7}{'A(t)-traj':>30}",flush=True)
for n in [3,4,5,6]:
    d,nmm,Abox,traj=build_and_measure(n)
    print(f"{n:>2}{d:>3}{nmm:>5}{Abox:>7}   {traj}",flush=True)
