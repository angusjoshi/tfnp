import os
"""Decisive: is the late-round kappa climb at d=12,15 REAL anisotropy or
warm-start-sampler degradation? Build the real SSG cut history (warm-start algo),
then at a chosen round measure kappa with the honest extreme-start explorer at
ESCALATING hit-and-run budgets. If kappa falls with budget -> sampler artifact.
If it plateaus high -> real anisotropy (bad for C2)."""
import sys, time
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import make_ssg, fixed_point, in_X, chord_ts, balanced, make_cut, hitrun

def kap(S):
    w = np.linalg.eigvalsh(np.cov(S.T))
    diam2 = float(((S.max(0) - S.min(0)) ** 2).sum())
    return float(w.max()/max(w.min(),1e-18)), float(w.min())/max(diam2,1e-18)

def hr(p, cuts, d, rng, nstep, nt):
    for _ in range(nstep):
        u = rng.normal(size=d); u/=np.linalg.norm(u)
        fts = chord_ts(p, u, cuts, nt=nt)
        if len(fts)>0: p = p + rng.choice(fts)*u
    return p

def replenish(surv, cuts, d, N, rng, nstep, nt):
    out=list(surv)
    while len(out)<N: out.append(hr(out[rng.integers(len(out))].copy(),cuts,d,rng,nstep,nt))
    return np.array(out[:N])

def build_cuts(d, delta, seed, rounds):
    rng=np.random.default_rng(seed); f,_=make_ssg(d,delta,seed); xstar=fixed_point(f,d)
    pool=rng.uniform(0,1,size=(1200,d)); cuts=[]
    for t in range(rounds):
        sub=pool[rng.choice(len(pool),size=70,replace=False)]
        c=balanced(sub,d); c_,s_,v=make_cut(f,c)
        if v<1e-11: break
        cuts.append((c_,s_)); surv=pool[in_X(pool,cuts)]
        if len(surv)<20: break
        pool=replenish(list(surv),cuts,d,1200,rng,15,2000)
    return cuts, xstar, f

def extreme_starts(expl,k=6):
    mu=expl.mean(0); C=np.cov(expl.T)+1e-12*np.eye(expl.shape[1]); w,V=np.linalg.eigh(C)
    return [expl[np.argmax(expl@V[:,-1])],expl[np.argmin(expl@V[:,-1])],
            expl[np.argmax(expl@V[:,-2])],expl[np.argmin(expl@V[:,-2])],mu.copy()][:k]

def measure_escalate(cuts, d, xstar, rng, label):
    # independent-explorer kappa at escalating budgets (honest, not warm-start)
    for (burn,thin,ns,nt) in [(1500,18,180,2000),(5000,40,240,2500)]:
        t0=time.time()
        expl=hitrun(cuts,d,xstar.copy(),nsamp=ns,thin=thin,burn=burn,rng=rng,nt=nt)
        if len(expl)<50: print(f"  {label} budget{burn}: explorer failed"); continue
        starts=extreme_starts(expl)
        pooled=np.vstack([hitrun(cuts,d,s.copy(),nsamp=ns//2,thin=thin,burn=burn,rng=rng,nt=nt) for s in starts]+[expl])
        k,r=kap(pooled)
        print(f"  {label} budget(burn={burn},ns={ns},nt={nt}): kappa={k:.2f} lam_min/diam2={r:.1e} [{time.time()-t0:.0f}s]",flush=True)

def main():
    d=int(sys.argv[1]); delta=float(sys.argv[2]); seed=int(sys.argv[3])
    rounds=[int(x) for x in sys.argv[4].split(',')]
    rng=np.random.default_rng(seed+100)
    maxr=max(rounds)
    cuts,xstar,f=build_cuts(d,delta,seed,maxr)
    print(f"[kappa-escalate d={d} delta={delta} seed={seed}] built {len(cuts)} cuts",flush=True)
    for t in rounds:
        if t<=len(cuts):
            measure_escalate(cuts[:t], d, xstar, rng, f"t={t}")
    print("done",flush=True)

if __name__=="__main__":
    main()
