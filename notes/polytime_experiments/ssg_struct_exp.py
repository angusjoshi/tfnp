import numpy as np, common as C
from conditioning import rej_sample
rng=np.random.default_rng(41)
def build(d,seed,T):
    f,types,succ,rew,gamma=C.make_ssg_full(d,1e-3,seed)
    r=np.random.default_rng(seed);cuts=[];start=np.full(d,0.5);pairs=set();comp_per_round=[]
    xstar=C.fixed_point(f,d)
    for t in range(T):
        S,_=rej_sample(cuts,d,300,r)
        if len(S)<40: break
        bp=C.balanced(S,d)
        # EXP-2: at each MAX/MIN node, the decisive comparison = (argwinner, runner-up) among succ
        for i in range(d):
            sc=succ[i]
            if types[i] in (0,1):  # max or min node
                vals=np.array([bp[j] if j>=0 else (0.0 if j==-1 else 1.0) for j in sc])
                order=np.argsort(vals)
                win = order[-1] if types[i]==0 else order[0]   # argmax / argmin
                run = order[-2] if types[i]==0 else order[1]
                pairs.add((i,int(sc[win]),int(sc[run])))
        c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        cuts.append((c_,s_));start=bp
    return cuts,pairs,len(cuts),types,succ
print("EXP-1: thinnest direction v_min alignment — axis (e_i) vs difference (e_i±e_j)?",flush=True)
print(f"{'d':>2}{'sd':>3}{'axisOvlp':>9}{'diffOvlp':>9}",flush=True)
for d in [4,5,6]:
    for seed in [0,1]:
        cuts,_,tc,_,_=build(d,seed,2*d)
        if len(cuts)<2: print(f"{d} {seed} collapse");continue
        Y,_=rej_sample(cuts,d,400,np.random.default_rng(90+seed))
        if len(Y)<60: print(f"{d} {seed} undersampled");continue
        Cov=np.cov(Y.T); w,V=np.linalg.eigh(Cov); vmin=V[:,0]
        axis=np.max(np.abs(vmin))
        diff=max(abs(vmin[i]+vmin[j])/np.sqrt(2) for i in range(d) for j in range(d) if i!=j)
        diff=max(diff, max(abs(vmin[i]-vmin[j])/np.sqrt(2) for i in range(d) for j in range(d) if i!=j))
        print(f"{d:>2}{seed:>3}{axis:>9.2f}{diff:>9.2f}",flush=True)
print("EXP-2: #distinct decisive comparison pairs vs d, d*t (fixed graph => predict poly(d))",flush=True)
print(f"{'d':>2}{'sd':>3}{'t':>4}{'distinctPairs':>14}{'d*t':>6}{'maxposs':>8}",flush=True)
for d in [4,5,6]:
    for seed in [0,1]:
        cuts,pairs,tc,types,succ=build(d,seed,2*d)
        maxposs=sum(len(succ[i])*(len(succ[i])-1) for i in range(d) if types[i] in (0,1))
        print(f"{d:>2}{seed:>3}{tc:>4}{len(pairs):>14}{d*tc:>6}{maxposs:>8}",flush=True)
