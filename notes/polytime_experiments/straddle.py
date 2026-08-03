import numpy as np, common as C
from conditioning import rej_sample
from cc_measure import seg_in, convex_ok
rng=np.random.default_rng(21)
def greedy_pieces(Y,cuts,rng,tgt=0.95):
    n=len(Y);cov=np.zeros(n,bool);pieces=[]
    while cov.mean()<tgt and len(pieces)<n:
        unc=np.where(~cov)[0]; seed=unc[0];Q=[Y[seed]];mem=[seed]
        for q in unc[1:]:
            if seg_in(Y[seed],Y[q],cuts) and convex_ok(Q+[Y[q]],cuts,rng=rng):
                Q.append(Y[q]);mem.append(q)
        cov[mem]=True;pieces.append(mem)
    return pieces
def build(d,seed,T):
    f,_=C.make_ssg(d,1e-3,seed);r=np.random.default_rng(seed);cuts=[];start=np.full(d,0.5)
    for t in range(T):
        S,_=rej_sample(cuts,d,300,r)
        if len(S)<40: break
        bp=C.balanced(S,d);c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        cuts.append((c_,s_));start=bp
    return cuts
print("straddle_t: # convex pieces of X_{t-1} that straddle >=2 pyramids of cut t",flush=True)
print("(additive CC=poly iff straddle small/flat;  CC_t <= CC_{t-1}+(d-1)straddle_t)",flush=True)
print(f"{'d':>2}{'sd':>3}{'t-1':>4}{'CC(t-1)':>8}{'straddle':>9}{'CC(t)':>6}",flush=True)
for d in [4,5]:
    for seed in [0,1]:
        for tm1 in [d, 2*d-1]:
            cutsA=build(d,seed,tm1)
            if len(cutsA)<tm1: continue
            Y,_=rej_sample(cutsA,d,220,np.random.default_rng(80+seed))
            if len(Y)<50: continue
            pieces=greedy_pieces(Y,cutsA,rng)
            # next cut: reproduce round tm1's balanced-point cut on X_{t-1}
            f,_=C.make_ssg(d,1e-3,seed); bp=C.balanced(Y,d)  # balanced pt of current samples
            v=f(bp)-bp; s=np.sign(v); s[np.abs(v)<=1e-9]=0
            # pyramid index of a point under cut (bp,s): argmax_i s_i*(y_i-bp_i)
            def pyr(y): return int(np.argmax(s*(y-bp)))
            straddle=0
            for mem in pieces:
                ks=set(pyr(Y[i]) for i in mem)
                if len(ks)>=2: straddle+=1
            CCt = len(pieces) + (d-1)*straddle  # upper-bound proxy for CC_t
            print(f"{d:>2}{seed:>3}{tm1:>4}{len(pieces):>8}{straddle:>9}{CCt:>6}",flush=True)
