import numpy as np, common as C
from conditioning import rej_sample
# k'_lb = # distinct arrangement-cell signatures among rejection samples of X_t.
# cell signature of y = per round r: (argmax_i w_i^r, argmin_i w_i^r), w^r = s^r*(y-c^r).
def build_ssg(d,seed,T):
    f,_=C.make_ssg(d,1e-3,seed); rng=np.random.default_rng(seed)
    cuts=[]; start=np.full(d,0.5); sigs=set()
    for t in range(T):
        S,_=rej_sample(cuts,d,300,rng)
        if len(S)<40: break
        bp=C.balanced(S,d); c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        sigs.add(tuple(s_.astype(int))); cuts.append((c_,s_)); start=bp
    return cuts, len(sigs)
def cellcount(cuts, Y):
    sigset=set()
    for y in Y:
        sig=[]
        for (c,s) in cuts:
            w=s*(y-c); sig.append((int(np.argmax(w)),int(np.argmin(w))))
        sigset.add(tuple(sig))
    return len(sigset)
print("k'_lb = distinct arrangement cells (runtime quantity) vs d, sigma  [SSG,t=2d]",flush=True)
print(f"{'d':>2}{'sd':>3}{'t':>4}{'sigma':>6}{'kprime_lb':>10}{'nsamp':>6}",flush=True)
for d in [3,4,5,6]:
    for seed in [0,1,2]:
        cuts,sig=build_ssg(d,seed,2*d)
        if len(cuts)<2: print(f"{d:>2}{seed:>3}   collapse"); continue
        Y,acc=rej_sample(cuts,d,500,np.random.default_rng(900+seed))
        if len(Y)<60: print(f"{d:>2}{seed:>3}{len(cuts):>4} undersampled acc={acc:.1e}"); continue
        kp=cellcount(cuts,Y)
        print(f"{d:>2}{seed:>3}{len(cuts):>4}{sig:>6}{kp:>10}{len(Y):>6}",flush=True)
