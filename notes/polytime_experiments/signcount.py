import numpy as np, common as C
# How many DISTINCT sign vectors s^r appear in a realizable trajectory? (2^d possible)
def run(d, delta, seed, R):
    f,_=C.make_ssg(d,delta,seed); rng=np.random.default_rng(seed)
    cuts=[]; start=np.full(d,0.5); sigs=[]
    for t in range(R):
        S=C.hitrun(cuts,d,start,nsamp=40,thin=6,burn=200,nt=800,rng=rng)
        bp=C.balanced(S,d); v=f(bp)-bp
        s=np.sign(v); s[np.abs(v)<=1e-9]=0
        sigs.append(tuple(s.astype(int)))
        c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        cuts.append((c_,s_)); start=bp
    distinct=len(set(sigs))
    # also count distinct ignoring zeros (the +/- pattern on active coords)
    return d, seed, len(sigs), distinct, 2**d
print("Distinct sign vectors in realizable SSG trajectory (vs 2^d possible)",flush=True)
print(f"{'d':>2}{'sd':>3}{'rounds':>7}{'distinct_s':>11}{'2^d':>7}",flush=True)
for d in [4,5,6,8,10]:
    R=6*d
    for seed in [0,1,2]:
        r=run(d,1e-3,seed,R)
        print(f"{r[0]:>2}{r[1]:>3}{r[2]:>7}{r[3]:>11}{r[4]:>7}",flush=True)
