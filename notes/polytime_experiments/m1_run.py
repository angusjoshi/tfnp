import numpy as np, common as C
def run(d, delta, seed, R=22):
    f,_=C.make_ssg(d,delta,seed); xstar=C.fixed_point(f,d)
    rng=np.random.default_rng(seed)
    cuts=[]; start=np.full(d,0.5); L=np.zeros(d); U=np.ones(d)
    onesign=0; widths=[]; asizes=[]; xin=True
    for t in range(R):
        S=C.hitrun(cuts,d,start,nsamp=30,thin=6,burn=200,nt=800,rng=rng)
        bp=C.balanced(S,d); v=f(bp)-bp
        s=np.sign(v); s[np.abs(v)<=1e-9]=0; nz=s[s!=0]
        if len(nz)>0 and (np.all(nz>0) or np.all(nz<0)): onesign+=1
        if np.all(v>=-1e-9): L=np.maximum(L,bp)
        if np.all(v<=1e-9): U=np.minimum(U,bp)
        widths.append(float(np.max(U-L)))
        if np.any(xstar<L-1e-6) or np.any(xstar>U+1e-6): xin=False
        gap=np.abs(xstar-bp); mx=gap.max()+1e-15; asizes.append(int(np.sum(gap>=0.5*mx)))
        c_,s_,vmag=C.make_cut(f,bp)
        if vmag<1e-11: break
        cuts.append((c_,s_)); start=bp.copy()
    n=len(widths); w=np.array(widths)
    rate=(w[-1]/w[0])**(1.0/max(n-1,1)) if w[0]>0 else float('nan')
    return d,delta,seed,n,onesign/n,w[-1],rate,1-delta,float(np.mean(asizes)),max(asizes),xin
print(f"{'d':>2}{'delta':>7}{'sd':>3}{'rnds':>5}{'1sgn%':>6}{'widT':>7}{'wrate':>7}{'lam':>6}{'mnA':>5}{'mxA':>4}{'xin':>4}",flush=True)
for d in [4,5,6]:
    for seed in [0,1]:
        r=run(d,1e-3,seed)
        print(f"{r[0]:>2}{r[1]:>7.0e}{r[2]:>3}{r[3]:>5}{r[4]*100:>5.0f}%{r[5]:>7.3f}{r[6]:>7.3f}{r[7]:>6.3f}{r[8]:>5.1f}{r[9]:>4}{str(r[10]):>4}",flush=True)
