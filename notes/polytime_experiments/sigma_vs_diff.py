import numpy as np, common as C
# Does sigma (# distinct signs) control difficulty (x*-in-kernel fraction & kappa)?
def run(d, delta, seed, R):
    f,_=C.make_ssg(d,delta,seed); xs=C.fixed_point(f,d); rng=np.random.default_rng(seed)
    cuts=[]; start=np.full(d,0.5); sigs=[]; kerok=0; nt=0; lastS=None
    for t in range(R):
        S=C.hitrun(cuts,d,start,nsamp=40,thin=6,burn=200,nt=800,rng=rng); lastS=S
        bp=C.balanced(S,d); v=f(bp)-bp
        s=np.sign(v); s[np.abs(v)<=1e-9]=0
        sigs.append(tuple(s.astype(int)))
        w=np.sort(s*(xs-bp)); nt+=1
        if w[0]+w[1]>=-1e-7: kerok+=1
        c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        cuts.append((c_,s_)); start=bp
    # kappa of last sample
    Cov=np.cov(lastS.T)+1e-12*np.eye(d); ev=np.linalg.eigvalsh(Cov)
    kap=ev.max()/max(ev.min(),1e-15)
    return len(set(sigs)), kerok/nt, kap
print("sigma (#distinct signs) vs difficulty  [SSG, 1e-3]",flush=True)
print(f"{'d':>2}{'sd':>3}{'sigma':>6}{'x*kerFrac':>10}{'kappa':>8}",flush=True)
rows=[]
for d in [4,5,6,7]:
    for seed in range(4):
        sig,kf,kap=run(d,1e-3,seed,6*d)
        rows.append((sig,kf,kap))
        print(f"{d:>2}{seed:>3}{sig:>6}{kf:>10.2f}{kap:>8.1f}",flush=True)
import numpy as np
R=np.array(rows,float)
print(f"corr(sigma, x*kerFrac) = {np.corrcoef(R[:,0],R[:,1])[0,1]:+.2f}",flush=True)
print(f"corr(sigma, kappa)     = {np.corrcoef(R[:,0],R[:,2])[0,1]:+.2f}",flush=True)
