import numpy as np, common as C
# Dominant-coordinate identification margin (convex-cell's load-bearing quantity).
def run(d, delta, seed, R):
    f,_=C.make_ssg(d,delta,seed); xs=C.fixed_point(f,d); rng=np.random.default_rng(seed)
    cuts=[]; start=np.full(d,0.5)
    margins=[]; id_ok=0; nt=0; safe_counts=[]; lockMs=[]; min_neg=0
    for t in range(R):
        S=C.hitrun(cuts,d,start,nsamp=40,thin=6,burn=200,nt=800,rng=rng)
        bp=C.balanced(S,d); v=f(bp)-bp
        s=np.sign(v); s[np.abs(v)<=1e-9]=0
        gap=np.abs(xs-bp); order=np.argsort(gap)[::-1]
        g1,g2=gap[order[0]],gap[order[1]]
        m=(g1-g2)/g1 if g1>0 else 0.0; margins.append(m)
        kstar=order[0]; khat=int(np.argmax(np.abs(v))); nt+=1
        if khat==kstar: id_ok+=1
        # safe-pyramid count: #{k: w_k(x*) >= -min_j w_j(x*)}, w=s*(x*-bp) but use s from validity sign of (x*-bp)
        w=np.sign(xs-bp)*(xs-bp)  # =|x*-bp|, that's not the cut sign. Use actual cut sign s where nonzero, else sign(x*-bp)
        sc=s.copy(); sc[sc==0]=np.sign((xs-bp))[sc==0]
        wx=sc*(xs-bp); mn=wx.min()
        safe_counts.append(int(np.sum(wx>=-mn-1e-9)))
        # lock-M: smallest M<=50 with argmax|f^M(bp)-bp| == kstar stably
        z=bp.copy(); lock=99
        for M in range(1,51):
            z=f(z)
            if int(np.argmax(np.abs(z-bp)))==kstar:
                # check stability: also M+ a couple
                lock=M; break
        lockMs.append(lock)
        c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        cuts.append((c_,s_)); start=bp
    return (np.mean(margins),np.min(margins),id_ok/nt,np.mean(safe_counts),
            np.median(lockMs),int(1/delta))
print("Dominant-coordinate ID: margin, 1-query ID rate, safe-pyramids, lock-M",flush=True)
print(f"{'d':>2}{'1/δ':>7}{'sd':>3}{'mean_m':>8}{'min_m':>7}{'IDrate':>7}{'safe#':>6}{'lockM':>6}",flush=True)
for d in [4,5,6]:
    for delta in [1e-2,1e-3,1e-4]:
        for seed in [0,1]:
            r=run(d,delta,seed,5*d)
            print(f"{d:>2}{r[5]:>7}{seed:>3}{r[0]:>8.3f}{r[1]:>7.3f}{r[2]:>7.2f}{r[3]:>6.1f}{r[4]:>6.0f}",flush=True)
