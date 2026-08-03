"""Priority A+B diagnostics on ground-truth (rejection) covariances of real
balanced-cut trajectories. Per round, measure the quantities the Lyapunov / lambda_min
arguments need:

  aTop  = (u_top . m_K)^2 / lam_max     downdate FRACTION on the top axis (want >= a0>0: Priority A)
  align = |m_hat_K . u_top|             alignment of mean-shift with top axis (want ~1)
  rMin  = (u_min . m_K)^2 / lam_min     how much the SMALLEST axis is hit (want << 1: Priority B)
  lminR = lam_min(Sig')/lam_min(Sig)    actual smallest-eigenvalue survival (want >= c>0)
  lmaxR = lam_max(Sig')/lam_max(Sig)    (want <= 1-ish: top axis attacked)
Candidate Lyapunov potentials (scale-invariant): kappa, tr(S)tr(S^-1), std(log lam).
m_K is measured about the FW cut center (matches the (S) downdate).
"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import make_ssg, fixed_point, in_X, balanced, make_cut, K_ok

def rej(cuts, d, N, rng, mt=500):
    out=[]; tr=0
    while len(out)<N and tr<mt:
        P=rng.uniform(0,1,size=(4*N,d)); out.extend(list(P[in_X(P,cuts)])); tr+=1
    return np.array(out[:N]) if out else np.empty((0,d))

def spec(S):
    w=np.linalg.eigvalsh(np.cov(S.T)); return w

def potentials(w):
    kappa=w.max()/w.min()
    trtr=w.sum()*(1/w).sum()/len(w)     # /d so isotropic -> 1
    stdlog=float(np.std(np.log(w)))
    return kappa, trtr, stdlog

def main():
    for (d,delta,seed) in [(5,1e-3,1),(6,1e-3,2),(7,1e-3,3)]:
        rng=np.random.default_rng(seed); f,_=make_ssg(d,delta,seed); xstar=fixed_point(f,d)
        cuts=[]
        print(f"[SSG d={d} delta={delta}]  aTop align rMin | lminR lmaxR | kappa trtr stdlog")
        for t in range(13):
            X=rej(cuts,d,7000,rng)
            if len(X)<1500: break
            c=balanced(X[:90],d); c_,s_,vmag=make_cut(f,c)
            if vmag<1e-11: break
            keep=K_ok(X,c_,s_); K=X[keep]
            if len(K)<400: cuts.append((c_,s_)); continue
            SX=np.cov(X.T); wX,VX=np.linalg.eigh(SX)      # ascending
            u_min=VX[:,0]; u_top=VX[:,-1]; lmin=wX[0]; lmax=wX[-1]
            mK=K.mean(0)-c_                                 # kept-mean about cut center
            mn=np.linalg.norm(mK)+1e-15
            aTop=(u_top@mK)**2/lmax
            align=abs((mK/mn)@u_top)
            rMin=(u_min@mK)**2/lmin
            SK=np.cov(K.T); wK=np.linalg.eigvalsh(SK)
            lminR=wK[0]/lmin; lmaxR=wK[-1]/lmax
            kap,trtr,stdlog=potentials(wK)
            print(f"  t={t:2d}  {aTop:.2f} {align:.2f} {rMin:.2f} | {lminR:.2f} {lmaxR:.2f} | "
                  f"{kap:.2f} {trtr:.2f} {stdlog:.2f}")
            cuts.append((c_,s_))
    print("done")

if __name__=="__main__":
    main()
