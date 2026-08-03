"""Bridge from the symmetric-case theorem (S) to real (asymmetric) bodies.
(S) Sigma(X cap K) = Sigma(X) - m_K m_K^T holds exactly when X is symmetric about
c, because then removed half R = reflection of kept half K': Sigma(R)=Sigma(K'),
m_R=-m_K. For REAL balanced cuts we measure the asymmetry defects:
   dSigma = ||Sigma(R)-Sigma(K')|| / ||Sigma(X)||     (0 if symmetric)
   dmean  = ||m_R + m_K|| / diam                        (0 if symmetric)
and how well the rank-1 downdate PREDICTS the real Sigma(K'):
   pred_err = ||Sigma(K') - (Sigma(X)-m_K m_K^T)|| / ||Sigma(X)||
If small on real bodies => (S) approximately governs the real dynamics =>
balanced cuts approximately self-correct.  Exact rejection sampling.
"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import make_ssg, fixed_point, in_X, balanced, make_cut, K_ok

def rej(cuts, d, N, rng, mt=400):
    out=[]; tr=0
    while len(out)<N and tr<mt:
        P=rng.uniform(0,1,size=(4*N,d)); out.extend(list(P[in_X(P,cuts)])); tr+=1
    return np.array(out[:N]) if out else np.empty((0,d))

def frob(A): return float(np.sqrt((A*A).sum()))

def main():
    for (d,delta,seed) in [(5,1e-3,1),(6,1e-3,2),(7,1e-3,3),(8,1e-4,4)]:
        rng=np.random.default_rng(seed); f,_=make_ssg(d,delta,seed); xstar=fixed_point(f,d)
        cuts=[]
        print(f"[SSG d={d} delta={delta}] round: dSigma dmean pred_err | kappa->kappa'")
        for t in range(14):
            X=rej(cuts,d,6000,rng)
            if len(X)<1500: break
            c=balanced(X[:80],d); c_,s_,vmag=make_cut(f,c)
            if vmag<1e-11: break
            keep=K_ok(X,c_,s_); K=X[keep]; R=X[~keep]
            if len(K)<300 or len(R)<300:
                cuts.append((c_,s_)); continue
            SX=np.cov(X.T); SK=np.cov(K.T); SR=np.cov(R.T)
            mK=K.mean(0)-c_; mR=R.mean(0)-c_   # relative to cut center
            diam=float((X.max(0)-X.min(0)).max())
            dS=frob(SR-SK)/frob(SX); dm=np.linalg.norm(mR+mK)/diam
            pred=SX-np.outer(K.mean(0),K.mean(0))+np.outer(X.mean(0),X.mean(0))  # Sigma(X)-cov-shift approx
            # cleaner: predicted Sigma(K') under (S) uses mean shift of kept half about X-mean
            mKx=K.mean(0)-X.mean(0)
            pred=SX-np.outer(mKx,mKx)*(len(R)/len(X))*2  # (S)-type; coefficient from p=1/2
            perr=frob(SK-(SX-np.outer(mKx,mKx)))/frob(SX)
            kX=np.linalg.eigvalsh(SX); kK=np.linalg.eigvalsh(SK)
            print(f"   t={t:2d}  dSigma={dS:.2f} dmean={dm:.2f} pred_err={perr:.2f} "
                  f"frac={keep.mean():.2f} | k {kX.max()/kX.min():.1f}->{kK.max()/kK.min():.1f}")
            cuts.append((c_,s_))
    print("done")

if __name__=="__main__":
    main()
