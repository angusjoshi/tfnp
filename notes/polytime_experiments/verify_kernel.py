import numpy as np
rng = np.random.default_rng(7)
# High-res ray test: z in ker(K) iff no direction has phi>=0 ... <0 ... >=0 (re-entry), K={max+min>=0}
def has_reentry(z,d,ndir=20000,nt=4000,Tmax=400.0,tol=1e-9):
    U=rng.normal(size=(ndir,d)); U/=np.linalg.norm(U,axis=1,keepdims=True)
    ts=np.linspace(0,Tmax,nt)
    P=z[None,None,:]+ts[None,:,None]*U[:,None,:]
    phi=P.max(2)+P.min(2)
    mem=phi>=-tol
    ff=np.where(~mem,np.arange(nt)[None,:],nt).min(1)
    idx=np.arange(nt)[None,:]
    return (((idx>=ff[:,None])&mem).any(1)).any()

# targeted: clear conj-violators should have re-entry (NOT in kernel)
tests_out = [np.array([-1.,0.5,3.]), np.array([-1.,0.5,0.6]), np.array([-2.,1.,1.5,5.])]
for z in tests_out:
    s=np.sort(z); print(f"z={z}  two-smallest-sum={s[0]+s[1]:.3f} (<0 => conj:NOT ker)   reentry_found={has_reentry(z,len(z))}")

# borderline earlier 'disagreements' (pair sum tiny negative): should ALSO have re-entry
print("--- borderline (pair sum slightly <0): expect reentry=True if conj exact ---")
for z in [np.array([-0.721,0.713,0.919]), np.array([-0.654,0.615,1.493]), np.array([-0.358,0.303,1.6])]:
    s=np.sort(z); print(f"z={z} sum2={s[0]+s[1]:.4f}  reentry_found={has_reentry(z,len(z))}")

# clear interior of conj (all pairwise >0) should have NO re-entry
print("--- interior (all pairwise sums >0): expect reentry=False ---")
for z in [np.array([1.,1.,1.]), np.array([2.,-0.5,1.,0.7]), np.array([0.1,0.2,5.])]:
    s=np.sort(z); print(f"z={z} sum2={s[0]+s[1]:.3f}  reentry_found={has_reentry(z,len(z))}")
