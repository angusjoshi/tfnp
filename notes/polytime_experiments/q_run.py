import numpy as np, common as C
from conditioning import rej_sample
rng=np.random.default_rng(0)

def visible(z, Y, inmask_fn, nseg=10):
    # fraction of Y visible from z: segment [z,y] stays inside (all nseg interior pts in body)
    ts=np.linspace(0.08,0.92,nseg)
    vis=np.zeros(len(Y),bool)
    for k,y in enumerate(Y):
        P=z[None,:]+ts[:,None]*(y-z)[None,:]
        vis[k]=inmask_fn(P).all()
    return vis

def greedy_cover(Y, cands, inmask_fn, target=0.93):
    covered=np.zeros(len(Y),bool); k=0
    visc={j:visible(cands[j],Y,inmask_fn) for j in range(len(cands))}
    while covered.mean()<target and k<len(cands):
        best=max(range(len(cands)), key=lambda j:(visc[j]&~covered).sum())
        gain=(visc[best]&~covered).sum()
        if gain==0: break
        covered|=visc[best]; k+=1
    return k, covered.mean()

# ---- calibration bodies ----
def cover_body(inmask_fn, box_sampler, ncloud=500, ncand=25):
    Y=box_sampler(ncloud); cand=box_sampler(ncand)
    return greedy_cover(Y,cand,inmask_fn)

print("CALIBRATION",flush=True)
# dumbbell in 2D: two boxes joined by thin neck along x; expect k~2-3
def dumbbell_mask(P):
    x,y=P[:,0],P[:,1]
    lobeL=(x<0.35)&(y>0.2)&(y<0.8); lobeR=(x>0.65)&(y>0.2)&(y<0.8)
    neck=(x>=0.35)&(x<=0.65)&(y>0.47)&(y<0.53)
    return lobeL|lobeR|neck
def dumbbell_samp(n):
    out=[]
    while len(out)<n:
        P=rng.uniform(0,1,(4000,2)); out.extend(P[dumbbell_mask(P)])
    return np.array(out[:n])
kd,cd=cover_body(dumbbell_mask,dumbbell_samp); print(f"  dumbbell(2D):  k={kd} cov={cd:.2f}  (expect ~2-3)",flush=True)

# comb with m teeth: expect k~m
for m in [3,5]:
    def comb_mask(P,m=m):
        x,y=P[:,0],P[:,1]
        base=(y<0.2)
        tooth=np.zeros(len(P),bool)
        for i in range(m):
            cx=(i+0.5)/m
            tooth|=(np.abs(x-cx)<0.5/(2*m))&(y>=0.2)&(y<0.9)
        return base|tooth
    def comb_samp(n,m=m):
        out=[]
        while len(out)<n:
            P=rng.uniform(0,1,(4000,2)); out.extend(P[comb_mask(P)])
        return np.array(out[:n])
    kc,cc=cover_body(comb_mask,comb_samp); print(f"  comb(m={m}):    k={kc} cov={cc:.2f}  (expect ~{m})",flush=True)

# ---- realizable SSG X_t ----
print("REALIZABLE SSG  X_t (t=d)",flush=True)
def run_real(d,seed):
    f,_=C.make_ssg(d,1e-3,seed); xs=C.fixed_point(f,d)
    cuts=[]; start=np.full(d,0.5)
    for t in range(d):
        S,_=rej_sample(cuts,d,400,rng)
        if len(S)<50: break
        bp=C.balanced(S,d); c_,s_,vm=C.make_cut(f,bp)
        if vm<1e-11: break
        cuts.append((c_,s_)); start=bp
    Y,_=rej_sample(cuts,d,500,rng)
    if len(Y)<50: return None
    cand=np.vstack([np.array([c for c,_ in cuts]), rej_sample(cuts,d,20,rng)[0]]) if cuts else Y[:20]
    inmask=lambda P: C.in_X(P,cuts)
    return greedy_cover(Y,cand,inmask)
for d in [3,4,5]:
    ks=[]
    for seed in [0,1]:
        r=run_real(d,seed)
        if r: ks.append(r[0])
    print(f"  d={d}: k={ks}",flush=True)
