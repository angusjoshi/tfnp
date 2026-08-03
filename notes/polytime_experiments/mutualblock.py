import numpy as np, common as C
from conditioning import rej_sample
from sigma_verdict import build_controlled, spread_signs
from doublebind import group_by_sign
def seg_in(a,b,cuts,ns=14):
    ts=np.linspace(1/(ns+1),ns/(ns+1),ns)
    return C.in_X(a[None,:]+ts[:,None]*(b-a)[None,:],cuts).all()
def margin(y,cl): return min((s*(y-c)).max()+(s*(y-c)).min() for (c,s) in cl)
def run(cuts, Y, signs, eta=0.1):
    cl=group_by_sign(cuts); classes=list(range(len(cl)))
    p0=C.balanced(Y,len(Y[0]))
    corners=[np.where(np.array(sg)>0,1.0,0.0) for sg in signs]  # one per class sign
    # map class index (from group_by_sign order) to its sign corner
    csigns=[np.array(cl_[0][1]) for cl_ in cl]
    cor=[np.where(cs>0,1.0,0.0) for cs in csigns]
    g=[(1-eta)*cor[l]+eta*p0 for l in classes]
    med=np.median([margin(y,cl[l]) for y in Y for l in classes])
    Delta=0.2*med
    nDB=nMB=nUnc=0; hADD={1:0,2:0,3:0,'4+':0}
    for y in Y:
        bind=[l for l in classes if margin(y,cl[l])<=Delta]
        seesP0=seg_in(p0,y,cuts)
        sees=[seg_in(g[l],y,cuts) for l in classes]
        unc = (not seesP0) and (not any(sees))
        if unc: nUnc+=1
        if len(bind)>=2:
            nDB+=1
            mb=False
            for a in range(len(bind)):
                for b in range(a+1,len(bind)):
                    la,lb=bind[a],bind[b]
                    if (not sees[la]) and (not sees[lb]):
                        mb=True
                        hd=int(np.sum(csigns[la]!=csigns[lb]))
                        hADD[hd if hd<=3 else '4+']=hADD.get(hd if hd<=3 else '4+',0)+1
            if mb: nMB+=1
    n=len(Y)
    return nDB/n, nMB/n, nUnc/n, hADD
print("MutualBlock vs DoubleBind vs actual-uncovered (Δ=0.2·med, η=0.1)",flush=True)
print(f"{'d':>2}{'sigma':>6}{'DoubleBind':>11}{'MutualBlk':>10}{'uncovered':>10}{'Hamming(mb pairs)':>20}",flush=True)
for (d,sigma) in [(5,3),(5,5),(5,8),(4,3),(6,4)]:
    r2=np.random.default_rng(600); signs=spread_signs(d,sigma,r2)
    cuts,ok=build_controlled(d,min(2*d,10),signs,r2)
    if not ok: print(f"d={d} s={sigma} collapse");continue
    Y,_=rej_sample(cuts,d,300,r2)
    if len(Y)<60: print(f"d={d} s={sigma} undersampled");continue
    db,mb,unc,h=run(cuts,Y,signs)
    print(f"{d:>2}{sigma:>6}{db:>11.3f}{mb:>10.3f}{unc:>10.3f}   {dict(h)}",flush=True)
