import pickle, sys, math, bisect
from tabgen import H,R,D,IMAX,Q
tailLo,tailHi,phiLo,phiHi=pickle.load(open("table.pkl","rb"))
HR=H*R; DEN6=HR*6*Q*Q
def tailUp(y):
    i=(y+R-1)//R
    if i>IMAX: return tailHi[IMAX]
    d=i*R-y
    return tailHi[i]+(phiHi[i]*d*(6*Q*Q+3*i*d*Q+2*(i*d)**2))//DEN6+1
def tailDown(y):
    i=(y+R-1)//R
    if i>IMAX: return 0
    d=i*R-y
    return tailLo[i]+(phiLo[i]*d*(6*Q*Q+3*i*d*Q-d*d*H*H))//DEN6
def PhiUp(y): return D-tailDown(y) if y>=0 else tailUp(-y)
def PhiDown(y):
    if y>=0:
        t=tailUp(y); return D-t if t<=D else 0
    return tailDown(-y)
RD=10**12
def rinv(b2num,b2den):
    # 1/s where s^2 = 1-b^2 = (b2den-b2num)/b2den ; 1/s = sqrt(b2den/(b2den-b2num))
    lo=math.isqrt(b2den*RD*RD//(b2den-b2num))
    while (lo+1)**2*(b2den-b2num)<=b2den*RD*RD: lo+=1
    while lo*lo*(b2den-b2num)>b2den*RD*RD: lo-=1
    return lo,lo+1
# blocks: mult, tn, td, bn, bd, rl, rh
def mkblock(mult,tn,td,bn,bd):
    rl,rh=rinv(bn*bn,bd*bd)
    return (mult,tn,td,bn,bd,rl,rh)
BLOCKS=[mkblock(96,0,1,3,10),mkblock(1,12,5,-3,10),mkblock(3,22,5,-18,25)]
MTOT=sum(b[0] for b in BLOCKS)
ALPHA_INV=100
def yup(num,blk):
    mult,tn,td,bn,bd,rl,rh=blk
    return (num*(rh if num>=0 else rl)*R)//(td*bd*RD)+1
def ydown(num,blk):
    mult,tn,td,bn,bd,rl,rh=blk
    return (num*(rl if num>=0 else rh)*R)//(td*bd*RD)
def mnums(blk,zl,zh):
    mult,tn,td,bn,bd,rl,rh=blk
    m1=tn*bd*H+bn*zl*td; m2=tn*bd*H+bn*zh*td
    return max(m1,m2),min(m1,m2)
def Gup(ci,zl,zh,blocks=BLOCKS):
    tot=0
    for blk in blocks:
        mh,ml=mnums(blk,zl,zh); cc=ci*blk[2]*blk[4]
        tot+=blk[0]*(PhiUp(yup(mh-cc,blk))+PhiUp(yup(-ml-cc,blk)))
    return tot
def Glow(ci,zl,zh,blocks=BLOCKS):
    tot=0
    for blk in blocks:
        mh,ml=mnums(blk,zl,zh); cc=ci*blk[2]*blk[4]
        tot+=blk[0]*(PhiDown(ydown(ml-cc,blk))+PhiDown(ydown(-mh-cc,blk)))
    return tot
def certbin(zl,zh,ETA,c0,cmaxi=IMAX-1):
    cs=[c0]; c=c0
    while True:
        g=Gup(c,zl,zh)+ETA
        # largest c' with 2*ALPHA_INV*MTOT*tailLo[c'] >= g
        lo,hi=c,cmaxi
        if 2*ALPHA_INV*MTOT*tailLo[c]<g:  # cannot even stay
            break
        while lo<hi:
            mid=(lo+hi+1)//2
            if 2*ALPHA_INV*MTOT*tailLo[mid]>=g: lo=mid
            else: hi=mid-1
        if lo<=c: break
        c=lo; cs.append(c)
        if c>=cmaxi: return None
    a=c; b=a
    while b<=cmaxi:
        if 2*ALPHA_INV*MTOT*tailHi[b]+2*ETA<=Glow(b,zl,zh) and 2*ALPHA_INV*tailHi[b]<=D: break
        b+=1
    else: return None
    fN=Glow(b,zl,zh,BLOCKS[:1])-ETA
    if fN<=0: return None
    if zl>=0: dN=tailLo[zl]-tailHi[zh]
    else: dN=tailLo[-zh]-tailHi[-zl]
    if dN<=0: return None
    term=(fN*dN)//(2*MTOT*tailHi[a])
    return cs,b,term
def run(zmin,zmax,w,ETA):
    c0=0
    while 2*ALPHA_INV*tailLo[c0+1]>=D: c0+=1
    out=[]; tot=0; ncell=0
    for zl in range(zmin,zmax,w):
        zh=zl+w
        r=certbin(zl,zh,ETA,c0)
        if r is None: continue
        cs,b,term=r
        out.append((zl,zh,cs,b,term)); tot+=term; ncell+=len(cs)+1
    return out,tot,ncell,c0
if __name__=="__main__":
    w=int(sys.argv[1]); ETA=10**int(sys.argv[2])
    out,tot,ncell,c0=run(-5632,5632,w,ETA)
    print("w",w,"c0",c0,"bins",len(out),"cells",ncell,"ratio",tot/D)
    pickle.dump(out,open(f"cert_{w}.pkl","wb"))
