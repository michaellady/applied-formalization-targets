# exact-integer generator for the normal table and the certificate
import sys, math, pickle
H=1024; R=4096; D=10**40; IMAX=10752
Q=H*H*R
PI_LO=314159265358979323846; PI_HI=314159265358979323847; PI_DEN=10**20
def isqrt(n): return math.isqrt(n)
def cdiv(a,b): return -((-a)//b)
def build():
    # phi(0)=1/sqrt(2pi): phiHi0^2*2*PI_LO >= D^2*PI_DEN
    hi0 = isqrt(cdiv(D*D*PI_DEN, 2*PI_LO))+1
    while (hi0-1)**2*2*PI_LO >= D*D*PI_DEN: hi0-=1
    lo0 = isqrt((D*D*PI_DEN)//(2*PI_HI))
    while (lo0+1)**2*2*PI_HI <= D*D*PI_DEN: lo0+=1
    assert hi0*hi0*2*PI_LO >= D*D*PI_DEN and lo0*lo0*2*PI_HI <= D*D*PI_DEN
    phiHi=[hi0]; phiLo=[lo0]
    B=2*H*H
    for i in range(IMAX):
        a=2*i+1
        P3=96*B**4-96*a*B**3+48*a*a*B*B-16*a**3*B
        up=P3+5*a**4; low=P3-5*a**4
        phiHi.append(cdiv(phiHi[-1]*up,96*B**4)); phiLo.append((phiLo[-1]*low)//(96*B**4))
    tailHi=[0]*(IMAX+1); tailLo=[0]*(IMAX+1)
    tailHi[IMAX]=cdiv(phiHi[IMAX]*H,IMAX); tailLo[IMAX]=0
    den=H*R*6*Q*Q
    for i in range(IMAX-1,-1,-1):
        ip=i+1; d=R
        Un=d*(6*Q*Q+3*ip*d*Q+2*(ip*d)**2)
        Ln=d*(6*Q*Q+3*ip*d*Q-d*d*H*H)
        tailHi[i]=tailHi[i+1]+cdiv(phiHi[i+1]*Un,den)
        tailLo[i]=tailLo[i+1]+(phiLo[i+1]*Ln)//den
    return tailLo,tailHi,phiLo,phiHi
if __name__=="__main__":
    t=build()
    pickle.dump(t,open("table.pkl","wb"))
    tailLo,tailHi,phiLo,phiHi=t
    from scipy.special import ndtr
    for x in [0,0.5,1,2,3,4,5,6,8,10,10.5]:
        i=int(x*H)
        print(x, tailLo[i]/D, tailHi[i]/D, ndtr(-x), (tailHi[i]-tailLo[i])/max(tailLo[i],1))
