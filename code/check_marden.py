# Numeric + symbolic check of the identities used in Marden/Basic.lean
import random, cmath, sympy as sp
a,b,c,z=sp.symbols('a b c z')
p=(z-a)*(z-b)*(z-c); dp=sp.diff(p,z)
m=(a+b)/2
print("p'(m) + (a-b)^2/4 =", sp.simplify(sp.expand(dp.subs(z,m)+(a-b)**2/4)))
random.seed(1)
def rc(): return complex(random.uniform(-3,3),random.uniform(-3,3))
worst=0
for trial in range(2000):
    A,B,C=rc(),rc(),rc()
    s=A+B+C; q=A*B+B*C+C*A
    disc=cmath.sqrt(4*s*s-12*q)
    z1=(2*s+disc)/6; z2=(2*s-disc)/6
    S=[]
    for (u,v,w) in [(A,B,C),(B,C,A),(C,A,B)]:
        M=(u+v)/2; d=v-u
        prod=(M-z1)*(M-z2)
        assert abs(prod+d*d/12)<1e-9*(1+abs(d)**2)
        S.append(abs(M-z1)+abs(M-z2))
        # tangency: points on side line have focal sum >= S, equality only at t=0
        for t in [1e-3,-1e-3,0.3,-0.7,2.0]:
            P=M+t*d
            assert abs(P-z1)+abs(P-z2) > S[-1]-1e-12
    worst=max(worst,max(S)-min(S))
    S2=abs(z1-z2)**2/2+abs(A+B-2*C)**2/18+abs(A-B)**2/6
    assert abs(S[0]**2-S2)<1e-8*(1+S2)
print("max spread of focal sums over 3 midpoints:",worst)
print("all checks passed")

# Check of the statement of Marden.marden (Main.lean) on a concrete triangle, with
# z1,z2 obtained exactly as in exists_critical_points: z = (s ± r)/3, r^2 = s^2 - 3q.
A,B,C = 0j, 4+0j, 1+3j
s=A+B+C; q=A*B+B*C+C*A; r=cmath.sqrt(s*s-3*q)
z1,z2=(s+r)/3,(s-r)/3
for z in (z1,z2):
    assert abs(3*z*z-2*s*z+q)<1e-12
fs=lambda z: abs(z-z1)+abs(z-z2)
twoA=fs((A+B)/2)
print("2A =",twoA, [fs((A+B)/2),fs((B+C)/2),fs((C+A)/2)])
for (x,y) in [(A,B),(B,C),(C,A)]:
    for t in [-2,-0.5,-1e-4,1e-4,0.5,2]:
        assert fs((x+y)/2+t*(y-x))>twoA
assert abs((z1+z2)/2-s/3)<1e-12
print("Main.lean statement verified numerically on triangle 0,4,1+3i")
