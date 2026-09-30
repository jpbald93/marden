"""Phase 2 numeric/symbolic checks for uniqueness of the Steiner inellipse."""
import sympy as sp, random, cmath, math
# 1. certificate for lam_eq_core (conjugates treated as independent variables)
a,b,c,f1,f2,A,B,C,F1,F2,l1,l2,l=sp.symbols('a b c f1 f2 A B C F1 F2 l1 l2 l')
m1,m2,m3=(a+b)/2,(b+c)/2,(c+a)/2; M1,M2=(A+B)/2,(B+C)/2
P1=(m1-f1)*(m1-f2)+l1*(b-a)**2; P2=(m2-f1)*(m2-f2)+l2*(c-b)**2
P1c=(M1-F1)*(M1-F2)+l1*(B-A)**2; P2c=(M2-F1)*(M2-F2)+l2*(C-B)**2
Fq=((m1-f1)*(M1-F1)+(m1-f2)*(M1-F2)+2*l1*(b-a)*(B-A))-((m2-f1)*(M2-F1)+(m2-f2)*(M2-F2)+2*l2*(c-b)*(C-B))
goal=(l1-l2)*((B-A)*(c-b)-(b-a)*(C-B))**2
assert sp.expand(goal-(-(c-a)*(C-A)*Fq+(C-A)**2*(P1-P2)+(c-a)**2*(P1c-P2c)))==0
# 2. lam_twelfth_core
Q=lambda m,d:(m-f1)*(m-f2)+l*d**2
assert sp.factor(sp.expand(8*((m2-m3)*Q(m1,b-a)+(m3-m1)*Q(m2,c-b)+(m1-m2)*Q(m3,a-c))))==sp.factor((a-b)*(a-c)*(b-c)*(12*l-1))
print("symbolic certificates ok")
# 3. numeric: random ellipses tangent-at-midpoint fail unless foci = critical points
def fs(f1,f2,z): return abs(z-f1)+abs(z-f2)
random.seed(1)
bad=0
for _ in range(2000):
    a,b,c=[complex(random.uniform(-5,5),random.uniform(-5,5)) for _ in range(3)]
    s=2*(a+b+c)/3; q=(a*b+b*c+c*a)/3; r=cmath.sqrt(s*s-4*q); z1,z2=(s+r)/2,(s-r)/2
    # perturb foci; check the hypotheses of steiner_unique then fail
    f1=z1+complex(random.gauss(0,.3),random.gauss(0,.3)); f2=z2
    ms=[(a+b)/2,(b+c)/2,(c+a)/2]
    vals=[fs(f1,f2,m) for m in ms]
    if max(vals)-min(vals)<1e-9: bad+=1
print("perturbed foci with equal midpoint focal sums:",bad)
