"""Exact independent integration, matrix algebra, and rational residual certificates."""
import csv, json, math
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def determinant(A):
    a=[list(map(F,row)) for row in A]; n=len(a); d=F(1)
    for j in range(n):
        k=next(k for k in range(j,n) if a[k][j])
        if k!=j: a[j],a[k]=a[k],a[j]; d=-d
        p=a[j][j]; d*=p
        for k in range(j+1,n):
            t=a[k][j]/p
            for l in range(j,n): a[k][l]-=t*a[j][l]
    return d
def solve(A,b):
    a=[list(map(F,row))+[F(v)] for row,v in zip(A,b)]; n=len(a)
    for j in range(n):
        k=next(k for k in range(j,n) if a[k][j])
        a[j],a[k]=a[k],a[j]; p=a[j][j]
        a[j]=[v/p for v in a[j]]
        for k in range(n):
            if k==j: continue
            t=a[k][j]; a[k]=[x-t*y for x,y in zip(a[k],a[j])]
    return [row[-1] for row in a]
def frac(q,n): return F(q%n,n)
def integrate(j,k):
    breaks=sorted({F(0),F(1)}|{F(a,j) for a in range(1,j)}|{F(a,k) for a in range(1,k)})
    total=F(0)
    for a,b in zip(breaks,breaks[1:]):
        mid=(a+b)/2; A=(j*mid).__floor__(); B=(k*mid).__floor__()
        total+=F(j*k,3)*(b**3-a**3)-F(j*B+k*A,2)*(b*b-a*a)+A*B*(b-a)
    return total
def arithmetic(n):
    m=n; factors=[]; p=2
    while p*p<=m:
        if m%p==0:
            exponent=0
            while m%p==0: m//=p; exponent+=1
            factors.append((p,exponent))
        p+=1
    if m>1: factors.append((m,1))
    phi=n; jordan=n*n; mu=1
    for p,e in factors:
        phi=phi//p*(p-1); jordan=jordan//(p*p)*(p*p-1)
        mu=0 if e>=2 else -mu
    return phi,jordan,mu
def gram(j,k): return F(1,4)+F(math.gcd(j,k)**2,12*j*k)
for j in range(1,25):
    for k in range(1,25): assert integrate(j,k)==gram(j,k)
ordinary=[]
for M in range(1,19):
    data={n:arithmetic(n) for n in range(1,M+1)}
    S=sum((F(v[0]**2,v[1]) for v in data.values()),F(0))
    coefficients=[6*j*sum((F(data[k][0]*arithmetic(k//j)[2],data[k][1]) for k in range(j,M+1,j)),F(0))/(1+3*S) for j in range(1,M+1)]
    G=[[gram(j,k) for k in range(1,M+1)] for j in range(1,M+1)]
    independent=solve(G,[F(1,2)]*M)
    assert independent==coefficients
    residual=1-sum(coefficients)/2
    assert residual==1/(1+3*S)
    detC=math.prod(F(data[n][1],12*n*n) for n in range(1,M+1))
    assert determinant(G)==detC*(1+3*S)
    ordinary.append({'M':M,'squared_error':str(residual),'coefficients':list(map(str,coefficients))})
divisor_closed=[]
for top in range(1,41):
    indices=[n for n in range(1,top+1) if top%n==0]
    S=sum((F(arithmetic(n)[0]**2,arithmetic(n)[1]) for n in indices),F(0))
    G=[[gram(j,k) for k in indices] for j in indices]
    coefficients=solve(G,[F(1,2)]*len(indices))
    formula=[6*j*sum((F(arithmetic(k//j)[2]*arithmetic(k)[0],arithmetic(k)[1]) for k in indices if k%j==0),F(0))/(1+3*S) for j in indices]
    assert coefficients==formula
    assert 1-sum(coefficients)/2==1/(1+3*S)
    divisor_closed.append({'indices':indices,'squared_error':str(1/(1+3*S))})
reciprocal=[]
for M in range(2,25):
    V=[[frac(q,n) for n in range(2,M+1)] for q in range(1,M)]
    assert abs(determinant(V))==F(1,M)
    B=[[sum((frac(q,n)*frac(q,m)/q/(q+1) for q in range(1,M)),F(0)) for m in range(2,M+1)] for n in range(2,M+1)]
    assert determinant(B)==F(1,M*math.factorial(M)**2)
    reciprocal.append({'M':M,'determinant':str(determinant(B))})
def log_base(x,K=50):
    t=(x-1)/(x+1)
    lo=2*sum((t**(2*k+1)/(2*k+1) for k in range(K)),F(0))
    hi=lo+2*t**(2*K+1)/((2*K+1)*(1-t*t))
    return lo,hi
def log_interval(n):
    a=n.bit_length()-1; lo2,hi2=log_base(F(2)); lo,hi=log_base(F(n,2**a))
    return lo+a*lo2,hi+a*hi2
intervals=[]
for coefficients in ([F(1)],[F(1),F(-1,2)],[F(3,2),F(1,3),F(-2,5)]):
    M=len(coefficients)+1; Q=2000
    linear_lo=linear_hi=F(0)
    for n,c in enumerate(coefficients,2):
        lo,hi=log_interval(n); a=-2*c/n
        linear_lo+=a*(lo if a>=0 else hi)
        linear_hi+=a*(hi if a>=0 else lo)
    quadratic=sum((sum((c*frac(q,n) for n,c in enumerate(coefficients,2)),F(0))**2/q/(q+1) for q in range(1,Q+1)),F(0))
    lo=1+linear_lo+quadratic
    hi=1+linear_hi+quadratic+sum(map(abs,coefficients))**2/(Q+1)
    assert lo<hi
    # A separate floating check is diagnostic only; the rational series supplies the proof.
    ref=1-2*sum(float(c)*math.log(n)/n for n,c in enumerate(coefficients,2))+float(quadratic)
    assert float(lo)-1e-13<=ref<=float(hi)+1e-13
    intervals.append({'coefficients':list(map(str,coefficients)),'Q':Q,'lower_rational':str(lo),'upper_rational':str(hi),'decimal_for_orientation':[float(lo),float(hi)]})

# Plot data: finite exact rational errors and a clearly labeled finite prime product.
limit=100000; prime=bytearray(b'\x01')*(limit+1); prime[:2]=b'\x00\x00'
for p in range(2,math.isqrt(limit)+1):
    if prime[p]: prime[p*p:limit+1:p]=b'\x00'*len(prime[p*p:limit+1:p])
Cprime=math.prod(1-2/(p*(p+1)) for p in range(2,limit+1) if prime[p])
rows=[]; S=F(0)
for n in range(1,513):
    phi,J,mu=arithmetic(n); S+=F(phi*phi,J)
    if n<=10 or n%8==0:
        rows.append({'M':n,'error':float(1/(1+3*S)),'comparison':1/(3*Cprime*n)})
with (ROOT/'ordinary.csv').open('w',newline='',encoding='utf-8') as f:
    w=csv.DictWriter(f,fieldnames=['M','error','comparison']); w.writeheader(); w.writerows(rows)
result={'status':'passed','independent_piecewise_integrals':24**2,
 'ordinary_exact_normal_equations':ordinary,'divisor_closed_cases':divisor_closed,'reciprocal_determinants':reciprocal,
 'certified_residual_intervals':intervals,'prime_product_cutoff':limit,'finite_prime_product':Cprime,
 'scope':'Finite exact checks. They do not establish RH, asymptotic density of the reciprocal dictionary, Lean formalization, or research novelty.'}
(ROOT/'results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':'passed','integrals':24**2,'ordinary_cases':len(ordinary),'divisor_closed_cases':len(divisor_closed),'reciprocal_determinants':len(reciprocal),'residual_intervals':len(intervals),'finite_prime_product':Cprime}))
