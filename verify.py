"""Exact replay of the candidate criterion and recorded counterexamples.

These finite calculations are diagnostic checks, not the uniform proof.
"""
import argparse
from fractions import Fraction as F
from random import Random
from probe import linearization, first_negative

def qint(n, q):
    return sum((q**j for j in range(n)), F(0))

def coefficients(N, q, r):
    d = [qint(i,q)/qint(N,q) for i in range(N+1)]
    return [1-x for x in d], [(1-r)*x for x in d], [r*x for x in d]

def poly_add(a, b):
    return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0))
            for i in range(max(len(a),len(b)))]

def poly_scale(a, x):
    return [v*x for v in a]

def poly_mul(a, b):
    out = [F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j] += x*y
    return out

def quotient_products(a,b,c):
    """Compute polynomial products modulo the terminal polynomial directly."""
    N=len(a)-1
    polys=[[F(1)]]
    previous=[F(0)]
    for i in range(N):
        next_poly=poly_add([F(0)]+polys[-1],poly_scale(polys[-1],-b[i]))
        next_poly=poly_add(next_poly,poly_scale(previous,-c[i]))
        next_poly=poly_scale(next_poly,1/a[i])
        previous=polys[-1]
        polys.append(next_poly)
    terminal=poly_add([F(0)]+polys[-1],poly_scale(polys[-1],-b[N]))
    terminal=poly_add(terminal,poly_scale(polys[-2],-c[N]))
    terminal=poly_scale(terminal,1/terminal[-1])
    out=[]
    for m in range(N+1):
        plane=[]
        for n in range(N+1):
            product=poly_mul(polys[m],polys[n])
            for i in range(len(product)-1,N,-1):
                leading=product[i]
                for j,x in enumerate(terminal):
                    product[i-N-1+j] -= leading*x
            product=(product+[F(0)]*(N+1))[:N+1]
            row=[F(0)]*(N+1)
            for k in range(N,-1,-1):
                row[k]=product[k]/polys[k][-1]
                for j,x in enumerate(polys[k]):
                    product[j] -= row[k]*x
            assert all(x==0 for x in product)
            plane.append(row)
        out.append(plane)
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=7)
    parser.add_argument('--perturbations',type=int,default=3,
                        help='rational perturbations per size and asymmetric reference')
    args=parser.parse_args()
    count=0
    for N in range(1,args.max_n+1):
        for q in [F(1),F(11,10),F(3,2),F(2)]:
            for r in [F(1),F(9,10),F(1,2),F(1,10)]:
                a,b,c=coefficients(N,q,r)
                matrices=linearization(a,b,c)
                direct=quotient_products(a,b,c)
                assert matrices==direct,(N,q,r,'quotient mismatch')
                assert first_negative(matrices) is None,(N,q,r,'negative')
                for m in range(N+1):
                    for n in range(N+1):
                        assert sum(matrices[m][n])==1
                        assert matrices[m][n]==matrices[n][m]
                count+=1
        print(f'N={N}: matrix and quotient products agree; cumulative systems={count}',flush=True)
    examples=[([F(0),F(25,132),F(59,132),F(95,132),F(1)],F(-1598,289007)),
              ([F(0),F(30,121),F(60,121),F(90,121),F(1)],F(-809,172081))]
    for d, expected in examples:
        products=quotient_products([1-x for x in d],[F(0)]*5,d)
        assert products[4][4][4]==expected
        print(f'Convex-profile diagnostic: g(4,4;4)={expected}',flush=True)
    rng=Random(117)
    perturbed_count=0
    for N in range(1,args.max_n+1):
        for r in [F(1,10),F(1,2),F(9,10)]:
            s=min(r,1-r)
            eta=F(1,2)*(s/(32*N))**N
            margin=F(1,2)*(s/4)**N
            for sample in range(args.perturbations):
                a,b,c=coefficients(N,F(1),r)
                for i in range(1,N):
                    da=F(rng.randint(-2,2),4)*eta
                    db=F(rng.randint(-2,2),4)*eta
                    a[i]+=da
                    b[i]+=db
                    c[i]-=da+db
                db=F(rng.randint(-2,2),4)*eta
                b[N]+=db
                c[N]-=db
                assert all(x>=0 for row in [a,b,c] for x in row)
                matrices=linearization(a,b,c)
                assert matrices==quotient_products(a,b,c)
                for m in range(N+1):
                    for n in range(N+1):
                        for k in range(N+1):
                            if abs(m-n)<=k<=min(m+n,N):
                                assert matrices[m][n][k]>=margin,(N,r,sample,m,n,k)
                            else:
                                assert matrices[m][n][k]==0
                perturbed_count+=1
        print(f'N={N}: perturbed lower margin replayed; cumulative systems={perturbed_count}',flush=True)
    print(f'Exact diagnostic replay ended: {count} geometric systems, {perturbed_count} perturbed systems; two counterexamples reproduced.',flush=True)

if __name__=='__main__':
    main()
