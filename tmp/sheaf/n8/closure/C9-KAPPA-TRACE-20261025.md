# C9 kappa branch via y1=lambda y0, trace pairing, and integrality

Task: task-328. Owner: qside. Date: 2026-10-25.
Short natural-language theorem/proof and exact obstruction; no Lean/Project
edits; no arbitrary actual y1 or mixed/E3 profile; only this file written.

## 0. Verdict

Using the JW-F relation y1=lambda y0 (task-282), the trace-kernel W=ker Tr,
the J/O integrality of Kondo's y-basis, and the Sp-fixed line U=<y1>, one gets
a genuine **lower half**

    kappa := e v_p(Tr y1) - v_pi(y1) >= 0,                     (0.1)

but **not** the range kappa<=40.  The integrality and trace data alone do not
exclude kappa>=41.  A structurally consistent model with all recorded data
has kappa=81, so kappa in [0,40] is not a source theorem.

The exact obstruction is a primitivity/p-adic normalization of y1 (equivalently
the p-coefficient of y1 in J=Z_p p + (J cap W)); no source theorem fixes it.
The JW-F relation y1=lambda y0 only gives kappa(y1)=kappa(y0), not the value.

No actual kappa is computed; B=I and B=O_K remain unproved.  No mixed/E3 data
is used.

## 1. Data and notation

K=Q_p(pi), p=12301, e=41, pi^41=p u, u in Z_p^times,
O_K=Z_p[pi], J=m=pi O_K, I=p^{-1}J, W=ker Tr.

Kondo: y1,...,y_e is a Q_p-basis of K, y_i in J,
W=Q_p-span(y2,...,y_e), Tr(y1)!=0, U=Q_p y1 is the Sp-fixed line.

JW-F (task-282): with y0=F(x0), y1=lambda y0,
lambda=(1-tn)/p^s in Q_p^times, and

    kappa(y1)=kappa(y0)                                         (1.1)

for kappa(y)=e v_p(Tr y)-v_pi(y).  The scaling invariance uses
v_pi(p)=e=41.

## 2. Lower bound kappa>=0

### 2.1 Lattice decomposition

Because Tr: K -> Q_p is nonzero and W=ker Tr, and Tr(p)=41p!=0, one has a
Z_p-module decomposition

    J = Z_p p  +  L,   L := J cap W.                            (2.1)

Indeed for y in J, Tr(y) in pZ_p (integrality of the trace on pi O_K gives
Tr(J) subset pZ_p); set a=Tr(y)/(41p) in Z_p and l=y-a p; then Tr(l)=0 and
l in J.  Moreover L subset pi O_K and, for nonzero l in L,
v_pi(l)<=40: if v_pi(l)>=41 then l in pi^41 O_K=pO_K, but the trace-kernel
elements of J have their pi-coordinates supported in degrees 1,...,40
(the standard tame basis; equivalently W=span(pi,...,pi^40) in the coordinate
model).

### 2.2 Trace and valuation

Write y1=a p + l, a in Z_p, l in L.  Since Tr(l)=0,

    Tr(y1)=41 a p,
    A := v_p(Tr(y1)) = v_p(a)+1 >= 1,
    a != 0.                                                     (2.2)

Let B:=v_pi(y1)=v_pi(a p+l).  Since v_pi(a p)=41+v_p(a) and, if l!=0,
v_pi(l)<=40, one has
    B <= max(41+A, 40) = 41 A     (A>=1).                      (2.3)
(If l=0, B=41+A=41A; if l!=0, B<=40<41A for A>=1 except A=1 where
B<=40<41.)  Therefore

    kappa = 41 A - B >= 41 A - 41 A = 0.                        (2.4)

This is the new genuine lower half, independent of y1=lambda y0.

### 2.3 What y1=lambda y0 adds

The JW-F relation only gives kappa(y1)=kappa(y0); it does not give A or B.
Since y0=F(x0) is not computed by Kondo/JW data, the relation does not add an
upper bound.  The Sp-fixed line U fixes y1 only up to a nonzero scalar; any
scalar multiple has the same line and the same kappa, so it does not normalize
the p-coefficient a of y1.

## 3. Exact obstruction to kappa<=40

The upper bound kappa<=40 is equivalent to

    B >= 41 A - 40.                                             (3.1)

No source theorem gives (3.1).  The recorded structural data admit a model with
kappa>=41:

Model D.  Take y1 := p^2 + pi (integrally in J), y0:=y1 (lambda=1),
and y2,...,y41 a Q_p-basis of W=span(pi,...,pi^40).  Then:

    v_pi(y1)=1  (pi term; p^2 has valuation 82),
    Tr(y1)=Tr(p^2)+Tr(pi)=41 p^2 + 0 = 41 p^2,
    v_p(Tr(y1))=2,
    kappa=41*2-1=81 >= 41.                                     (3.2)

The model satisfies:

- y1 in J, Tr(y1)!=0, W=ker Tr, and y1,...,y41 is a Q_p-basis;
- U=Q_p y1 is Sp-fixed (Sp acts on W only, as in Kondo diag(1,Sp));
- y1=lambda y0 with lambda=1; the JW-F relation (1.1) is satisfied with
  suitable n,t,s (e.g. 1-tn=p^s);
- J=Z_p y1 + (J cap W) because y1 is a uniformizer (its pi-unit part is
  1+pi^81, a unit), so the integrality/sp-stability axioms hold;
- Tr(J) subset pZ_p and all integrality conditions hold.

This is an abstract coordinate model, not an actual Kondo F(x_i) tuple (the
frozen source does not give actual F-values).  Its role is exactly to show
that the recorded structural data + trace pairing + y1=lambda y0 do not imply
kappa<=40.  It is not claimed as an actual source counterexample.

Thus the full range [0,40] is **not derived**; the exact missing input is a
source normalization fixing the p-coefficient a of y1 (equiv. vp(a)) or the
primitivity of y1 in J/pJ along the p-direction.  Kondo gives only a Q_p-basis,
not an integral primitive basis; the trace pairing W=ker Tr and Sp-fixed line
do not fix a.

## 4. Conditional kappa-B theorem (unchanged)

If the actual kappa were known:

    kappa <= 0       => H_A-full and B=O_K;
    1 <= kappa <= 40 => B=I;
    kappa >= 41      => branch B not well-posed inside I.        (4.1)

The new lower bound kappa>=0 removes only the negative kappa side structurally:
the possible actual ranges remaining are kappa=0 (B=O_K boundary) or
kappa>=1; but without an upper bound, kappa>=41 is structurally allowed, so
B=I is not proven.  Model B (y1=p+pi) gives kappa=40/B=I; Model A (y1=p)
gives kappa=0/B=O_K; Model D gives kappa=81/ill-posed.  All are consistent
with the recorded trace/integrality data.

## 5. Classification

PROVED:
- kappa integer and invariant under y1=lambda y0;
- kappa(y1)=kappa(y0);
- J=Z_p p + (J cap W), Tr(y1)=41ap, A=v_p(a)+1>=1;
- B<=41A and hence kappa>=0 from integrality+trace;
- Model D kappa=81 is structurally consistent (kappa<=40 not a consequence).

CONDITIONAL/MISSING:
- actual Kondo F(x0), y0, n, lambda, y1;
- actual a=v_p coefficient of y1, equivalently kappa;
- source primitivity normalization of y1;
- actual B=I/B=O_K branch; kappa does not fix P6 sign.

WITHDRAWN:
- deriving kappa in [0,40] from y1=lambda y0 + trace W=kerTr + J/O
  integrality + Sp-fixed line;
- using the full-basis anti-diagonal Gram (false; y1 radical; task-259);
- treating Model D as an actual source counterexample (it is a structural
  consistency model only).

## 6. Conclusion

The independent kappa-trace attack improves the structural lower side:
kappa>=0 follows from J integrality and Tr(J) subset pZ_p.  It does not prove
kappa<=40.  y1=lambda y0 only transports kappa; the Sp-fixed line and trace
kernel do not fix the p-coefficient of y1, and a structurally consistent model
has kappa=81.  The exact missing source input is the actual y1/Tr(y1) or a
primitive integral normalization of the Sp-fixed line.  B=I and B=O_K remain
unproved; kappa decides only the branch, not P6.

No arbitrary actual y1 or mixed/E3 profile was introduced.
target_accepted=false; P6 open.

## 7. Sources

- C9-KAPPA-JW-ALL-20261025.md (task-282): y1=lambda y0, kappa invariance,
  F(tau)=0.
- C9-KAPPA-ACTUAL-20261025.md (task-269): conditional kappa-B theorem and
  source obstruction.
- C9-GRAM-AUDIT-20261025.md (task-259): full anti-diagonal Gram false;
  restricted W-Gram unproved; exact G1-G3 obstruction.
- C9-Y1-TRACE-20261025.md (task-217): models A/B/C; missing y1,Tr,c,C.
- Kondo 2025/2026 snapshots: trace kernel W=ker Tr, y_i Q_p-basis, Sp-fixed
  line, JW relations.
