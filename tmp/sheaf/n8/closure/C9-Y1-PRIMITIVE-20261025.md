# C9 y1 primitivity / kappa<=40 from Kondo structure: exact obstruction

Task: task-344. Owner: qside. Date: 2026-10-25.
Short natural-language theorem/proof and exact obstruction; no mixed/E3 data;
no Lean/Project/target edits; only this file written.

## 0. Verdict

Neither the primitivity of y1 nor kappa<=40 follows from the frozen Kondo /
H-fixed-line / trace-pairing / H_A-lite / y1=lambda y0 data.

Two separate gaps must not be conflated:

1. **Primitivity of y1** would mean v_pi(y1)=1 (or a unit p-coefficient in
   J=Z_p p+(J cap W)).  Kondo's y_i are only a Q_p-basis with y_i in J; no
   source theorem makes y1 primitive.
2. **Even if y1 is primitive**, kappa<=40 is not automatic.  With
   A=v_p(Tr y1)>=1, primitive y1 gives B=v_pi(y1)=1 and kappa=41A-1.  This is
   <=40 only when A=1.  A primitive y1 can have A>=2, and then kappa>=81.

A structurally consistent model has primitive y1=p^2+pi, A=2, kappa=81.  Thus
the proposed implication
    y1 primitive + trace/H_A-lite  =>  kappa<=40
is false even granting primitivity.

The exact missing source input is the actual y1/Tr(y1), equivalently both the
unit p-coefficient a in y1=a p+l and v_p(Tr y1).  B=I remains unproved; B=O_K
also unproved.  The b=3 B=I P6 corridor remains conditional.

No mixed/E3 data is used.

## 1. Data and the target inequality

p=12301, e=41, K=Q_p(pi), pi^41=p u, O_K=Z_p[pi], J=m=pi O_K,
I=p^{-1}J, W=ker Tr.

Kondo: y1,...,y41 Q_p-basis, y_i in J, W=span(y2,...,y41),
U=Q_p y1 Sp-fixed, Tr(y1)!=0.

    kappa := e v_p(Tr y1) - v_pi(y1),  e=41.                     (1.1)

Write J=Z_p p + L, L=J cap W=span(pi,...,pi^40),
y1=a p+l, a in Z_p, l in L, and

    A := v_p(Tr y1) = v_p(a)+1 >= 1,
    B := v_pi(y1) <= 41A,
    kappa = 41A-B >= 0.                                          (1.2)

The desired upper bound is equivalent to

    B >= 41A - 40.                                               (1.3)

For primitive y1, B=1, so (1.3) becomes
    1 >= 41A-40  <=>  A<=1  <=>  A=1.                            (1.4)

Thus primitivity alone is insufficient unless one also proves A=1.

## 2. What the Kondo structure gives

### 2.1 Only a Q_p-basis

Kondo gives y_i as a Q_p-basis of K with y_i in J.  It does not give:
- a Z_p-basis of J or O_K;
- primitivity of y1 in J;
- the unit p-coefficient a;
- v_pi(y1) or v_p(Tr y1).

A Q_p-basis vector can be multiplied by a p-power and remain in J; the source
does not normalize that scalar.

### 2.2 Fixed line U

H=Phi^{-1}(Sp_40(Z_p)) acts as diag(1,A) on K=U direct-sum W;
alpha_+(y1)=y1 for every alpha in H.  This fixes the line representative y1
pointwise, but not its p-adic normalization: replacing y1 by c y1 preserves U,
the fixed-line property, and kappa.  No source fixes c to a unit.

### 2.3 H_A-lite and diag(1,-1)

H_A-lite (conditional on the Kondo/AbsTopIII interface) gives
alpha_+(J)=J and alpha_+(I)=I.

If diag(1,-1) in H preserves J, then J=(J cap U) direct-sum (J cap W) as
Z_p-lattices (2 is a p-adic unit).  This is a splitting constraint, but it
only says that the U-coordinate lattice is a principal Z_p-lattice Z_p c y1.
It does not force c to be a unit, and it does not constrain v_p(Tr y1).
Granting the full Sp-stability of J cap W adds a standard-lattice condition
on W, not a normalization of y1's p-coefficient.

### 2.4 Trace pairing and y1=lambda y0

W=ker Tr gives Tr(y1) in pZ_p, hence A>=1.  The Kondo Sp-form is alternating;
the trace form is symmetric; the source does not identify them or prove that
alpha_+ is a trace isometry.  The single trace Tr(a(alpha))=41 does not
distinguish y1.

The JW-F relation y1=lambda y0 gives only kappa(y1)=kappa(y0).  It does not
give lambda's p-adic valuation or the value of kappa.

### 2.5 H_A-full

H_A-full would imply alpha_+(O_K)=O_K for every actual alpha and hence B=O_K
(task-202/225).  In that case B=I is false.  H_A-full cannot be used to prove
B=I, and H_A-full itself is not an actual source theorem (task-196/204/208).
Thus the branch cannot be decided by imposing H_A-full; only H_A-lite is
available, and it does not normalize y1.

## 3. Primitivity does not imply kappa<=40

The following model satisfies primitive y1, J-splitting, fixed line, trace
kernel, and y1=lambda y0:

    y1 := p^2 + pi,   y0 := y1,   lambda=1,
    W := ker Tr = span_Zp(pi,...,pi^40),
    J := Z_p y1 direct-sum (J cap W)   (y1 is a uniformizer).
    (3.1)

Then:

    v_pi(y1)=1 (primitive in J),
    Tr(y1)=Tr(p^2)+Tr(pi)=41p^2+0=41p^2,
    A=v_p(Tr y1)=2,
    kappa=41*2-1=81 >= 41.                                      (3.2)

So even the strongest possible statement "y1 is primitive" is compatible with
kappa=81.  The missing condition is A=1 (equivalently Tr(y1) has exactly one
p-adic unit factor), not primitivity of y1.

Model E (y1=p+pi) gives v_pi=1, A=1, kappa=40/B=I; Model A (y1=p) gives
v_pi=41, A=1, kappa=0/B=O_K.  All three are structurally consistent with the
recorded fixed-line/lattice constraints.  These are abstract consistency
models, not actual Kondo F(x_i) tuples; actual F(x0), y0, n, lambda, y1,
Tr(y1) are missing.

## 4. Exact obstruction

The frozen source does not determine:

(i) the unit p-coefficient a of y1 (primitivity);
(ii) v_p(Tr y1)=A;
(iii) the equality A=1 under primitive y1;
(iv) kappa in [1,40] and hence B=I;
(v) B=O_K as an actual branch.

The exact missing input is the actual Kondo data
    F(x0), y0, n, lambda, y1, Tr(y1),
or equivalently the integral primitive normalization of the Sp-fixed line U
and the trace valuation A.

A proof of B=I would need both:
- y1 primitive (B=1), and
- v_p(Tr y1)=1 (A=1),
so that kappa=40; or 2<=... for kappa between1 and40 with suitable B/A.
No source theorem supplies either.  A proof of B=O_K would need kappa<=0 or
H_A-full; H_A-full is open, and kappa<=0 is not determined.

## 5. Consequences

- B=I is not proved.
- B=O_K is not proved.
- kappa<=40 is not proved; primitivity alone would not suffice.
- The b=3 B=I P6 corridor remains conditional on kappa in [1,40] and on the
  missing arch lower bound.
- No mixed/E3 profile is used.

## 6. Classification

PROVED:
- J=Z_p p+(J cap W), y1=a p+l, A=v_p(a)+1>=1, B<=41A, kappa>=0;
- primitivity B=1 makes the desired upper equivalent to A<=1;
- H fixed line fixes y1 but not its p-scalar;
- H_A-lite + diag(1,-1) gives J splitting (conditional), not y1 primitivity;
- Model (3.1) has primitive y1 and kappa=81, so primitivity alone does not
  imply kappa<=40;
- H_A-full => B=O_K, not B=I.

MISSING:
- actual Kondo F(x0), y1, Tr(y1), p-coefficient;
- source proof y1 primitive and A=1 (or the corresponding kappa range);
- actual B=I/B=O_K, actual h_inf, complete C/P6.

WITHDRAWN:
- primitive y1 => kappa<=40;
- H_A-lite/fixed-line/trace/y1=lambda y0 => y1 primitive or kappa<=40;
- H_A-full as a route to B=I;
- any mixed/E3 input.

## 7. Conclusion

The Kondo structure, H-fixed line, trace pairing, H_A-lite splitting, and
y1=lambda y0 do not prove y1 primitive or kappa<=40.  The exact obstruction is
two-fold: actual y1/Tr(y1) is not computed (so primitivity/A are unknown), and
even primitivity would only reduce kappa<=40 to A<=1, which is not implied by
the recorded structure.  The model y1=p^2+pi (primitive, A=2, kappa=81)
demonstrates the gap.  B=I and B=O_K remain undecided; the b=3 B=I P6 corridor
remains conditional.

target_accepted=false; P6 open.

## 8. Sources

- C9-KAPPA-TRACE-20261025.md (task-328): kappa>=0; Model D kappa=81;
  J split and A/B formulae.
- C9-BRANCH-BI-SOURCE-20261025.md (task-335): H fixed line/H_A-lite analysis;
  H_A-full => B=O_K.
- C9-KAPPA-JW-ALL-20261025.md (task-282): y1=lambda y0, kappa invariance.
- C9-KAPPA-ACTUAL-20261025.md (task-269): conditional kappa-B theorem;
  source obstruction.
- C9-AUDIT-HAFULL-LITE-20261025.md / C9-ADJUDICATE-HAFULL-20261025.md:
  H_A-lite conditional, H_A-full open.
- Kondo 2025/2026 snapshots: H=Phi^{-1}(Sp), fixed line U, trace kernel
  W=ker Tr, y_i Q_p-basis in J.
