# C9 branch B=I from Kondo H fixed line / H_A: proof attempt and exact obstruction

Task: task-335. Owner: qside. Date: 2026-10-25.
Short natural-language theorem/proof and exact obstruction; no mixed/E3 data;
no Lean/Project/target edits; only this file written.

## 0. Verdict

Neither B=I nor B=O_K is proved from the frozen source.

The Kondo fixed line and H_A data give real constraints, but not the missing
upper kappa<=40:

- H=Phi^{-1}(Sp) fixes the line U=<y1>; consequently alpha_+(y1)=y1 for every
  alpha in H.
- H_A-lite (alpha_+(J)=J, alpha_+(I)=I) and diag(1,-1) in H force a
  Z_p-splitting J=(J cap U) direct-sum (J cap W) when the full H-action is
  assumed.  This says the lattice J is compatible with the fixed line, but it
  does **not** make y1 primitive in J and does not bound v_pi(y1).
- The trace pairing W=ker Tr gives Tr(y1) in pZ_p, hence only
  v_p(Tr(y1))>=1; it gives no upper bound.
- y1=lambda y0 (JW-F) gives only kappa(y1)=kappa(y0), not the value.
- H_A-full (alpha_+(O_K)=O_K) would imply B=O_K, hence B=I is impossible
  under it.  It cannot be used to prove B=I, and H_A-full itself is not an
  actual source theorem.

The exact missing input is the actual y1/Tr(y1), equivalently the p-coefficient
of y1 in J=Z_p p+(J cap W) (a primitive integral normalization of the fixed
line).  A structurally consistent model with kappa=81 shows that H_A-lite +
fixed line + trace pairing + y1=lambda y0 do not imply kappa<=40.

No actual branch is selected; no mixed data is used.

## 1. Setup and conditional kappa-B theorem

p=12301, e=41, K=Q_p(pi), pi^41=p u, O_K=Z_p[pi], J=m=pi O_K,
I=p^{-1}J, W=ker Tr.

Kondo: y1,...,y41 Q_p-basis, y_i in J, W=span(y2,...,y41),
U=Q_p y1 is the Sp-fixed line, Tr(y1)!=0.  Write

    kappa := e v_p(Tr y1) - v_pi(y1).                           (1.1)

The conditional source theorem (task-250/269):

    kappa <= 0       => H_A-full and B=O_K;
    1 <= kappa <= 40 => B=I;
    kappa >= 41      => B not well-posed inside I.              (1.2)

Task-328 proved kappa>=0 from J integrality and trace:
J=Z_p p+(J cap W), y1=a p+l, Tr(y1)=41ap, A=v_p(Tr y1)=v_p(a)+1>=1,
B=v_pi(y1)<=41A, hence kappa=41A-B>=0.

Thus the missing part is exactly the upper bound kappa<=40.  B=I is equivalent
to 1<=kappa<=40; B=O_K corresponds to kappa<=0 (with H_A-full in the strong
case).

## 2. What H fixed line and H_A-lite add

### 2.1 Fixed line

H=Phi^{-1}(Sp_40(Z_p)) is represented as diag(1,A) on K=U direct-sum W.
For every alpha in H, alpha_+(y1)=y1.  This fixes the line U pointwise on the
representative y1, but it does not normalize y1 among scalars: replacing y1 by
c y1 changes the line representative and leaves kappa unchanged.  In
particular H fixing the line does not fix the p-coefficient a in
y1=a p+l.

### 2.2 H_A-lite and diag(1,-1)

H_A-lite gives alpha_+(J)=J and alpha_+(I)=I for the actual H-action
(conditional on the Kondo/AbsTopIII interface).

Take A=-I in Sp_40(Z_p), an actual element of H.  If J is invariant under
diag(1,-1), then for j=j_U+j_W in J also j_U-j_W in J; since 2 is a p-adic
unit, both j_U and j_W lie in J.  Hence

    J = (J cap U) direct-sum (J cap W).                         (2.1)

This is a real lattice constraint.  It implies the U-part of J is a principal
Z_p-lattice Z_p c y1, but c may be any p-power; it does not force c to be a
unit, i.e. y1 need not be primitive in J.  Therefore (2.1) does not bound
v_pi(y1) above or below in terms of v_p(Tr y1).

For all A in Sp_40, J cap W must be Sp-stable.  This is an additional lattice
normalization (a standard-lattice statement), not a computation of y1's
p-coefficient.  Even granting it, the U-line representative remains free up to
p-adic scalar.

### 2.3 Trace pairing

W=ker Tr and y1 in J give Tr(y1) in pZ_p, so A=v_p(Tr y1)>=1.  The trace
pairing is symmetric, while the Kondo Sp-form is alternating; the source does
not identify them or prove that alpha_+ is a beta-isometry.  The trace of
a(alpha) is Tr(1)=41 for every A, so the single trace value does not
distinguish kappa or B.  Higher beta-pairings with I are not computed.

Thus trace pairing + H_A-lite + fixed line do not imply kappa<=40.

## 3. H_A-full cannot prove B=I

H_A-full means alpha_+(O_K)=O_K for every actual alpha.  By task-202/225:

    H_A-full => l=O_K/J fixed => B=O_K.                          (3.1)

Hence if H_A-full were actual, B=I is false (B=O_K instead).  A proof of B=I
must therefore use only H_A-lite/partial integrality, not H_A-full.

H_A-full itself is not an actual source theorem:
- task-204 gave only a conditional implication (P)=>H_A-full;
- task-208 showed the full-Out filtration/integrality premise used for one
  route fails;
- task-196/203 audited H_A-lite as conditional and H_A-full as open.

So there is no branch proof in either direction from H_A-full:
H_A-full would give B=O_K, but is missing; without it, B=I is not forced.

## 4. Structural obstruction to kappa<=40

Even with fixed line, trace kernel, y1=lambda y0, and J-splitting/integrality,
kappa can exceed 40.  Consider the lattice model

    y1 := p^2 + pi,    y0 := y1,    lambda=1,
    W = ker Tr = span_Zp(pi,...,pi^40),
    J = Z_p y1 direct-sum (J cap W)  (y1 is a uniformizer).       (4.1)

Then

    v_pi(y1)=1,
    Tr(y1)=Tr(p^2)+Tr(pi)=41p^2+0=41p^2,
    A=v_p(Tr(y1))=2,
    kappa=41*2-1=81 >= 41.                                     (4.2)

The model satisfies:

- y1 in J, Tr(y1)!=0, W=ker Tr, U=Q_p y1 fixed by diag(1,Sp);
- J splitting (2.1) and J/I preservation of H_A-lite;
- y1=lambda y0 with the JW-F relation (suitable n,t,s);
- integrality y_i in J and Tr(y1) in pZ_p.

It is an abstract coordinate model, not an actual Kondo F(x_i) tuple; its role
is to show that the recorded fixed-line/H_A-lite/trace/y1=lambda y0 data do not
imply kappa<=40.  It is not claimed as an actual source counterexample.

The exact missing source input is the actual F(x0), y0, n, lambda, y1, and
Tr(y1), equivalently a primitive integral normalization of y1 (the unit
p-coefficient a in J=Z_p p+(J cap W)).

## 5. Classification

PROVED:
- kappa integer invariant; kappa(y1)=kappa(y0);
- kappa>=0 from J integrality/trace;
- conditional kappa-B theorem (1.2);
- H fixes U: alpha_+(y1)=y1;
- H_A-lite + diag(1,-1) => J=(J cap U) direct-sum (J cap W), conditional;
- trace gives only v_p(Tr y1)>=1;
- H_A-full => B=O_K (so not usable for B=I);
- Model (4.1) has kappa=81 and satisfies the structural fixed-line/lattice
  constraints (abstract model, not actual source).

CONDITIONAL/MISSING:
- actual H_A-lite full-Out validity;
- actual Kondo F(x_i), y1, Tr(y1), p-coefficient a;
- source proof kappa<=40 or 1<=kappa<=40;
- actual B=I or B=O_K branch;
- complete C/target/P6.

WITHDRAWN/INVALID:
- "H_A-full proves B=I" (it proves B=O_K conditionally);
- deriving kappa<=40 solely from fixed line + trace + H_A-lite;
- treating Model (4.1) as an actual source counterexample;
- any mixed/E3 profile input.

## 6. Conclusion

The Kondo H fixed line and H_A data do not yield the missing kappa upper bound.
They give a lattice splitting and fixed U-line, but the p-coefficient a of y1
is not normalized; a structural model with kappa=81 satisfies the recorded
constraints.  H_A-full, if it held, would give B=O_K and exclude B=I; it is not
actual.  Therefore:

- B=I is not proved;
- B=O_K is not proved;
- the exact missing source input is the actual y1/Tr(y1) (primitive integral
  normalization), not another group-action theorem.

The b=3 B=I P6 corridor therefore remains conditional on the unproved
kappa in [1,40] and on the missing arch lower bound.  No mixed/E3 data is used.
target_accepted=false; P6 open.

## 7. Sources

- C9-KAPPA-TRACE-20261025.md (task-328): kappa>=0; Model D kappa=81;
  exact obstruction to kappa<=40.
- C9-NEW-BI-SOURCE-20261025.md (task-250): kappa-B dichotomy; H-orbit.
- C9-KAPPA-ACTUAL-20261025.md (task-269): actual kappa source obstruction;
  models A/B.
- C9-AUDIT-HAFULL-LITE-20261025.md / C9-ADJUDICATE-HAFULL-20261025.md:
  H_A-lite conditional, H_A-full open; H_A-full => B=O_K.
- C9-AUDIT-HAFULL-INTEGRALITY-20261025.md: conditional (P)=>H_A-full;
  full-Out filtration premise audited/not actual.
- Kondo 2025/2026 snapshots: H=Phi^{-1}(Sp), fixed line U, trace kernel
  W=ker Tr, y_i in J.
