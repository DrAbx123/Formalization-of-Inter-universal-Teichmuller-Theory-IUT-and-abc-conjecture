# C9 trace-dual F basis and canonical integral model

Task: task-238. Date: 2026-10-25. Author: transport.
Stage: new-math exploration; explicit construction/scenario only. No Lean/Project
edits. Only this file written. target_accepted=false.

## 0. Purpose and labels

This file explores whether a trace-dual basis for

    beta(x,y) = Tr_{K/Q_p}(xy)

can produce actual Kondo-type y_i=F(x_i), a canonical integral model, and the
outcome H_A-full/B=O_K.

The result is mixed and is labelled throughout:

- SECTION 2 is a CONSTRUCTED SCENARIO S_A with explicit y_i in J. It satisfies
  the recorded structural axioms, Theorem-E trace kernel, and gives
  H_A-full true/B=O_K. It is not a proof that these y_i equal Kondo F(x_i).
- SECTION 3 computes the exact beta-Gram matrices and beta-dual bases. It
  proves that the beta-dual of O_K is I and the beta-dual of J is p^{-1}I;
  these dual bases do not lie in J, so they cannot directly serve as Kondo
  y_i.
- SECTION 4 proves a unit/log realization of the scenario, and states the
  exact unproved point in interpreting it as Kondo F(x_i).
- SECTION 5 explains why trace duality cannot by itself resolve the H_A/B
  underdetermination.

No actual F(x_i) values are assumed. No U/B branch is selected as source
truth.

## 1. Local setup

Let p=12301, e=41, K=Q_p(pi) with pi^e=p u, u in Z_p^times, f=1,
O_K=Z_p[pi], m=(pi), J=m, I=p^{-1}J=pi^{1-e}O_K, W=ker Tr. Then

    Tr(1)=e=41,  Tr(pi^a)=0 for 1<=a<=e-1=40,
    Tr(p)=Tr(pi^e/u)=e p/u? Wait p=pi^e/u, so Tr(p)=e p/u.

Actually p is rational, so Tr(p)=e p=41p.  (Use p=pi^e/u; Tr(pi^e)=Tr(pu)=p Tr(u)=e p u; divide by u gives e p.)

    O_K=Z_p 1 direct-sum (J cap W),
    J cap W=Z_p-span(pi,...,pi^40),
    J=Z_p-span(p,pi,...,pi^40).                              (1.1)

## 2. Constructed scenario S_A

Define

    y_1=p,   y_i=pi^{i-1} for 2<=i<=41.                     (2.1)

### 2.1 Structural checks

- y_1,...,y_41 is a Z_p-basis of J, hence a Q_p-basis of K.
- y_i in J for all i.
- W=ker Tr=Q_p-span(pi,...,pi^40)=Q_p-span(y_2,...,y_41).
- Tr(y_1)=Tr(p)=41p in p Z_p and nonzero.
- J=Z_p-span(y_1,...,y_41).
- U:=Q_p y_1=Q_p 1; K=U direct-sum W.

Thus (R1) of the Kondo structural data is satisfied.

### 2.2 Decomposition of 1

Write 1=u_0+w_0, u_0 in U, w_0 in W:

    u_0=1,  w_0=0,  c=1/p,  u_0=c y_1.                     (2.2)

Indeed c=41/Tr(y_1)=41/(41p)=1/p.

### 2.3 H action and H_A-full

Let H act by diag(1,A) on K=U direct-sum W in the y-basis, A in Sp_40(Z_p).
For alpha=alpha_A,

    a(alpha)=alpha_+(1)=u_0+A w_0=1.                       (2.3)

Hence a(alpha) in O_K minus J for every A, and

    alpha_+(O_K)=Z_p a+J=Z_p 1+J=O_K.                      (2.4)

Therefore H_A-full holds and

    B=closed Z_p-span union_alpha alpha_+(O_K)=O_K.          (2.5)

Theorem 2.1 (scenario S_A). The explicit y-basis (2.1) satisfies the recorded
structural axioms, the trace-kernel Theorem-E condition W=ker Tr, the
diag(1,A) Sp-action, H_A-full, and B=O_K.

Proof. All points are direct from (1.1)-(2.3); (2.4) uses O_K=Zp1+J. QED.

Label: this is a CONSTRUCTED NORMALIZATION/SCENARIO. It proves that a
trace-compatible y-basis giving B=O_K exists. It does not prove that (2.1)
equals Kondo F(x_i) for the given JW generators.

## 3. Exact beta-Gram and trace-dual bases

### 3.1 Standard O_K basis

Let e_a=pi^a, 0<=a<=40. For 0<=a,b<=40,

    beta(e_a,e_b)=Tr(pi^{a+b}).

Since 0<=a+b<=80, this is nonzero only when

    a+b=0:  beta=Tr(1)=41,
    a+b=41: beta=Tr(pi^41)=Tr(pu)=41 p u,
    otherwise 0.

Thus the Gram matrix H of the standard O_K basis is sparse: one entry 41 at
(0,0), and the anti-diagonal a+b=41 equal to 41pu.

The beta-dual basis f_a is:

    f_0=1/41,
    f_a=pi^{-a}/41  (1<=a<=40).                             (3.1)

Indeed beta(e_a,f_b)=Tr(pi^{a-b}/41), which is 1 if a=b and 0 otherwise
(the exponent lies in [-40,40], and only exponent 0 has nonzero trace).

Since f_0,...,f_40 is a Z_p-basis of

    I=pi^{1-e}O_K=pi^{-40}O_K,

we have proved:

Theorem 3.1 (trace-dual of O_K). The beta-dual lattice of O_K is

    O_K^vee = I = pi^{-40}O_K,                              (3.2)

with dual basis f_a=pi^{-a}/41. This is a canonical integral model of I, but
f_a not in J for a>=1; in particular f_1,...,f_40 are not Kondo y_i in J.

### 3.2 Naive y-basis Gram

For y_1=p, y_i=pi^{i-1} (2<=i<=41):

    beta(y_1,y_1)=Tr(p^2)=41 p^2,
    beta(y_1,y_i)=Tr(p pi^{i-1})=0  (2<=i<=41),
    beta(y_i,y_j)=Tr(pi^{i+j-2})
      =41 p u  if i+j=43 (2<=i,j<=41),
      =0 otherwise.                                          (3.3)

The Gram matrix G of y is therefore

    G_{11}=41p^2,
    G_{1i}=G_{i1}=0 for i>=2,
    G_{ij}=41pu if i+j=43,
    G_{ij}=0 otherwise.                                     (3.4)

### 3.3 Beta-dual of the naive y-basis

Solve beta(y_i,g_j)=delta_{ij}. The result is

    g_1=1/(41p),
    g_j=pi^{1-j}/41  for 2<=j<=41.                          (3.5)

Check:

- beta(y_1,g_1)=Tr(1/41)=1; beta(y_i,g_1)=Tr(pi^{i-1}/(41p))=0
  because pi^{i-1}/p=pi^{i-42}/u has exponent i-42 in [-40,-1], whose trace
  is 0.
- beta(y_1,g_j)=Tr(pi^{42-j}/(41u))=0 for 2<=j<=41.
- beta(y_i,g_j)=Tr(pi^{i-j}/41)=delta_{ij}, since i-j in [-39,39].

The lattice spanned by g is

    Z_p-span(g_1,...,g_41) = pi^{-41}O_K = p^{-1}I = J^vee.  (3.6)

Proof: g_1 has exponent -41, g_j (j>=2) has exponent 1-j in [-40,-1]; together
they span all exponents -41,...,-1.

Theorem 3.2 (trace-dual of J). The beta-dual lattice of J=m is

    J^vee = p^{-1}I = pi^{-41}O_K.                           (3.7)

In particular the dual basis g_j lies in p^{-1}I, not in J: g_1=1/(41p) has
p-adic valuation -1, and the other g_j have negative exponents. Therefore the
beta-dual basis of J cannot directly serve as Kondo y_i in J.

Label: this is a PROVED exact local computation. It is a no-go for the naive
idea "take the beta-dual basis as the y_i"; the dual basis changes the lattice
in the wrong direction.

## 4. Can S_A be interpreted as Kondo F(x_i)?

For the scenario S_A, each y_i lies in J=m. In the tame low-ramification case
e=41<p-1, log:U^1->m is an isomorphism, so there are units

    u_i := exp(y_i) in 1+m subset O_K^times,
    log(u_i)=y_i.                                           (4.1)

Thus the y_i are realizable as p-adic logarithms of actual units. Moreover,
local reciprocity gives elements x_i in G_K whose images in O_K^times are u_i
(up to the chosen reciprocity normalization).

However, Kondo F(x_i) is not an arbitrary map from units; it is the composite
for the fixed JW generators x_i of Theorem 1.2. The following are not supplied
by the trace-dual construction:

1. a choice of JW generators x_i whose reciprocity images are exactly the
   units u_i=exp(y_i);
2. a proof that these x_i satisfy the Jannsen-Wingberg relations;
3. a proof that the Kondo y_i=F(x_i) equal the chosen powers p,pi,...,pi^40.

The papers give existence of some JW generators and structural properties of
F, not the values F(x_i). Prescribing y_i and finding compatible x_i is an
inverse problem not solved by trace duality.

Classification:

- PROVED: the units u_i=exp(y_i) exist and log u_i=y_i.
- CONDITIONAL: choosing x_i in G_K mapping to u_i under reciprocity.
- NOT PROVED/IMPOSSIBLE FROM CURRENT SOURCE: that these x_i can be chosen to
  be the Kondo JW generators with y_i=F(x_i). This is the additional source
  input, not an arbitrary assumption of this file.

Therefore S_A is a constructed normalization/scenario satisfying the recorded
structural axioms and H_A/B=O_K, but it is not established as an actual Kondo
F-basis.

## 5. Why trace duality does not resolve H_A/B

Every Q_p-basis of K has a beta-dual basis. The trace-dual construction is
therefore compatible with both Model A and Model B of the underdetermination
theorem:

- Model A (S_A): y_1=p, y_i=pi^{i-1}; H_A-full true, B=O_K.
- Model B: y_1=p+pi, y_i=pi^{i-1}; H_A-full false, B=I.

Both are J-bases satisfying the structural axioms; both have beta-dual bases.
The trace pairing alone does not select y_1, the coordinate of 1, or a B
branch. In particular:

    trace-duality is a canonical construction of dual lattices
    O_K^vee=I and J^vee=p^{-1}I,
    but it is not a canonical construction of the Kondo y-basis in J.

This is consistent with the underdetermination theorem: the trace form is a
symmetric Q_p-bilinear form and does not encode the field multiplication or the
Kondo F map; it cannot distinguish y_1=p from y_1=p+pi.

## 6. Proved / conditional / impossible summary

PROVED (exact local algebra):

- S_A explicit y-basis: y_i in J, W=kerTr, Tr(y1)=41p, c=1/p,u0=1,w0=0;
  H_A-full true, B=O_K in the scenario.
- Standard O_K Gram H; dual basis f_a=pi^{-a}/41; O_K^vee=I.
- Naive y Gram G (3.4); dual basis g (3.5); J^vee=p^{-1}I.
- f_a and g are not J-bases; direct dual-basis use as Kondo y_i is impossible
  within J.

CONDITIONAL:

- Units u_i=exp(y_i) and elements x_i in G_K mapping to u_i under reciprocity.
- Interpreting S_A as Kondo F(x_i) requires a JW-compatible choice of x_i; no
  such choice is constructed or known.

NOT PROVED / MISSING:

- Actual Kondo F(x_i) values for E_j's local field;
- a trace-dual construction that is canonical at the level of Kondo F;
- H_A-full/B=O_K as an actual source theorem (only scenario/conditional);
- any complete C/target conclusion.

## 7. Conclusion

The trace-dual construction yields a clean and exact canonical integral model:

    O_K^vee = I,    J^vee = p^{-1}I,

with explicit dual bases. A constructed y-basis S_A=(p,pi,...,pi^40) satisfies
the structural Kondo axioms and gives H_A-full/B=O_K. But the beta-dual bases
themselves do not lie in J, so they cannot be the Kondo y_i; and S_A's
interpretation as Kondo F(x_i) needs a JW-compatible choice of x_i that is not
provided by trace duality. Trace duality does not resolve the H_A/B
underdetermination.

This is a constructed normalization/scenario, not a source theorem. P6 remains
open. target_accepted=false.
