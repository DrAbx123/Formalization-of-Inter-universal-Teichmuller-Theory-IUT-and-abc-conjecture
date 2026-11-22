# C9 actual kappa / B=I: conditional theorem and exact source obstruction

Task: task-269. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no audit loop, no Lean/Project edits, no arbitrary data.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs

- C9-NEW-BI-SOURCE-20261025.md (task-250), 235 lines,
  SHA256 a90cc1b516a9afc784a20a8ce2fafb6cf16752459d73562d36c3093b85b294b3.
- C9-ZP-BASIS-THEOREM-20261025.md (task-255), 253 lines,
  SHA256 f7fca7b4336497d954a711d79033df56c046faa2caabe8ff436f9b8046c30e3a.
- C9-KAPPA-THEOREM-20261025.md (direct kappa theorem), 192 lines,
  SHA256 a73b6a5d2f7ceb87a68841be29a88edb018cd5094002bae59c70bf194046cd88.
- C9-LOGIC-CORRECTION-20261025.md (task-264), 180 lines,
  SHA256 a0dc631787154e821db664344bab425d8edeff848dc19eb336f7e2df6b0c21c9.

## 1. Verdict

The **kappa branch theorem is valid conditionally on the actual kappa**, but
there is **no source theorem computing the actual kappa** and hence **no
source theorem proving B=I**. The exact obstruction is:

1. Kondo's y_i=F(x_i) are only a Q_p-basis of K; no cited theorem makes them a
   Z_p-basis of J or O_K.
2. Local reciprocity does not identify the nonabelian wild inertia P_K with the
   abelian pro-p group U^1; the F values y_i are not computed by any explicit
   reciprocity formula in the frozen source.
3. The trace-pairing anti-diagonal Gram used in the conditional kappa theorem is
   an extra normalization assumption, not a Kondo theorem.
4. Even if y_i were a Z_p-basis of J, not every y_i can have v_pi(y_i)=1:
   J/pi J is one-dimensional over F_p, so at most one basis vector has
   v_pi=1; the others have v_pi>=2.
5. The structural axioms admit both kappa=0/B=O_K and kappa=40/B=I (models A
   and B); the actual y1/Tr(y1) is the missing input.

Therefore: **actual kappa is not determined; B=I is not proved; B=O_K is not
proved.** This is an exact source obstruction, not a negative computation.

## 2. Kappa branch theorem (valid conditional)

Let p=12301, e=41, K=Q_p(pi), pi^e=p u, O_K=Z_p[pi], J=m=(pi),
I=p^{-1}J, W=ker Tr. Kondo gives a Q_p-basis y_1,...,y_e with y_i in J,
W=Q_p-span(y_2,...,y_e), Tr(y1) in pZ_p nonzero. Define

    kappa := e v_p(Tr(y1)) - v_pi(y1).                           (2.1)

Since Tr(y1) in pZ_p and y1 in J, kappa is an integer.

Theorem 2.1 (kappa-B dichotomy; task-250). For the actual data:

(a) kappa<=0 => H_A-full and B=O_K;
(b) 1<=kappa<=40 => B=I (A=-I gives a(alpha)=1-2w0 notin O_K; Sp-orbit
    spans I/J);
(c) kappa>=41 => B is not well-posed inside I; B=I is not obtained.

This theorem is conditional only on the actual kappa. It does not prove
kappa lies in any range.

Correction from task-264: kappa decides B, not P6. In particular
kappa<=0/B=O_K does NOT imply b=3 P6 false; 1<=kappa<=40/B=I does not
automatically prove P6 (only the finite lower-bound direction is available).

## 3. Exact kappa in the two structural models

The structural axioms admit:

Model A: y1=p. Then v_pi(y1)=41, Tr(y1)=41p, v_p(Tr)=1,

    kappa=41*1-41=0,  B=O_K.                                    (3.1)

Model B: y1=p+pi. Then v_pi(y1)=1, Tr(y1)=41p, v_p(Tr)=1,

    kappa=41*1-1=40,  B=I.                                      (3.2)

Both satisfy the recorded Kondo structural data (Q_p-basis, W=kerTr,
y_i in J, Tr(y1) in pZ_p, Sp action). They show that kappa=0 and kappa=40 are
both compatible with the source structure. No frozen source selects one.

## 4. Why the source cannot compute kappa

### 4.1 Kondo gives only Q_p-basis

Kondo 2026 Lemma 1.3 gives y_i as a Q_p-basis of k_+(G_K)=K, with y_i in J.
It does not state:

- that the y_i are a Z_p-basis of J;
- that the change-of-basis matrix to (p,pi,...,pi^40) has determinant in
  Z_p^times;
- that v_pi(y_i)=1 for all i;
- any explicit values of y_i or Tr(y_i).

Without an integral basis/change matrix, kappa is not computable from the
source data.

### 4.2 Local reciprocity/wild inertia

Local reciprocity identifies the inertia subgroup of G_K^ab with O_K^times and
its pro-p part with U^1=1+m. Wild inertia P_K is a nonabelian pro-p group; its
image in G_K^ab is the abelianization P_K/[P_K,P_K], mapped to U^1, not an
isomorphism P_K->U^1. The JW generators x_i lie in P_K; F(x_i) depends on
their actual reciprocity-unit values, which are not explicit in the frozen
source. The JW relation under F gives only

    F(x_0)=t F(x_0')+p^s y_1,                                   (4.1)

involving F(x_0),F(x_0') outside the y-basis; it does not compute y1 or
Tr(y1).

### 4.3 Trace pairing is not the source form

The field trace pairing beta(x,y)=Tr(xy) is symmetric; its restriction to W
has W^perp=Q_p1, while the Kondo fixed line U=<y1> is not W^perp in general
(tasks 224/227). The anti-diagonal Gram matrix used in the direct kappa theorem
(task C9-KAPPA-THEOREM) is an extra normalization assumption, not a Kondo
theorem. Without it, v_p(Tr(y1)) need not be1, so kappa need not lie in
[0,40].

### 4.4 Even a hypothetical Z_p-basis does not force all v_pi=1

J/pi J is one-dimensional over F_p (J=pi O_K, pi J=pi^2 O_K,
J/pi J ~= O_K/pi O_K ~= F_p). A Z_p-basis of J has e=41 elements, but at most
one can have nonzero reduction modulo pi J; the other 40 have v_pi>=2. Thus
the hypothesis "all y_i have v_pi=1" in task-255 is impossible. This does not
by itself determine kappa; it only rules out that route.

## 5. Exact missing input

The actual kappa is equivalent to either of:

- the actual y1 (or y1 modulo J/pi J) and Tr(y1);
- v_pi(y1) and v_p(Tr(y1));
- the Z_p-change-of-basis matrix from the y-basis to (p,pi,...,pi^40),
  together with the trace of y1.

No source in the frozen corpus supplies these. Therefore:

    kappa is source-undetermined;
    B=O_K is not proved;
    B=I is not proved.

This is the exact obstruction. It is not a counterexample to either branch.

## 6. Classification

| item | status |
|---|---|
| kappa=e vp(Tr y1)-vpi(y1) integer | PROVED |
| kappa<=0=>B=OK, 1..40=>B=I, >=41 not well-posed | PROVED conditional on actual kappa |
| kappa decides B only, not P6 sign | PROVED (task-264 correction) |
| actual kappa computed by Kondo/JW/F/trace | NO; exact obstruction |
| y_i Q_p-basis vs Z_p-basis | ONLY Q_p in source |
| local reciprocity P_K iso U^1 | FALSE (nonabelian vs abelian) |
| all vpi(y_i)=1 for Z_p-basis | IMPOSSIBLE |
| kappa=0/B=OK model | CONSISTENT |
| kappa=40/B=I model | CONSISTENT |
| B=I source theorem | NOT OBTAINED |
| B=OK source theorem | NOT OBTAINED |
| P6 via kappa | NO: kappa not P6 sign |

## 7. Conclusion

The only rigorous source theorem is the conditional kappa-B dichotomy: if the
actual kappa lies in 1..40, then B=I; if kappa<=0, then B=O_K. The actual kappa
is not computed: Kondo gives a Q_p-basis, not an integral basis; local
reciprocity does not identify wild inertia with U^1; the trace pairing does not
fix the y-basis; and even a Z_p-basis cannot have all v_pi(y_i)=1. Models A/B
show kappa=0/B=OK and kappa=40/B=I are both compatible with the recorded
structure. The exact missing input is the actual y1/Tr(y1) or the integral
change-of-basis. Therefore B=I is not proved, B=OK is not proved, and P6 is not
decided by kappa.

No arbitrary data; no Lean/kernel closure; target_accepted=false; P6 open.

## 8. Status

- Short natural-language theorem/proof only; no Lean/Project edits.
- Conditional kappa-B theorem restated; exact source obstruction to actual
  kappa/B=I recorded; no arbitrary input.
- target_accepted=false.
