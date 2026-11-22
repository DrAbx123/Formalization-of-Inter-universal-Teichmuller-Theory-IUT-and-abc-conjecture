# C9 audit: H_A-lite construction and alpha_+(1) integrality obstruction (task-196)

Task: task-196. Audit of C9-HAFULL-CONSTRUCT-20261025.md.
Owner: kummer. Date: 2026-10-25.
Stage: SHEAF stage1 natural-language verification only. No Lean/Project edits,
no new attack, no target changes. Only this file written.
target_accepted=false; P6 open.

## 0. Inputs

- C9-HAFULL-CONSTRUCT-20261025.md, 188 lines,
  SHA256 c02d4a24cd201ad6f0fc2d5e308772f943ae29c911058f40ed19a2c8d7ba6878.
- C9-SYMPLECTIC-SOURCE-20261025.md,
  SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70.
- C9-FULL-OUT-COLUMN-ATTACK-20261025.md (E16),
  SHA256 7cc2ddd03cfefa97e38049ca1ccb90016e944dece0185f706e42f7f97cd61fd8.
- C9-CONSTRUCT-E-20261025.md (E22),
  SHA256 0f4e95cd0f21921baf93f3cc8a29bdd4bc582055b13c827d576572b74c8d422d.
- C9-CONSTRUCT-KCK-20261025.md (E23),
  SHA256 e250d5c545ac6f152275b0fc9ec0e4966ff2917318d01b4c684143645c7fd40a.
- C9-HAFULL-ALPHA1-20261025.md (E24 attempt),
  SHA256 ba8459c4500b8e73acfa12a3c20431c5fdf8ed1af077ddd453f5d3c4f2e6a43b.
- C9-HAFULL-CORRECTED-ATTACK-20261025.md (E26/task-202),
  SHA256 a1bdfd61b7fb90d1d24ec9a3d770c308360a095f435d4a2c9f35509775356bf0.

Binding E16/E20: y_i=F(x_i) lies in J and maps to 0 in I/J; the Kondo y-basis
is not an I/J basis. Full Out is Q_p-linear; H_A/H_A-full are explicit source
hypotheses. Task-203 confirms E24 invalid and task-200's W=Z_p-span(pi..pi40)
subset J conflation erroneous. Task-202 corrects alpha_+(1) to a canonical
element and states the exact integrality criterion.

## 1. Executive verdict

1. H_A-lite is CONDITIONAL/VALID on the paper interface: local
   reciprocity/inertia, Kondo alpha_+ log = log alpha^times, and J=m give
   alpha_+(J)=J, alpha_+(I)=I, a Z_p-action on J and an F_p-action on I/J.
   It does not use the y-basis and does not require alpha(O_K)=O_K.

2. Gamma_0=Stab(O_K) is open of finite index; B_Gamma0=O_K. This is valid
   conditional H_A-full for Gamma_0, not full Out.

3. CORRECTED task-202/E26: alpha_+(1) is canonically determined:
   alpha_+(1)=p^{-1} alpha_+(p)=p^{-1} log(alpha^times(exp p)) in I.
   It is not undetermined. The obstruction is integrality: H_A-full(alpha)
   iff alpha_+(1) lies in O_K minus J (nonzero class in l=O_K/J). If H_A-full
   holds for all actual alpha, then B_Gamma=O_K. Full H_A-full and
   Gamma_0=Out remain open; B=O_K is conditional on H_A-full; B=I is not
   available under H_A-full and is not constructed outside it.

4. E24/task-195 is INVALID as written: its step W subset J is false. W=ker Tr
   is a Q_p-hyperplane of dimension 40; J=m is a Z_p-lattice of rank 41; a
   nonzero Q_p-vector space is not contained in a Z_p-lattice (p^{-1}pi in W
   but not in m). The Z_p-span(pi,...,pi^40) is W cap J, not W. Task-203
   confirms the invalid step and rejects task-200's conflation.

5. Aut(K) acts diagonally on O_K and fixes l; B_Aut(K)=O_K. The field
   automorphism matrix on O_K is diag(1,zeta,...,zeta^40); on the negative-
   exponent I/J basis it is the inverse diagonal. It does not produce B=I.

6. E22 blocks exact q=p^6 for every elliptic curve over a number field
   (p-adic Mahler-Manin). E23 supplies an actual E_j/Q with j0=1/p^6, explicit
   equation, v_p(Delta)=6, local q=p^6+744p^12+... not p^6, and qhat order3;
   the b=3 profile is actual with a unit twist, partially resolving O1. A
   complete C is still missing.

## 2. H_A-lite: J and I preservation

Inputs: local reciprocity identifies inertia with O_K^times, so Out(G_K) acts
on O_K^times; Kondo 2026 Theorem2.6 proof gives alpha_+ log = log alpha^times;
in the tame low-ramification type log(O_K^times)=J=m and I=p^{-1}J.

For alpha in Out(G_K):

    alpha_+(J)=alpha_+(log(O_K^times))
             = log(alpha^times(O_K^times))
             = log(O_K^times)=J,
    alpha_+(I)=p^{-1}alpha_+(J)=I.

Thus alpha_+|J is a Z_p-linear automorphism of J; the induced map on I/J is
F_p-linear. This is conditional on the Kondo/AbsTopIII interface and
k_+(G_K)=K identification. It does not require O_K preservation and does not
use the y-basis.

Status: CONDITIONAL/VALID. H_A-lite alone does not give H_A-full.

## 3. Gamma_0 and B_Gamma0

Gamma_0={gamma in Out(G_K): gamma(O_K)=O_K}. Since Out is compact and acts
continuously on K_+, and the stabilizer of a lattice in GL_d(Q_p) is open,
Gamma_0 is open finite index. For gamma in Gamma_0, gamma(O_K)=O_K and, by
H_A-lite, gamma(J)=J, gamma(I)=I; hence H_A-full on Gamma_0 and

    B_Gamma0 = closed Z_p-span union_{gamma in Gamma_0} gamma(O_K) = O_K.

This does not imply B=O_K for full Out. For cosets outside Gamma_0, gamma(O_K)
is a commensurable lattice not necessarily equal to O_K and not necessarily
inside I; full B is not well-posed without H_A-full.

Status: VALID CONDITIONAL for Gamma_0; NOT PROVED full Out.

## 4. alpha_+(1): corrected canonical formula and exact criterion

The earlier claim "alpha_+(1) is not determined" is FALSE (task-202). Since
p in J and alpha_+(J)=J,

    alpha_+(p)=alpha_+(log(exp p))=log(alpha^times(exp p)) in J,
    a(alpha):=alpha_+(1)=p^{-1}alpha_+(p)
            =p^{-1}log(alpha^times(exp p)) in I.

This is canonical, no basis/generator/lift chosen. The obstruction is
integrality:

    a(alpha) in I, but a(alpha) may fail to lie in O_K.

Because alpha_+(J)=J,

    alpha_+(O_K)=alpha_+(Z_p 1+J)=Z_p a(alpha)+J.

Hence the exact criterion:

    H_A-full(alpha) <=> alpha_+(O_K)=O_K
                     <=> a(alpha) in O_K minus J
                     <=> a(alpha) has nonzero class in O_K/J=l.

Proof of the equivalences: if a in J then Z_p a+J=J; if a not in O_K then
Z_p a+J is not contained in O_K; if a in O_K minus J its nonzero class in the
one-dimensional line l gives Z_p a+J=O_K.

Decompose K=Q_p 1 direct-sum W, a(alpha)=lambda(alpha)1+w(alpha), w in W.
Then a in O_K iff w in J cap W; a in O_K minus J iff additionally lambda has
nonzero class mod p. No W subset J is assumed.

Conditional theorem: if H_A-full holds for every actual alpha, then every
alpha fixes l and B_Gamma=O_K. H_A-full itself is NOT proved; Gamma_0=Out is
not proved. The exact remaining obstruction is integrality of
a(alpha)=alpha_+(1) in O_K minus J for every actual alpha, equivalently an
explicit computation of alpha_+(p) or alpha^times(exp p).

Status: canonical formula VALID CONDITIONAL on H_A-lite; exact criterion VALID;
H_A-full OPEN; B=O_K conditional on H_A-full; B=I not available under it.

## 5. E24 attempted proof: invalid W subset J

E24's trace-scalar part is conditionally valid: W=ker Tr preserved gives
Tr o alpha_+ = lambda(alpha)Tr, lambda in Q_p^times; compactness puts lambda in
Z_p^times; K=Q_p1 direct-sum W and alpha_+(1)=lambda1+w with w in W.

Fatal step: W subset m=J. W is a Q_p-hyperplane, J=m a Z_p-lattice; a nonzero
Q_p-vector space cannot be contained in a Z_p-lattice. Example p^{-1}pi in W
but p^{-1}pi not in m. The Z_p-span(pi,...,pi^40) is W cap J, not W. Therefore
w need not lie in J, alpha_+(1) need not lie in O_K, and alpha_+(O_K) subset O_K
does not follow. E24 constructs neither H_A-full nor B=O_K and does not exclude
B=I. Task-203 adjudicates E24 invalid; task-200's W=Z_p-span(pi..pi40) subset J
is a Q_p/Z_p conflation.

The valid survivor is the canonical alpha_+(1) formula of Section 4 plus the
integrality criterion; the invalid step is not that alpha_+(1) is undetermined.

## 6. Aut(K), E22 and E23

Aut(K): sigma(pi)=zeta pi, zeta^41=1, acts on O_K by
diag(1,zeta,...,zeta^40) in the pi-power basis, preserves O_K,J,I, fixes l;
B_Aut(K)=O_K. On the negative-exponent I/J basis the diagonal entries are
inverse exponents; still fixes l.

E22: exact q=p^6 is impossible for any elliptic curve over any number field.
q=p^6 is algebraic with 0<|q|_p<1; p-adic Mahler-Manin says J(p^6) is
transcendental over Q; a Tate parameter q_v=p^6 would give algebraic
j(E)=J(p^6), contradiction. This blocks the exact task-183 q=p^6 profile, not
all complete C.

E23: actual E_j/Q with j0=1/p^6,
E_j: y^2=x^3-3j0/(j0-1728)x-2j0/(j0-1728),
Delta=2985984 p^6/(1-1728p^6)^3, v_p(Delta)=6, v_p(j0)=-6. Its Tate parameter
is NOT p^6: q=p^6+744p^12+..., q/p^6 in 1+p^6Z_p. Since 82 is a p-adic unit,
qhat=q^{1/82}=pi^3 v with v in 1+pZ_p, order b=3; K_v/Q_p has e=41,f=1.
F=Q(i,E[6]) is Galois with [F:Q] dividing 576=2^5*3^2, so 41 does not divide
[F:Q]; K=F(E[41]); X_K,C_K,V,epsilon formal. The b=3 profile is ACTUAL with
unit twist; still missing stable reduction over all F places (semistabilization
degree prime to 41), other bad q-orders, mod-41 image containing SL2, and
explicit C_F/C_K/V/epsilon. O1 partially resolved; exact q=p^6 remains blocked.

## 7. Classification

ACTUAL/PAPER-LEVEL:
- local p=12301,e=41,K=Qp(pi); J=m,I=p^{-1}J; trace table; W=ker Tr.
- inertia/reciprocity action and Kondo alpha_+ log=log alpha^times.
- H_A-lite: full Out preserves J,I and acts Z_p/F_p (conditional interface).
- Gamma_0 open finite index; B_Gamma0=O_K.
- Aut(K) diagonal; fixes l; B_Aut(K)=O_K.
- alpha_+(1)=p^{-1}log(alpha^times(exp p)) in I canonical.
- H_A-full iff alpha_+(1) in O_K minus J; nonzero class in l.
- E22 exact q=p^6 impossible; E23 actual E_j unit-twist b=3.

CONDITIONAL:
- H_A-lite for full Out (Kondo/AbsTopIII interface).
- Gamma_0 H_A-full/B_Gamma0=O_K.
- H_A-full => B=O_K; H_A-full itself open; Gamma_0=Out open.
- E23 b=3 profile and partial O1; other data missing.

INVALID/WITHDRAWN:
- E24 W subset J proof; task-200 W=Z_p-span(pi..pi40) subset J.
- alpha_+(1) undetermined (task-202 corrects).
- exact q=p^6 global E/Mahler-Manin blocked.
- y-basis as I/J basis; B=O_K/B=I for full Out as actual; any full B conclusion
  from H_A-lite/Gamma_0 alone.

MISSING:
- H_A-full integrality a(alpha) in O_K minus J for all actual alpha;
  Gamma_0=Out; explicit full-Out matrices/lambda/w.
- E23 stable reduction all F places, other q-orders, mod41 SL2, explicit
  C_F/C_K/V/epsilon, complete C, S_bad, q/BPS/weights, TC/arch.

## 8. Error ledger

| id | item | verdict | correction |
|---|---|---|---|
| H1 | H_A-lite J/I preservation | CONDITIONAL/VALID | paper interface; no y-basis |
| H2 | Z_p/F_p action on J/I/J | CONDITIONAL/VALID | follows from H_A-lite |
| H3 | Gamma_0 open finite index | VALID CONDITIONAL | stabilizer of lattice |
| H4 | B_Gamma0=O_K | VALID CONDITIONAL | subgroup only |
| H5 | alpha_+(1) integrality obstruction | VALID | a=p^{-1}log(alpha^times(exp p)) in I; H_A-full iff a in O_K minus J |
| H6 | alpha_+(1) undetermined | FALSE | task-202 canonical formula |
| H7 | Aut(K) diagonal | VALID local | O_K basis; I/J inverse exponents; fixes l |
| H8 | W subset J / E24 | INVALID | W Q_p-hyperplane not Z_p-sublattice of J |
| H9 | task-200 W=Z_p-span(pi..pi40) subset J | INVALID | conflates Q_p kernel with Z_p span |
| H10 | H_A-full full Out | NOT PROVED | integrality a(alpha) missing |
| H11 | H_A-full => B=O_K | CONDITIONAL THEOREM | task-202; then l fixed |
| H12 | B=I under H_A-full | IMPOSSIBLE | l fixed; no B=I generator |
| H13 | B=O_K without H_A-full | NOT PROVED | only conditional |
| H14 | E22 exact q=p^6 global E | IMPOSSIBLE | Mahler-Manin |
| H15 | E23 actual E_j unit twist | ACTUAL/CONDITIONAL | explicit equation/Delta; other data missing |

## 9. Conclusion

H_A-lite is a conditional construction: under reciprocity/Kondo log
compatibility full Out preserves J,I and acts Z_p/F_p-linearly. Gamma_0 is an
open finite-index H_A-full subgroup with B_Gamma0=O_K. Task-202 gives the
canonical alpha_+(1)=p^{-1}log(alpha^times(exp p)) and the exact H_A-full
criterion a(alpha) in O_K minus J; if H_A-full holds for all alpha then B=O_K.
Full H_A-full and Gamma_0=Out remain open; B=O_K is conditional, B=I is not
available under H_A-full.

E24/task-195 is invalid at W subset J; task-203 confirms; task-200's Z_p-span
reading is erroneous. Exact q=p^6 is impossible for any E over a number field
(E22); E23 actual E_j/Q gives a unit-twist b=3 profile, partially resolving O1,
but no complete C. P6 remains open.

## 10. Status

- Natural-language audit only; no Lean/Project edits; no new attack.
- H_A-lite, Gamma_0/B_Gamma0, alpha_+(1) criterion, E24 invalidity, E22/E23
  classified.
- No complete C; target_accepted=false; P6 open.
