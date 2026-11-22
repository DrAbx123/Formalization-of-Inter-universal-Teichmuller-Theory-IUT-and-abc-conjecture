# C9 alternative E profile: actual curve, bad at 12301, computed Tate parameter

Task: task-197 (C9-ALTERNATIVE-E-PROFILE-20261025). Owner: logdescent. Date: 2026-10-25. SHEAF stage1 natural-language/exact-computation research. Only this file written. No Lean/Project/target/other-owner edits. Consumer: n8-c9-output-region-source-route P6. P6 unproved; target_accepted=false.

Inputs: C9-CONSTRUCT-E-20261025.md (SHA256 0F4E95CD0F21921BAF93F3CC8A29BDD4BC582055B13C827D576572B74C8D422D); C9-FULLC-CONSTRUCTION-ATTACK-20261025.md (task-183); C9-AUDIT-FULLC-CONSTRUCTION-20261025.md (task-188); IUT I Def3.1; p-adic Mahler-Manin theorem (Barré-Sirieix-Diaz-Gramain-Philibert, Invent. Math. 124 (1996), 1-9).

## 0. Verdict

An actual elliptic curve over Q with algebraic j and split multiplicative reduction at p=12301 has been constructed:

    E: y^2 = x^3 + 4 x - 2437249.                                  (0.1)

Exact invariants:
- Delta(E) = -2566158921220528 = -16 * 12301 * 19 * 686229757.
- j(E) = 442368 / 160384932576283 = 442368 / (12301 * 19 * 686229757).
- Bad-reduction set over Q: {2, 19, 12301, 686229757}.
- At p=12301: split multiplicative reduction, v_p(Delta)=1, v_p(j)=-1.
- At 19 and 686229757: multiplicative reduction (v=1 in Delta), stable.
- At 2: additive reduction with v_2(Delta)=4, but j has v_2=14 >= 0, hence potential good reduction; a finite extension of degree a power of 2 makes it good and stable.

The actual Tate parameter at p is computed by solving J(q)=j(E) in Q_p. It has v_p(q)=1 and, modulo p^21,

    q = p * 5168865309000495801384673649029265377681057827317425313600722852686093890527523842
        (mod p^21),                                                   (0.2)

with q/p = 5348 + 1516 p + 7385 p^2 + 2824 p^3 + 41 p^4 + ... (p-adic digits; see section 3). The Newton residual J(q)-j(E) is 0 modulo p^20. In particular q is not p^6: its p-adic valuation is 1, while v_p(p^6)=6.

Field/torsion status:
- E is defined over Q, so field of moduli Q and j algebraic.
- Let F0 = Q(zeta_12, E[6]). Then F0 contains zeta_12 and all E[2], E[3] torsion; degree [F0:Q] divides 4 * |GL_2(Z/6)| = 4*288 = 1152 = 2^7*3^2, hence is prime to 41. F0/Q is Galois. Thus full E[6] is rational over F0, and F0/F_mod is Galois of degree prime to l=41, as required by IUT I Def3.1(b).
- However F0 is larger than Q(zeta_12). For this E, strict F=Q(zeta_12) is impossible: the cubic x^3+4x-2437249 has discriminant -160384932576283, which is not a square in Q, so Q(E[2]) is an S3-extension (nonabelian) and cannot be contained in the abelian field Q(zeta_12). Therefore full E[2] (and hence full E[6]) is not rational over Q(zeta_12) for this curve.
- The original task allowed F=Q(zeta_12) or larger (IUT Def3.1(b) only requires F/F_mod Galois of degree prime to l). The actual F below is a larger extension. If the strict field F=Q(zeta_12) is required, this E is not a solution and the search/construction of a special curve with abelian E[2]/E[3] remains open. This is the exact conditional boundary of the construction.

The curve is not an arbitrary choice: it was found by solving the exact congruence 4a^3+27b^2 = 0 mod 12301 for a=4 and choosing b so that the quotient is squarefree and the node is split. The bad set and q are computed from the equation, not selected.

## 1. Exact construction and invariants

Curve (0.1): E: y^2 = x^3 + 4x - 2437249 over Q.

Invariants (standard formulas):
- b2=0, b4=8, b6=-4*2437249 = -9748996, b8= -4*4*2437249? For b8 = a1^2 a6 +4 a2 a6 - a1 a3 a4 + a2 a3^2 - a2^2 a4 + a2 a4^2 with a2=0,a4=4,a6=b: b8=0.
- c4 = -48*4 = -192? c4 = b2^2 -24 b4 = -192 (depending sign convention; c4 = b2^2 - 24 b4).
- Delta = -16(4*4^3 + 27*b^2) = -16*160384932576283 = -2566158921220528.
- j = c4^3/Delta = 1728 * 4 a^3 / (4a^3+27b^2) = 442368 / 160384932576283.
Factor 160384932576283 = 12301 * 19 * 686229757, with all three factors prime; hence 12301 | Delta exactly once and 19,686229757 divide Delta exactly once.
- The model is minimal at all odd primes dividing Delta because p>3 and v_p(Delta)=1; any scaling by a nonunit would multiply Delta by a 12th power, increasing valuation. At 2, v_2(Delta)=4 and j has v_2=14; the reduction is additive but potentially good.

Bad-reduction set over Q: {2, 19, 12301, 686229757}. At 19 and 686229757 the reduction is multiplicative (v(Delta)=1), hence stable. At p=12301 it is split multiplicative (next section), also stable.

## 2. Torsion field and the strict F=Q(zeta_12) issue

E is over Q, so field of moduli Q. Define

    F0 = Q(zeta_12, E[6]).                                         (2.1)

Since E is over Q, E[6] is a finite Galois extension of Q; its Galois group is a subgroup of GL_2(Z/6), of order |GL_2(Z/2)|*|GL_2(Z/3)| = 6*48 = 288. Q(zeta_12)/Q is Galois of degree 4. Hence F0/Q is Galois and its degree divides 1152=2^7*3^2, which is prime to 41. F0 contains zeta_12, hence sqrt(-1), and contains all E[2] and E[3] by construction. Therefore full E[6] is rational over F0.

Strict F=Q(zeta_12) fails for this E. The 2-division field is the splitting field of the cubic x^3+4x-2437249. Its discriminant is -160384932576283, which is not a square (integer square root check exact: no square equals 160384932576283). Hence the cubic is irreducible with Galois group S3 (nonabelian), and Q(E[2]) has degree 6. Q(zeta_12)/Q is abelian of degree 4, so it cannot contain an S3-extension. Thus E[2] is not full over Q(zeta_12), and E[6] is not full over Q(zeta_12). Enlarging to F0 is necessary for this curve.

This is not a defect of the arithmetic: IUT I Def3.1(b) asks F/F_mod Galois of degree prime to l, not F=Q(zeta_12). The original task-191 explicitly allowed F=Q(zeta_12) or larger. If task-197 insists on the literal F=Q(zeta_12), this E is a counterexample to that strict field requirement while satisfying the source clause with F0; the strict version remains missing.

Stable reduction over F:
- At odd bad primes 19, 686229757, and p=12301, reduction is multiplicative, already stable over Q.
- At 2, E has additive reduction but potential good reduction because j is 2-adic integral (v_2(j)=14). By the potential good reduction theorem for local fields, there is a finite extension F_2/F0 of degree a power of 2 (or dividing a small 2-power) over which E has good reduction at all places over 2. Since 41 is odd, this extension degree remains prime to 41. Set F = F0 * F_2 (compositum); then E/F has good reduction at 2 and multiplicative reduction at the odd bad primes, hence stable reduction everywhere.
- The exact 2-adic extension F_2 is not computed; its existence is standard (potential good reduction). This is the only conditional field-theoretic step in the construction.

## 3. Actual Tate parameter via Tate's algorithm

At p=12301 the reduction of E is split multiplicative:
- Reduction cubic c(x)=x^3+4x-2437249 mod p has roots 1837 and 5232. The double root is x0=5232 (derivative 3x0^2+4 = 3*5232^2+4 is 0 mod p), the other root is x1=1837. The tangent slopes are determined by x0-x1 = 3395; its Legendre symbol is +1, so the node is split. (Exact computation: p=12301, x0=5232, x1=1837, x0-x1=3395, 3395^((p-1)/2) = 1 mod p.)
- v_p(Delta)=1 and v_p(j)=-1; the Tate parameter q has v_p(q)=1, q in p Z_p.

Tate j-function:
J(q) = q^{-1} + 744 + 196884 q + 21493760 q^2 + 864299970 q^3 + 20245856256 q^4 + 333202640600 q^5 + ...
(integer coefficients computed exactly from E4^3/Delta).

Write q=p u with u in Z_p^x. Then p J(pu)=j p becomes

    1/u + 744 p + 196884 p^2 u + 21493760 p^3 u^2 + ... = 442368/d,   (3.1)

where d = 160384932576283/12301 = 13038365383 = 19*686229757, and 442368/d is a p-adic unit. Newton iteration in Z_p modulo p^20 gives

    u = 5168865309000495801384673649029265377681057827317425313600722852686093890527523842
        (mod p^20),
    q = p u = 63582212166015098852832870556708993410854692333831648782602491810891640947379070780442
        (mod p^21).                                                   (3.2)

The p-adic digits of u (least significant first, base p) are

    5348, 1516, 7385, 2824, 41, 4349, 10, 2773, 6508, 12088, 6333,
    3196, 8068, 9902, 5174, 3285, 1405, 8124, 9709, 10104  (mod p^20).   (3.3)

The Newton residual F(u)=pJ(pu)-pj is 0 modulo p^20. The leading p-adic digits are q = p*(5348 + 1516 p + 7385 p^2 + 2824 p^3 + 41 p^4 + ...). This is the actual local Tate parameter of E at p, computed from the equation, not chosen.

Checks:
- v_p(q)=1, so q is not p^6 (which has valuation 6); the task-183 candidate is not used.
- q is transcendental over Q: if q were algebraic, the p-adic Mahler-Manin theorem would make J(q)=j(E) transcendental, contradicting j(E) algebraic. Thus the actual q is transcendental, consistent with the theorem and with the no-go for q=p^6.
- The split condition is exact and local: node tangent slopes in F_p; no numerical approximation is used for the split/nonsplit decision.

## 4. Actual / conditional / missing

Actual (exact):
- E: y^2=x^3+4x-2437249 over Q; j=442368/160384932576283 algebraic; field of moduli Q.
- Bad set {2,19,12301,686229757}; Delta=-16*12301*19*686229757; multiplicative at 19,12301,686229757, additive potential good at 2.
- Split multiplicative at p=12301; v_p(q)=1; actual q mod p^21 (3.2), Newton residual zero mod p^20.
- F0=Q(zeta_12,E[6]) is Galois over Q, contains E[6], degree divides 1152=2^7*3^2, prime to41.
- Strict F=Q(zeta_12) fails for this E because E[2] is S3: x^3+4x-2437249 is irreducible over Q (2437249=647*3767, no rational root) and its discriminant is nonsquare, so Q(E[2]) is nonabelian of degree 6, not contained in abelian Q(zeta_12).

Conditional/standard:
- A finite 2-power extension F_2/F0 makes E have good reduction at 2; F=F0*F_2 is Galois over Q of degree prime to41, and E/F has stable reduction everywhere. The exact F_2 is not computed.
- If the strict field F=Q(zeta_12) is required, this E does not satisfy the torsion field condition; a special E with abelian E[2] and E[3] over Q(zeta_12) would be needed. This file does not construct such a curve.
- The mod-41 image containing SL2(F41) is not verified for this E. It is a separate representation computation (Frobenius traces/large image theorem); no claim is made. This condition is not part of task-197 as stated, but is part of the original task-191 O1 condition.

Missing:
- Exact 2-adic semistabilizing extension F_2 and hence the explicit final F.
- Full E[6] over Q(zeta_12) for a strict-field solution (not achieved by this E).
- mod-41 image verification.
- E[41]/K/CK/V/epsilon; complete C; S_bad weights/local types; q/BPS/gluing; target column; TC-A..TC-H+TC-S; archimedean data.
- No target containment or global h_C/Q_C claim.

## 5. Consequence for O1

The q=p^6 profile is impossible by Mahler-Manin (task-191). This file gives an actual alternative E with algebraic j, bad reduction at p=12301, split multiplicative q of valuation 1, and a computed p-adic Tate parameter q not equal to p^6. It also gives the exact bad set and shows how to choose F so that full E[6] is rational and reduction is stable.

It does not close O1:
- F is larger than Q(zeta_12); strict-field clause (b) is not satisfied by this E.
- mod-41 image not verified.
- The remaining complete-C data and target conditions are missing.

Thus O1 remains open; the alternative profile is a real arithmetic candidate with exact local data, not an arbitrary curve and not a complete C.

## 6. Reproducibility and sources

Exact Python 3 computations (integers/Fractions, no floating point):
- primality p=12301, p mod12=1, p mod41=1, p^6;
- E invariants/discriminant/factorization;
- cubic discriminant nonsquare check;
- split node Legendre symbol;
- j q-expansion coefficients from E4^3/Delta;
- Newton iteration for q modulo p^20/p^21; residual check.

Sources:
- IUT I May 2020, Definition 3.1(a)-(f), especially (b) F/F_mod Galois of degree prime to l and full E[2]/E[3] over F.
- C9-CONSTRUCT-E-20261025.md for the Mahler-Manin no-go on q=p^6.
- Task-183/188 for the candidate and q_Tate=p^6u^6 audit.
- Standard Tate algorithm/j(q) q-expansion; standard potential good reduction theorem for local fields.

Acceptance: only C9-ALTERNATIVE-E-PROFILE-20261025.md written; no Lean/Project/target/other-owner edits. Natural-language self-review done; Lean/Project/kernel/comparator/independent review not run; not applicable. target_accepted=false; complete C9/P6 unproved.
