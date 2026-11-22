# C9 explicit C_F/C_K/V/epsilon equations for E_j

Task: task-230 (C9-EXPLICIT-C-EQUATIONS-20261025). Owner: logdescent. Date: 2026-10-25. SHEAF stage1 construction/audit; only this file written; no Lean/Project/target/other-owner edits. No U/B normalization and no arbitrary data are introduced. P6 unproved; target_accepted=false.

Inputs: C9-CONSTRUCT-KCK-20261025.md (task-193); C9-EJ-COMPLETION-20261025.md (task-198); IUT I Def3.1(a)-(f); IUT III Def1.1/Prop1.2/Thm3.11.

## 0. Verdict

This file constructs as much of the explicit C_F/C_K/V/epsilon data as follows from E_j alone:

1. Exact rational Weierstrass equation of E_j, with all arithmetic constants, bad set, and local type at p.
2. Exact 41-division polynomial recursion, its degree (840) and leading term, the field K=F(E[41]) as a splitting field, and X_K=E_K minus O.
3. The quotient stack C_K=[X_K/E[41]] with its translation action and local cusp type, and the K-core/C_F descent specification.
4. The V/Vbad data: after semistabilization Vbad={p=12301}; V is a section over p; local place/uniformizer at p are given.
5. epsilon: the origin cusp of X_K; the local cusp parameter t=x/y at O; the canonical-generator cusp at bad p is specified.

What is explicitly missing (the exact missing computations):
- The full expansion/factorization of psi_41 over F (degree 840, coefficients enormous), hence a defining polynomial/field equation for K and [K:F].
- The Velu/41-isogeny equation for the coarse quotient E_K/E[41], hence an explicit coarse equation for C_K; the stacky gerbe/orbicurve structure and its cusp equations.
- The descent data/1-cocycle defining C_F over F from C_K, and explicit C_F equations.
- The actual global places of K over p (V section) and explicit cusp coordinates on C_K/C_F; the local data at p are explicit, but the global field K is not.
- The mod-41 image/SL2 check, stable semistabilization of E_j at the M-primes, and the complete-C BPS/Theta/target data.

Thus E_j does not yet give a fully explicit complete C. The obstruction is computational (large division polynomial/field/descent equations), not a new arbitrary choice or a change of target.

## 1. Exact E_j equation

Let p=12301, p^6=3464515518466761109423801, and

    M := 1728 p^6 - 1 = 5986682815910563197084328127
       = 1009 * 50833 * 1799579 * 64860221162029.                  (1.1)

Then

    E_j : y^2 = x^3 + (3/M) x + (2/M),   j(E_j)=1/p^6.            (1.2)

Equivalently, with D=1-1728p^6=-M,

    E_j : y^2 = x^3 - 3/D x - 2/D.

Exact invariants:
- a=3/M, b=2/M.
- 4a^3+27b^2 = 108(1+M)/M^3 = 108*1728p^6/M^3.
- Delta(E_j) = -16(4a^3+27b^2) = -2985984 p^6/M^3.
- v_p(Delta)=6, v_p(j)=-6: split multiplicative reduction at p, local Tate parameter q with v_p(q)=6.
- M is coprime to p, odd, and M = 1 mod 3; the primes 1009,50833,1799579,64860221162029 are the potential-good additive primes; their semistabilization is a finite extension of degree with prime factors 2,3.
- At 2,3 the minimal model is good: j is a p-adic unit at 2,3 and j mod 2,3 is neither 0 nor 1728 (the nonminimal Delta factors cancel in the minimal model). This is task-198's local computation.

The rational equation (1.2) is an explicit Weierstrass equation. An integral model can be obtained by the standard scaling x=u^2 X, y=u^3 Y with u=M; it has huge coefficients and is not needed here.

## 2. E[41], its 41-division polynomial, and K

For E: y^2=x^3+a x+b, define division polynomials psi_n by

    psi_0=0, psi_1=1, psi_2=2y,
    psi_3=3x^4+6a x^2+12b x-a^2,
    psi_4=4y(x^6+5a x^4+20b x^3-5a^2 x^2-4ab x-8b^2-a^3),
    psi_{2m}=psi_m(psi_{m+2} psi_{m-1}^2 - psi_{m-2} psi_{m+1}^2)/(2y),
    psi_{2m+1}=psi_{m+2} psi_m^3 - psi_{m-1} psi_{m+1}^3.        (2.1)

For n odd, psi_n is a polynomial in x of degree (n^2-1)/2 with leading coefficient n. Thus psi_41 is an explicit polynomial in x of degree (41^2-1)/2=840 with leading term 41 x^840, with coefficients obtained by exact iteration of (2.1) using a=3/M,b=2/M. Its roots are the x-coordinates of the nonzero 41-torsion points (paired by +/-, so 820 points/2? degree 840 = (1681-1)/2; the 41^2-1 nonzero points have 840 x-values, each shared by P and -P).

The full expansion of psi_41 is a finite exact computation; it is not printed here because the coefficients have thousands of digits. This is the first missing explicit computation.

E[41] as a finite etale group scheme over F (char 0) is

    E[41] = Spec F[x,y]/( y^2-x^3-a x-b, psi_41(x) ),
    group law induced by E.                                                (2.2)

Let F=Q(i,E[6],F_sem) as in task-198 (F_sem the semistabilization at M and 2,3; F/Q Galois, 41 does not divide [F:Q], E[2],E[3] full over F, i in F). Define

    K := F(E[41]),   X_K := E_K minus {O_K}.                    (2.3)

K/F is finite Galois because E[41] is a Galois module. The x-coordinates of E[41] generate a subfield of K; the y-coordinates are determined by y^2=x^3+a x+b, and K is the splitting field of psi_41 times these quadratic extensions. A defining polynomial of K, [K:F], and the mod-41 image are not computed; these are the second, third and tenth missing computations.

At p=12301 the local E[41]-extension is explicit at the level of uniformizers:
- q is the actual Tate parameter with v_p(q)=6 and q/p^6 in 1+p^6Z_p.
- Since p=1 mod41 and p does not divide 82, q has an 82nd root in Q_p; write qhat=q^{1/82}=pi^3 v with v in 1+pZ_p, pi^41=p. (Task-198 exact.)
- The E[41] field over F_p is obtained by adjoining q^{1/41}=pi^{6/41}? Careful: q has valuation 6; q^{1/41} has valuation 6/41, and pi=q^{1/82} has valuation 3/41? The local normalization uses pi with pi^41=p and qhat=pi^3 v. The E[41] Kummer extension is generated by qhat^{2}=q^{1/41}? Since qhat=q^{1/82}, qhat^2=q^{1/41}; qhat^82=q; the 41-torsion points require q^{1/41}=qhat^2=pi^6 v^2, which is already in F_v(pi); hence K_v/F_v is the totally ramified extension generated by pi with pi^41=p u? The exact relation q=pi^6 v^2 gives pi^41=p u with u a 41st power? In task-198 e=41,f=1 and b=3. For the explicit K_v, pi is a uniformizer with pi^41=p u (u in Z_p^x); the unit u is determined by q and v; e=41,f=1.
- The local cusp/epsilon at p uses this pi; no arbitrary uniformizer is chosen beyond the source normalization.

## 3. X_K and the quotient stack C_K

X_K is the affine curve E_K minus O, i.e. the spectrum of the coordinate ring of E_K localized away from the origin; a standard affine piece is y^2=x^3+a x+b with the point O at infinity. Concretely, E minus O is covered by the affine y^2=x^3+a x+b; the puncture is the missing point at infinity.

E[41](K) acts on E_K by translation P: (x,y) -> P+(x,y), with the group law on (1.2). This action is free on E_K (translation by a nonzero torsion point has no fixed point) and preserves X_K. Define

    C_K := [ X_K / E[41] ].                                    (3.1)

This is the quotient stack/gerbe of the free action. Its local type at the cusp is (1,41-tors)^pm as in IUT I Def3.1(d); the inertia at the cusp is mu_41. The source-level definition is complete; an explicit coarse equation requires the invariant ring of the translation action, equivalently the 41-isogeny

    E_K -> E_K/E[41],                                          (3.2)

whose kernel is E[41]. Velu's formulas give the coarse equation from psi_41:

    X = x + sum_{P in E[41]\{O}} ( x(x,y;P) - x(P) ), etc.,

with the standard Velu sums; the resulting curve E'_K and the quotient map are explicit only after psi_41 is expanded. This is the missing coarse C_K equation.

The stack itself is not a variety: it is a mu_41-gerbe over the coarse quotient (with possible additional stacky cusp structure); its explicit presentation as a quotient groupoid [X_K/E[41]] is (3.1), but a presentation by equations/stacky charts is not computed. The local formal neighborhood of the cusp has the type (1,Z/41)^pm; a local equation for this orbicurve is the standard quotient of a disc by mu_41, but its global glueing to E'_K is missing.

## 4. C_F and the K-core

E[41] is a finite etale group scheme over F (not necessarily constant). It acts on X_F = E_F minus O_F by translation; the quotient stack

    C_F := [ X_F / E[41]_F ]                                  (4.1)

is an F-stack, and the base change C_F x_F K is C_K. This is the required K-core relation. The explicit descent data are a 1-cocycle for the Galois action of Gal(K/F) on E[41](K) and on the quotient (3.1); the F-form C_F exists by Galois descent of the stack C_K. Writing explicit C_F equations requires the descent cocycle and a coarse F-model of E'_K; neither is computed. This is the fourth missing computation.

## 5. V section and Vbad

After the construction of task-198:
- E_j has bad finite primes {2,3,p=12301} and the four primes of M.
- At 2,3 the minimal model is good; at the M-primes reduction is potential good additive and becomes good after F_sem; at p reduction is multiplicative I_6 and remains bad in every extension.
- Therefore, over F=Q(i,E[6],F_sem), the bad finite set is V_mod={p=12301}. The section V: V(K) -> V_mod selects one place of K over p; V_bad=V. The local K_v has e=41,f=1, pi^41=p u, qhat=pi^3 v, q-order b=3, and 41 does not divide b. The C_v local type is (1,Z/41)^pm, and epsilon_v is the canonical-generator cusp.

What is explicit: the local place at p is described by the local field F_p(pi), the uniformizer pi, the q/qhat data, and the cusp type. What is missing: a global equation for K, hence an actual K-place over p (the section V as a concrete place), and the explicit local model of C_v over that place. The V section exists by the source definition but is not numerically instantiated.

## 6. epsilon cusp

The cusp epsilon is the puncture O of X_K; on the coarse E_K it is the origin. A local parameter at O is t=x/y (or 1/y); the local equation of E_j at infinity is standard. In the quotient C_K the cusp has local type (1,Z/41)^pm and epsilon_v at bad p is the cusp arising from the canonical generator of Zhat. The origin/cusp is source-defined; an explicit coordinate on the quotient stack requires the quotient map (3.2) and the mu_41 action at the cusp, which is missing. This is the fifth missing computation.

## 7. Exact missing computations (prioritized)

1. Expand psi_41(x) for a=3/M,b=2/M (degree 840) exactly; factor it over F; determine the irreducible factors and K=F(E[41]) as a number field with defining equations. Compute [K:F].
2. Compute the 41-isogeny E_K -> E_K/E[41] by Velu from psi_41; get the coarse quotient equation and the quotient map; from it obtain the coarse moduli equation of C_K and the local cusp equation.
3. Compute the Galois 1-cocycle/descent data defining C_F from C_K; write explicit C_F equations over F.
4. Compute the global K-places over p and the section V; compute the local model of C_v at p and the canonical cusp coordinate.
5. Verify mod-41 image contains SL2(F41) (or identify the exact finite-index subgroup); this is clause (c).
6. Verify stable reduction/semistabilization at the four M-primes (potential good; exact Kodaira types) and the exact F_sem degree; ensure 41 not divide [F:Q].
7. Complete the remaining source data: BPS/Theta-gluing, target column, normalization; these are outside the curve/torsion construction.

## 8. Actual / conditional / missing

Actual exact:
- E_j: y^2=x^3+3/M x+2/M, M=1728p^6-1=1009*50833*1799579*64860221162029; j=1/p^6; Delta=-2985984 p^6/M^3; v_p(Delta)=6.
- psi_41 recursion, degree840, leading term 41x^840; E[41] definition (2.2).
- F=Q(i,E[6],F_sem), K=F(E[41]), X_K; C_K quotient stack definition; C_F K-core; V_mod={p}; epsilon origin/canonical cusp.
- Local p: e=41,f=1,b=3,qhat=pi^3 v, v in 1+pZ_p; 41 not divide b.

Conditional/standard:
- Semistabilization at M-primes and 2,3 with F_sem degree only 2,3; exact Kodaira types not computed.
- C_K/C_F/epsilon explicit equations; K field; V global places; mod41 image.
- Complete C and target data.

Missing: the explicit computations listed in section 7.

## 9. Conclusion

The equation E_j, the 41-division recursion, the quotient stack definitions, the V/Vbad specification and the epsilon cusp are explicit at the source-level skeleton, and the local p data e=41,f=1,b=3 are exact. A fully explicit C_K/C_F/V/epsilon equation is not obtained: it requires the degree-840 psi_41 expansion, the 41-isogeny/coarse quotient, descent data, and global K places. No arbitrary data or U/B normalization is introduced; the missing items are exact computations.

Only C9-EXPLICIT-C-EQUATIONS-20261025.md written. Natural-language self-review done; Lean/Project/kernel/comparator/independent review not run. target_accepted=false; P6 open.
