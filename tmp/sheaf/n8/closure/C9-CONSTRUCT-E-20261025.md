# C9 O1: construct actual E/F, or prove the q=p^6 candidate impossible

Task: task-191 (C9-CONSTRUCT-E-20261025). Owner: logdescent. Date: 2026-10-25. SHEAF stage1 natural-language/exact-computation research. Only this file written. No Lean/Project/target/other-owner edits. Consumer: n8-c9-output-region-source-route P6. P6 unproved; target_accepted=false.

Inputs: C9-FULLC-CONSTRUCTION-ATTACK-20261025.md (task-183; SHA256 2e37310dd3eb96135d8e13dc7ce7205a6f43c85f21720daa28bab3745d6d08bd), C9-AUDIT-FULLC-CONSTRUCTION-20261025.md (task-188), C9-TAME-LOG-DOMAIN-20261025.md (SHA256 23b3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06), IUT I Def3.1, and the task-183/188 local q discussion.

## 0. Verdict

The task-183 rational-j candidate does not exist. q=p^6 is a rational (hence algebraic) p-adic number with 0<|q|_p<1. The p-adic Mahler-Manin theorem (Barré-Sirieix-Diaz-Gramain-Philibert, Invent. Math. 124 (1996), 1-9) states that for algebraic q with 0<|q|_p<1, the p-adic modular invariant J(q)=q^{-1}+744+196884q+... is transcendental over Q. Therefore J(p^6) is not rational, and not algebraic at all.

Tate uniformization for an elliptic curve E over a number field F with split multiplicative reduction at a place v over p gives j(E)=J(q_v), where q_v is the Tate parameter. Since j(E) is an algebraic number, q_v cannot equal p^6. Hence no elliptic curve over any number field has a place over p=12301 with split multiplicative reduction and Tate parameter exactly p^6. This is stronger than merely "no field of moduli Q curve": it rules out the q=p^6 condition for all E/F, independently of full E[2]/E[3], stable reduction elsewhere, or mod-41 image.

Consequences:
- The task-183 candidate j(p^6) rational is invalid. The q-expansion is p-adic; its value at q=p^6 is p-adic and transcendental (over Q), not a rational j.
- No actual E/F satisfying the task-191 conditions (field of moduli Q or any number field, bad at p=12301, local Tate parameter p^6) exists. The remaining required data (Weierstrass equation, discriminant, bad set, E[6], mod-41 image) are not merely missing: they are incompatible with q=p^6.
- The obstruction is the candidate-profile q=p^6, not a proof that no complete C exists. A complete C with a different local q is not constructed in this file. O1 remains open for such alternatives; P6 is not advanced.

The no-go is conditional on the p-adic Mahler-Manin theorem as a literature input. It is not a computation-only result. Without that theorem, the exact computation below only shows the first p-adic digits have no small rational reconstruction; it does not by itself prove irrationality.

## 1. What task-183 assumed and what is actually true

Task-183 wrote j(q)=q^{-1}+744+196884q+... and substituted q=p^6, treating the result as a rational j. That is a type error:
- For complex q, the series converges only for |q|<1; q=p^6 is huge, so the complex series does not converge.
- For p-adic q, |q|_p=p^{-6}<1, so the series converges in Q_p; its value J(p^6) is a p-adic number, not an algebraic/rational number.
- A p-adic number being given by a convergent series with rational coefficients does not make it rational. The p-adic Mahler-Manin theorem gives transcendence of J(q) for algebraic q in the convergence domain, so J(p^6) is not rational.

The task-188 audit corrected the local Tate parameter to q_Tate=p^6 u^6 when pi^41=p u:
q_Tate=qhat^{2l}=pi^{246}=(pi^41)^6=p^6 u^6.
Thus exact q=p^6 requires u=1 (e.g. K=Q_p(p^{1/41})). With u=1, q is rational and the Mahler-Manin contradiction applies. With u!=1, q=p^6u^6 is a p-adic number that need not be algebraic; the theorem does not apply, and no actual E is supplied either. The task-191 condition q=p^6 selects u=1, which is impossible.

## 2. Exact local arithmetic (Python, exact integers)

Computed with exact integer arithmetic:
- p=12301 is prime (trial division by all integers 2..110).
- p mod 12 = 1; p mod 41 = 1.
- p^6 = 3464515518466761109423801.
- The modular invariant has integer q-coefficients
  J(q)=q^{-1}+744+196884 q+21493760 q^2+864299970 q^3
       +20245856256 q^4+333202640600 q^5+...
  (computed exactly from E4^3/Delta with E4=1+240 sum sigma_3(n)q^n, E6=1-504 sum sigma_5(n)q^n, Delta=(E4^3-E6^2)/1728).

Substituting q=p^6:
J(p^6)=p^{-6}+744+196884 p^6+21493760 p^{12}+864299970 p^{18}
       +20245856256 p^{24}+333202640600 p^{30}+...
p^6 J(p^6)=1+744 p^6+196884 p^{12}+21493760 p^{18}+864299970 p^{24}
       +20245856256 p^{30}+333202640600 p^{36}+...    (2.1)

This is an exact p-adic expansion; every coefficient is an integer and the n-th term after the leading 1 has p-adic valuation at least 6n. The first terms are not rational numbers. A rational-reconstruction test modulo p^42 returned numerator and denominator of size about p^21 (the continued-fraction convergent), i.e. no rational with small height; this is only a numerical sanity check, not the proof. The proof is the p-adic Mahler-Manin theorem.

## 3. Mahler-Manin input and the no-go

Theorem (p-adic Mahler-Manin; Barré-Sirieix, Diaz, Gramain, Philibert, Une preuve de la conjecture de Mahler-Manin, Invent. Math. 124 (1996), 1-9). Let q be an algebraic number with 0<|q|_p<1. Then J(q) is transcendental over Q.

Apply q=p^6:
- q=p^6 is rational, hence algebraic.
- 0<|q|_p=p^{-6}<1.
- Therefore J(p^6) is transcendental over Q (in particular not rational and not algebraic).

No-go proposition. Let E/F be an elliptic curve over a number field F, and let v be a finite place of F over p=12301 at which E has split multiplicative reduction with Tate parameter q_v. Then q_v cannot equal p^6.

Proof. If q_v=p^6, Tate uniformization over F_v gives j(E)=J(q_v)=J(p^6). But j(E) is an algebraic number (E is defined over the number field F). This contradicts the transcendence of J(p^6) over Q, hence over any algebraic extension. For nonsplit multiplicative reduction, the Tate parameter is defined over the quadratic unramified extension; the same j=J(q) identity holds there, so q_v=p^6 is again impossible. If reduction is good or additive, there is no Tate parameter q_v in the required sense (and additive reduction is not stable). Therefore no E/F with a place over p having stable multiplicative reduction and Tate parameter p^6 exists.

In particular, no E/F satisfies the task-191 list: field of moduli Q (or any number field), stable reduction everywhere, bad reduction at p=12301, local Tate parameter p^6, full E[2]/E[3], mod-41 image containing SL2(F41). The contradiction uses only the local q and algebraicity of j; the other conditions are irrelevant. This is a proved impossibility for the candidate profile, not a missing computation.

## 4. What about field F=Q(zeta_12) and the other clauses?

Field-level facts (actual, independent of the no-go):
- IUT I Def3.1(a) requires sqrt(-1) in F; (b) requires full E[2]/E[3] over F. Full E[3] forces mu_3 in F; with sqrt(-1) this forces Q(zeta_12) subset F. F=Q(zeta_12) has degree phi(12)=4, Galois, and 41 does not divide 4, satisfying the degree-prime-to-41 part.
- p=12301 is prime, p mod12=1, so p splits completely in Q(zeta_12) (four places over p); p mod41=1, so mu_41 subset Q_p and the tame K=Q_p(pi), pi^41=p, exists.
These are actual necessary local/field facts. They do not construct E and do not rescue q=p^6.

The other task-191 conditions are now moot for the q=p^6 candidate:
- Stable reduction everywhere: impossible simultaneously with q=p^6 at p, because q=p^6 already impossible at such a multiplicative place. (Stable reduction elsewhere is not the issue.)
- Full E[2]/E[3] over F=Q(zeta_12): no E with the local q exists; no torsion computation can change that.
- Bad reduction at 12301: required, but the local Tate parameter would be p^6, impossible.
- mod-41 image containing SL2(F41): not needed; no E exists for the local reason. The image condition cannot be satisfied by a nonexistent curve.

If one drops q=p^6 and asks for an actual E with the other properties, that is a different task; this file does not construct it. The no-go only blocks the exact local candidate, not all complete C.

## 5. Why a LMFDB/Cremona search is not the decisive tool

A LMFDB/Cremona search can enumerate E/Q with bad reduction at 12301, but:
- it cannot produce an E with q=p^6, because the no-go rules out every E over every number field with that local parameter;
- any curve found with bad reduction at 12301 has a Tate parameter q_v determined by its j, and q_v is not forced to be p^6; indeed the exact p^6 condition is the exceptional equation j=J(p^6), whose right side is transcendental.

Thus no Weierstrass equation, discriminant, conductor, bad set, E[6] field, or mod-41 matrix is computed here for the candidate: the candidate is impossible. A search for alternative curves with different local q remains a separate construction problem and is not satisfied by selecting an arbitrary E.

No arbitrary curve, bad set, or local parameter is introduced.

## 6. Actual / conditional / missing

Actual exact arithmetic:
- p=12301 prime; p mod12=1; p mod41=1; p^6 exact; F=Q(zeta_12) field constraint; p splits; local K=Q_p(pi), pi^41=p, exists.
- q_Tate=qhat^{2l}=p^6u^6; exact q=p^6 requires u=1 (task-188).
- J(q) coefficients and p-adic expansion (2.1), exact integer computation.
- If E has split multiplicative reduction at v over p and q_v=p^6, then j(E)=J(p^6) in F_v.

Conditional on the cited p-adic Mahler-Manin theorem:
- J(p^6) is transcendental over Q; hence not equal to algebraic j(E); hence no E/F with q_v=p^6.
- Therefore no actual E for the task-191 q=p^6 profile; O1 candidate profile is impossible.

Missing / conditional if the Mahler-Manin theorem is not accepted:
- A proof that J(p^6) is irrational without transcendence theory; not supplied.
- If one only assumes numerical non-rationality, the no-go is heuristic, not proved.
- An actual E with all task-191 conditions except q=p^6 (different local q) is not constructed; O1 remains missing for that alternative.
- Complete C, S_bad, per-p local types, q/BPS/gluing, target column, TC-A..TC-H+TC-S, archimedean data: all still missing.

## 7. Verdict for O1

- The q=p^6/j rational candidate of task-183 is refuted: J(p^6) is p-adic transcendental, not rational. No elliptic curve over a number field has Tate parameter p^6 at a place over p=12301.
- Consequently the exact task-191 curve (field of moduli Q or larger, stable reduction, full E[6], bad at 12301, local q=p^6, mod-41 SL2) does not exist. This is a proved no-go for that candidate profile, not a construction and not a proof that all complete C are impossible.
- A complete C with a different local q is not constructed; O1 remains open. No target containment or global inequality is claimed.

## 8. Sources and acceptance

- K. Barré-Sirieix, G. Diaz, F. Gramain, G. Philibert, Une preuve de la conjecture de Mahler-Manin, Invent. Math. 124 (1996), 1-9 (p-adic Mahler-Manin theorem).
- IUT I May 2020, Definition 3.1(a)-(f); the field Q(zeta_12) necessary condition.
- C9-FULLC-CONSTRUCTION-ATTACK-20261025.md (task-183) and C9-AUDIT-FULLC-CONSTRUCTION-20261025.md (task-188), especially the q_Tate=p^6u^6 correction.
- C9-TAME-LOG-DOMAIN-20261025.md local tame model and q_Tate=qhat^{2l}.
- Exact Python integer computation described in section 2 (no floating-point assertion).

Acceptance: only C9-CONSTRUCT-E-20261025.md written; no Lean/Project/target/other-owner edits. Natural-language self-review done; Lean/Project/kernel/comparator/independent review not run; not applicable. target_accepted=false; P6 unproved.
