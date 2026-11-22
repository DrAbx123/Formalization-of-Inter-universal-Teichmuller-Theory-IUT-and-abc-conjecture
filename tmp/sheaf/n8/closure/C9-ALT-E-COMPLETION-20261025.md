# C9 completion of the alternative E: source-level C and local-type check

Task: task-212 (C9-ALT-E-COMPLETION-20261025). Owner: logdescent. Date: 2026-10-25. SHEAF stage1 construction/audit; only this file written; no Lean/Project/target/other-owner edits. Consumer: n8-c9-output-region-source-route P6. P6 unproved; target_accepted=false.

Inputs: C9-ALTERNATIVE-E-PROFILE-20261025.md (SHA256 6E231A5D7EB23B8ACBB78E8FAEB21C6C3C8733829955628719CE1CBB8CD5A5AC); C9-EJ-COMPLETION-20261025.md (task-198); IUT I Def3.1(a)-(f); IUT III Def1.1/Prop1.2/Thm3.11; C9-IND1-GLOBAL constraints.

## 0. Verdict

The actual curve E: y^2=x^3+4x-2437249 from task-197 admits a source-level completion skeleton, but it is NOT in the C9 b=3 local profile.

Actual local data:
- p=12301: E has split multiplicative reduction, v_p(Delta)=1. The Tate parameter has v_p(q)=1, not 6. Hence the formal TAME exponent from q=pi^{2bl} is b=41*v_p(q)/(2l)=41/(2*41)=1/2, not an integer 3. The object qhat=q^{1/(2l)}=q^{1/82} has valuation 1/82 and is not an integral power of the local uniformizer; in the E[41]-field K_v, q^{1/41}=pi is a uniformizer, but qhat=pi^{1/2} is not in K_v.
- Therefore the C9 local hypotheses e=41, f=1, b=3, q=p^6 u^6 FAIL at p. The curve has local type I_1 at p, not the b=3/I_6 profile. It can still be a complete-C candidate with a different local type, but it cannot feed the C9 b=3 compensation formulas.

Other local data:
- 19 and 686229757: v=1 in Delta, multiplicative I_1; stable; v_q(q)=1; no integer b=3.
- 2: additive potential good (v_2(Delta)=4, v_2(j)=14>=0); after a finite 2-power extension F2, good; not bad in Vbad.
- No other bad primes.

Def3.1 status:
(a) satisfied with F containing i (F0 contains zeta_12).
(b) stable reduction after F=F0F2; field of moduli Q; F/Q Galois degree prime to 41; full E[6] over F0 subset F. Satisfied at source-skeleton level.
(c) l=41; K=F(E[41]) exists; l is prime to residue characteristics of Vbad (19,686229757,12301 are not 41); but the image containing SL2(F41) is NOT verified, and the p q-order/b=3 C9 hypothesis fails. Thus (c) is conditional (image) and the C9 b=3 sub-hypothesis is false.
(d) C_K=[X_K/E[41]] type (1,41-tors)^pm and C_F over F are defined at source/stack level; explicit equations/stacky points are missing.
(e) V/Vbad can be defined as a section over the bad rational primes {19,686229757,12301}; explicit global places require K equations, not supplied.
(f) epsilon as origin/canonical cusp is defined source-level; explicit cusp coordinates missing.

Conclusion: the E has an actual source-level stable-reduction skeleton and a different local type (I_1 at its bad places), but it does NOT satisfy the C9 b=3 local hypotheses. A complete C for the C9 b=3 route remains missing; O1 is not closed. No arbitrary curve or local parameter was introduced.

## 1. Curve and exact invariants (task-197)

E: y^2 = x^3 + 4x - 2437249 over Q.

- Delta = -2566158921220528 = -16 * 12301 * 19 * 686229757.
- j = 442368 / 160384932576283 = 442368 / (12301*19*686229757).
- Bad finite primes over Q: {2, 19, 12301, 686229757}.
- At p=12301: split multiplicative; v_p(Delta)=1; reduction roots 1837 and 5232 with double root 5232 and split tangent; v_p(j)=-1.
- At 19, 686229757: v(Delta)=1, multiplicative I_1.
- At 2: v_2(Delta)=4, v_2(j)=14>=0, additive potential good; no multiplicative q.
- Elsewhere good.

## 2. Field F0, F2, and F

F0 := Q(zeta_12, E[6]).
- E[6] is Galois over Q; Galois group embeds in GL_2(Z/6), order |GL_2(Z/2)|*|GL_2(Z/3)|=6*48=288.
- [Q(zeta_12):Q]=4. Hence [F0:Q] divides 4*288=1152=2^7*3^2, prime to 41; F0/Q Galois.
- F0 contains zeta_12, hence i, and contains all E[2],E[3], hence full E[6].

F2: a finite extension of F0 over which E acquires good reduction at all places over 2. Since v_2(j)=14>=0, E has potential good reduction at 2; the existence of F2 is the standard potential-good-reduction theorem. The exact degree is not computed; its prime factors are only 2 and 3 (2-adic local extension, including possible unramified odd degree 3), so 41 does not divide [F2:F0].

F := F0 * F2 (compositum; take Galois closure if necessary so F/Q is Galois). Then F/Q is Galois, [F:Q] has prime factors only 2,3 (from F0 and F2), hence 41 does not divide [F:Q]. F contains i and full E[6], and E/F has good reduction at 2; at 19,686229757,12301 it has multiplicative reduction; elsewhere good. Thus E/F has stable reduction everywhere.

This F is a source-valid enlargement of Q(zeta_12). Strict F=Q(zeta_12) is impossible for this E: x^3+4x-2437249 is irreducible (2437249=647*3767, no rational root) with nonsquare discriminant -160384932576283, so Q(E[2]) is S3 (nonabelian), not contained in abelian Q(zeta_12). The source clause only requires F/F_mod Galois of degree prime to 41, which F satisfies. If strict Q(zeta_12) is demanded, this E is not a solution.

## 3. E[41], K, X_K, C_K, C_F, V, epsilon

- E[41]: finite etale group scheme over Q (char 0), order 41^2; over F its geometric points are E[41](Fbar).
- K := F(E[41]), the finite Galois extension of F generated by the coordinates of all 41-torsion points. K/F is Galois because E[41] is a Galois module. [K:F] is not computed explicitly (it divides |GL_2(F_41)| times residual factors; depends on the unverified mod-41 image).
- X_K := E_K minus {O_K} (once-punctured elliptic curve over K).
- C_K := [X_K / E[41]]: the quotient stack of X_K by the finite etale group E[41]_K. Its local type at a bad place is (1,41-tors)^pm as in IUT I Def3.1(d). Source-level definition; explicit 41-division coordinates/coarse equations are missing.
- C_F := [X_F / E[41]_F], where E[41]_F is the finite etale F-group scheme; K-core(C_K)=C_F x_F K. This is the required CF and K-core relation at source level. Explicit C_F equations and stacky points are missing.
- V_mod: the bad finite rational primes after semistabilization. E/F has bad finite primes {19, 686229757, 12301} (2 is good after F2), so V_mod={19,686229757,12301}. V is a section V(K)->V_mod: choose one K-place over each of these rational primes. Such sections exist; the choice is part of the C data and is not an arbitrary curve. V_bad=V (all selected places are bad). At each such place E has multiplicative reduction; the covering E[41]->E gives local C_v type (1,Z/41)^pm at the bad cusp.
- epsilon: the cusp of C_K arising from the origin O of E_K (the puncture of X_K), with the canonical-generator cusp at bad v. Source-level definition; explicit coordinates require E_K/C_K equations, missing.

## 4. Local p data and the b=3 check

At p=12301:
- E has split multiplicative reduction (exact tangent calculation; task-197).
- v_p(Delta)=1, v_p(j)=-1. Therefore the Tate parameter q in Q_p satisfies v_p(q)=1 and q=p u with u in Z_p^x.
- From task-197 exact Newton computation:
  u = 5168865309000495801384673649029265377681057827317425313600722852686093890527523842 mod p^20,
  q = p u mod p^21,
  q/p = 5348 + 1516 p + 7385 p^2 + 2824 p^3 + 41 p^4 + ... (p-adic digits).
- The local E[41]-extension is obtained by adjoining q^{1/41}; since q=p u and p≡1 mod41 (mu_41 subset Q_p), q^{1/41} has valuation 1/41 and K_v/F_v is totally ramified of degree e=41 with f=1. Set pi=q^{1/41}; then q=pi^{41}.
- In the C9 tame model q_Tate=qhat^{2l} with qhat=pi^b and l=41. If q=pi^{41}, then 2 l b = 41, so b=41/(2*41)=1/2. This is not an integer. Equivalently qhat=q^{1/82}=pi^{1/2} is not in K_v (it is a square root of a uniformizer, requiring a quadratic extension). Thus the C9 b=3 and q=p^6 u^6 hypotheses FAIL at p.
- The local type is I_1 (v(q)=1), not I_6. The C9 b=3 local type (1,Z/41)^pm with qhat=pi^3 is not realized by this E.

At 19 and 686229757:
- v_q(Delta)=1, multiplicative I_1; v_q(q)=1; e=41, f=1 for the E[41] extension; q=pi^{41}, formal b=1/2, not 3. These places are in V_bad and contribute local I_1, not the C9 I_6/b=3 profile.
- l=41 is prime to their residue characteristics (19,686229757 !=41), but the C9 b=3 local hypotheses are not met.

At 2:
- additive potential good; after F2 good; removed from V_bad; no q-order.

Clause (c) q-order condition:
- IUT I Def3.1(c) requires l=41 prime to the residue characteristics of Vbad and to the orders of the q-parameters at V(F)_bad. Residue characteristics 19,686229757,12301 are not 41.
- The actual q-parameters of this E have valuation 1, not 6; the formal qhat exponent is 1/2. The C9 b=3 order condition (qhat order 3) does not hold. The exact clause-(c) q-order in the source sense requires the actual q-parameter order computation; in any case the b=3 C9 hypothesis is false.
- The mod-41 image containing SL2(F41) is not computed; clause (c) remains conditional for that reason too.

## 5. Def3.1 clause table

| Clause | Status for this E/F |
|---|---|
| (a) F contains sqrt(-1) | SATISFIED: zeta_12 in F0 subset F |
| (b) XF once-punctured, stable reduction, field of moduli Q, F/F_mod Galois degree prime to 41, full E[2]/E[3] | SATISFIED at source-skeleton level with F=F0F2 (F larger than Q(zeta_12)); full E[6] over F0; stable after F2; degree prime to 41. Strict F=Q(zeta_12) fails for this E. |
| (c) image contains SL2(F41), K=F(E[41]), l prime to residue chars and q-orders | PARTIAL: K exists; residue chars okay; image not computed; C9 b=3 q-order fails (v(q)=1, b=1/2). |
| (d) CK type (1,41-tors)^pm over K, K-core CF x K | SOURCE-LEVEL DEFINED: quotient stacks; explicit equations/stacky points missing. |
| (e) V section, Vbad, C_v type, local models | SOURCE-LEVEL DEFINED: Vbad={19,686229757,12301}; section exists; explicit places/local models missing. |
| (f) epsilon cusp, canonical generator at bad | SOURCE-LEVEL DEFINED: origin/canonical cusp; explicit coordinates missing. |

C9 local hypotheses:
- e=41, f=1, p>e+1, tame: yes at p (and at other multiplicative bad primes).
- b=3, q=p^6 u^6, qhat=pi^3 v: NO; actual q has valuation 1, b=1/2, qhat not in K_v.
- Therefore the C9 b=3 formulas cannot be applied to this E. This is the decisive local-profile mismatch.

## 6. Actual / conditional / missing

Actual exact:
- E/Q, j=442368/160384932576283, Delta, bad set {2,19,12301,686229757}.
- p=12301 split multiplicative I_1, v(q)=1; q mod p^21 and p-adic digits from task-197.
- 19,686229757 multiplicative I_1; 2 additive potential good.
- F0=Q(zeta_12,E[6]) degree divides1152=2^7*3^2; F=F0F2 with F2 a finite 2,3-power potential-good extension; F/Q Galois, 41 not divide [F:Q]; E/F stable.
- Source-level K=F(E[41]), X_K, C_K, C_F, V/Vbad, epsilon definitions.

Conditional/standard:
- Existence and exact degree of F2 (potential good reduction at2); not computed.
- C_F/C_K explicit quotient/stack equations; not constructed.
- K/F degree and exact 41-division field; not computed.
- mod-41 image containing SL2(F41); not verified.
- Clause (c) q-order in the source sense; not fully computed; at any rate b=3 fails.
- Exact V section places (requires K equations).

Missing:
- Explicit E[41] coordinates/field equations; C_F/C_K/V/epsilon equations.
- mod41 image.
- Complete C BPS/Theta/gluing/target column/weights.
- C9 b=3 local profile; this E is I_1, not I_6.
- Target/P6.

## 7. Conclusion

The actual E from task-197 can be completed to a source-level stable-reduction skeleton with F=F0F2, K=F(E[41]), C_K/C_F quotient stacks, V section and epsilon cusp. It verifies Def3.1(a)-(b) with a larger F and gives source-level (d)-(f). It does not verify clause (c) (SL2 image) and, decisively, it does not satisfy the C9 b=3 local hypotheses: v_p(q)=1, not 6; formal b=1/2, not 3; qhat=pi^{1/2} not in K_v. Therefore this E cannot be used for the C9 b=3 compensation route. It is a valid alternative complete-C candidate with local type I_1, not a C9 b=3 complete C.

No arbitrary curve/local parameter was chosen; the mismatch is a consequence of the actual E and is reported as a negative result, not patched by changing q.

## 8. Acceptance

Only C9-ALT-E-COMPLETION-20261025.md written. Natural-language/exact-integer self-review done; explicit E[41]/C equations and SL2 computation not performed; Lean/Project/kernel/comparator/independent review not run; not applicable. target_accepted=false; P6 open.
