# C9 attack: construct or obstruct a complete C for F_mod=Q

Task ID: task-183 / C9-FULLC-CONSTRUCTION-ATTACK-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Nature: natural-language construction attack only; no Lean/Project edits; no target changes; no arbitrary data; only this file written.

## 0. Inputs and status

- C9-FULLC-WEIGHTS-ATTACK-20261025.md (task-169), SHA256 142b63c7e22da681efb6cfc2e3c45e0a58c0bb5135f4e995fc35b1e488cc249c.
- C9-GLOBAL-ASSEMBLY-CORRECTED2-20261025.md (task-176), SHA256 83d33415f6a046e49e4c1a734095ae502a3dc94562a563af506ea640ebb5d781.
- C9-TAME-LOG-DOMAIN-20261025.md (TAME), SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06.
- PaperInitialThetaData.lean (transport projections, read-only), SHA256 df4c14a79f4d686ee9f9f6448577d96e3dc7d35c24d4a60c10e4fc933c48a484.
- IUT I May 2020, Definition 3.1(a)-(f), pp.61-64; IUT III May 2020, Def1.1, Prop1.2, Thm3.11; the page/line locations already checked in the frozen C9 files.

Binding corrections remain in force: corrected donor H=Phi^{-1}(Sp_{2g}(Z_p)); rho is not a homomorphism; mapping-class source; basis alignment inferred; trace target Tr_{K/K^{d=1}}; TAME (11)-(14) are not a target proof; full Ind1 is the procession automorphism group; TC-A..TC-H plus TC-S are required; full barGamma branch is undetermined; archimedean actual r_inf is missing.

This file does not construct a complete C. It specifies the exact candidate skeleton and isolates the first non-constructible source object. The distinction actual/conditional/missing is kept throughout.

## 1. Required complete C data

IUT I Definition 3.1 requires the collection

    (F/F, XF, l, CK, V, Vbad_mod, epsilon),                      (1.1)

with, in particular:

(a) F a number field with sqrt(-1) in F; F an algebraic closure of F.
(b) XF a once-punctured elliptic curve over F admitting stable reduction over all nonarchimedean places; F_mod the field of moduli of XF; F/F_mod Galois of degree prime to l; the 2- and 3-torsion points of the elliptic curve EF are rational over F.
(c) l>=5 prime, image of G_F -> GL2(F_l) on l-torsion contains SL2(F_l); K the finite Galois extension of F cut out by the kernel; l prime to residue characteristics of Vbad_mod and to the orders of the q-parameters at V(F)_bad.
(d) CK a hyperbolic orbicurve of type (1,l-tors)^pm over K with K-core CF x_F K, giving XK/XF and CK/CF.
(e) V subset V(K) mapping bijectively to Vmod=V(F_mod), a section of V(K)->Vmod; Vbad=V inters V(K)bad; at v in Vbad, C_v is of type (1,Z/lZ)^pm; local models over K_v.
(f) epsilon a cusp of CK arising from a nonzero element of Q; at bad v, epsilon_v is the cusp from the canonical generator of Zhat.

A complete C additionally needs the actual Bad/Good sets, q-parameters/BPS data, Theta-gluing, target column, and normalization used by C9. None of these is a free parameter; all must come from the cited source objects.

## 2. Candidate field and local parameters

For F_mod=Q the natural minimal choice is constrained by the 2- and 3-torsion clause:

- sqrt(-1) in F is required by (a).
- E[3] rational over F implies the determinant character chi_3 of G_F on E[3] is trivial, hence Q(zeta_3)=Q(sqrt(-3)) is contained in F. Indeed if E[3] is fixed by G_F, the whole mod-3 representation is trivial on G_F, so its determinant chi_3 is trivial on G_F.
- Therefore F must contain the compositum Q(i,sqrt(-3))=Q(zeta_12), of degree 4 over Q. A choice F=Q(i) alone is impossible for clause (b); this is the first field-level constraint.
- Q(zeta_12)/Q is Galois of degree 4, prime to l=41. Thus the field-level constraint is satisfiable by F=Q(zeta_12) (or a larger extension of degree prime to 41).

The first candidate skeleton is therefore:

    F_mod=Q,  F=Q(zeta_12),  l=41,  p=12301,                 (2.1)
    e=41, K/Q_p tame totally ramified, pi^41=p u,             (2.2)
    b=3,  qhat=pi^3,  q_Tate=qhat^{2l}=p^{6}.                  (2.3)

Equation (2.3) is forced by the tame local model used in TAME §7: q_Tate=qhat^{2l}, e=41, qhat=pi^3, hence q_Tate=p^{2b}=p^6. The local q has p-adic valuation 6, and 41 is prime to 6; p=12301 is odd and p=1 mod 41, so mu_41 is in Q_p and the tame totally ramified local field exists. This valuation check does not by itself verify Clause (c)'s q-order condition; that needs the actual q-parameter order. The local field K=Q_p(pi) has f=1 and O_K=Z_p[pi].

At the level of base places, 12301=1 mod 12, so p splits completely in F=Q(zeta_12); V(F) has four places over p. The section V in Definition 3.1(e) selects one of them; Vbad_mod contains p if E has bad reduction there.

Candidate bad set: S_bad(C) must contain p=12301 and is finite nonempty; its other elements are the bad-reduction primes of the actual elliptic curve E. No set may be chosen arbitrarily. For the uniform profile the weights are

    alpha_p=1 for F_mod=Q,  rho_p=1 at each bad p,             (2.4)

and the local formula q_Tate(p)=p^{2 b_p} applies only where the tame e=41,b_p type holds. Other bad primes require their own e_p,b_p and local types; they cannot be silently set to e=41 or b=3.

## 3. Clause-by-clause status of the candidate

### 3.1 Clause (a): field

F=Q(zeta_12) contains i and sqrt(-3); F/F_mod is Galois of degree 4, prime to 41. This clause is satisfiable at the field level. The actual construction must still specify F as the algebraic closure of F and the embedding F into F; this is formal.

### 3.2 Clause (b): actual curve and torsion

Required: an elliptic curve E/F (XF once-punctured) with

    field of moduli Q, stable reduction over all nonarchimedean places,
    E[2](F) and E[3](F) full, and bad reduction at p=12301.       (3.1)

The field F=Q(zeta_12) is necessary for E[3](F), but it does not supply an E. A natural candidate is a Tate-type specialization with rational j-invariant j(p^6), where j(q)=q^{-1}+744+196884 q+... is the Tate j-function. Such a j is rational, so an E/Q with this j exists abstractly (via the standard j-invariant construction). However:

1. The resulting E/Q need not have bad reduction only at p=12301; its minimal discriminant may contain other primes. The actual bad set is then larger and must be included in S_bad with its own local types.
2. It is not proved that the specialization has the local q=p^6 at p=12301; j determines q only after a local Tate uniformization, and the global equation's minimal discriminant may require a twist.
3. It is not proved that E[2],E[3] are rational over F=Q(zeta_12); the Tate q being a 6th power gives local 6-torsion over Q_p(zeta_12), not global 6-torsion over Q(zeta_12).
4. It is not proved that E has stable reduction over all finite places and field of moduli Q simultaneously with the above.

This is the first actual construction obstruction: no explicit elliptic curve/equation with (3.1) and q=p^6 is supplied by the frozen corpus. The obstruction is a missing actual object, not a proved impossibility.

### 3.3 Clause (c): mod-41 image and q-orders

Given an actual E/F, one must compute the image of G_F in GL2(F_41) and verify it contains SL2(F_41). The candidate F=Q(zeta_12) is quadratic over Q(i); the restriction of a generic E/Q mod-41 image could be large, but no actual E or matrix computation exists. The valuation of q=p^6 is 6, prime to 41, but only if the local q is exactly p^6; Clause (c)'s q-order condition still needs the actual q-parameter order check.

No actual theorem says the Tate specialization satisfying (3.1) also has mod-41 image containing SL2. This is the second missing computation, after the curve itself.

### 3.4 Clause (d): CK and XK

Once E/F and E[41] are actual, K/F is the finite Galois extension cut out by the mod-41 kernel, and CK is constructed from the l-torsion cover as in EtTh; this part is formal from the source and does not need a new arbitrary choice. It cannot be instantiated before E/K are actual.

### 3.5 Clause (e): V section and Vbad

For F_mod=Q, V_mod=V(Q) is the set of rational places; the section V selects one F-place over each rational place. Vbad_mod is a nonempty set of finite rational places; if E has bad reduction at p=12301, p belongs to it. The actual Vbad set is the bad-reduction set of E; it is finite by standard arithmetic. No arbitrary set is allowed.

At each bad p, the q-parameter and local model must be computed from E. For p=12301 the target is e=41,b=3, q=p^6; for any other bad p the e_p,b_p are whatever E gives, and the uniform local formulas may not apply.

### 3.6 Clause (f): epsilon and cusp

The cusp epsilon is chosen from the nonzero Q element of the type (1,l-tors)^pm orbicurve. At bad v, epsilon_v must be the canonical-generator cusp. Formal once CK is actual; no numerical obstruction.

## 4. First construction obstruction (precise)

The first missing object is E/F in clause (b). More precisely, the earliest unconstructed source datum is:

    an actual elliptic curve E over F=Q(zeta_12) (or a larger F) with
    field of moduli Q, stable reduction everywhere, full E[2]/E[3]
    over F, bad reduction at p=12301, and local Tate parameter p^6.   (4.1)

No equation, discriminant, conductor, torsion-field computation, or bad-set enumeration for such an E exists in the frozen corpus. The Tate j(p^6) candidate supplies at most a rational j, not the rest of (4.1).

This obstruction is prior to S_bad, per-p e_p/b_p, q/BPS, row/Theta weights, and the target column: all of those require the actual E. Therefore the complete C is not constructed, and the natural-language contradiction route cannot be instantiated at present.

An attempted shortcut 'take S_bad={12301}' is not allowed: the actual bad set of E need not be a singleton, and no theorem produces E with bad reduction exactly at 12301 and good reduction elsewhere. An attempted shortcut 'take q=p^6 and ignore global bad primes' is also invalid: q is a local parameter, while the global discriminant may have additional primes and the field-of-moduli/torsion conditions are global.

## 5. If a curve E were constructed: what would follow

Assume an actual E/F satisfying (4.1), and let S_bad be its bad-reduction primes in F_mod=Q. Then:

1. Vbad_mod=S_bad, V section, CK/XK and epsilon are constructed by the source clauses; bad set is finite/nonempty.
2. For each p in S_bad one computes e_p,b_p from the local extension K/F and the q-parameter; only the p with tame e=41 are covered by the C9 local formulas.
3. The weights are alpha_p=1, rho_p=1 for the uniform profile; row/Theta weights are rho_p^{j+1}=1 for the covered p.
4. The local Q_p=-b_p/e_p log p and the conditional finite residual D_C=sum d_p log p can be evaluated only after the full S_bad/local types are known.
5. Even then, the target-container conditions TC-A..TC-H and TC-S remain; the corrected donor/basis/full-barGamma issues are independent of the curve construction.

Thus constructing E is necessary but not sufficient for the natural-language contradiction route; it is the first gate.

## 6. Actual / conditional / missing

Actual source-level:

- IUT I Definition 3.1 clauses and the field constraint F must contain Q(zeta_12) for full 2- and 3-torsion over F.
- F=Q(zeta_12) is Galois of degree 4 prime to 41; p=12301 splits completely; mu_41 in Q_p; the tame local field Q_p(pi), pi^41=p, exists.
- The local identity q_Tate=qhat^{2l}=p^{2b}, hence q=p^6 for b=3.
- p=12301 prime, p=1 mod41; q=p^6 has p-adic valuation 6, prime to 41 (Clause (c)'s q-order condition still needs the actual q-parameter order check).

Conditional:

- Any actual E/F satisfying (4.1); once supplied, S_bad/q/weights are determined by it.
- The Tate j(p^6) specialization as a candidate; its global equation, bad set, torsion fields, and mod-41 image are not computed.

Missing/obstruction:

- First actual object: E/F with field of moduli Q, stable reduction, full E[2]/E[3] over F, bad at 12301, local q=p^6.
- Its conductor/bad set; the mod-41 image; the actual K/CK/V/epsilon data.
- Complete C, actual S_bad and per-p e_p/b_p, q/BPS/gluing, row/Theta weights.
- TC-A..TC-H/TC-S and actual archimedean r_v/h_inf.

Impossible/withdrawn:

- F=Q(i) alone cannot satisfy E[3](F): E[3] rational over F forces Q(sqrt(-3)) in F, and Q(i) does not contain it. Use F containing Q(zeta_12).
- Claiming S_bad={12301} or q=p^6 globally without an actual E is arbitrary.
- Claiming a complete C or global h_C>=Q_C from the local q candidate is withdrawn.

## 7. Verdict and next executable step

Verdict: a genuine complete C for F_mod=Q is not constructed. The first construction obstruction is clause (b): no actual elliptic curve E/F with the required field of moduli, stable reduction, full 2/3 torsion over F, bad prime 12301 and local Tate parameter p^6 is supplied. The field-level start is fixed: F must contain Q(zeta_12); the local start is fixed: e=41,b=3,q=p^6 at p=12301. Everything downstream (S_bad, per-p types, q/BPS, weights, target) is missing.

Next executable step (non-Lean): produce or rule out an explicit E/Q with

    field of moduli Q, full E[6] over Q(zeta_12), bad reduction at 12301,
    local q=p^6, and mod-41 image containing SL2(F_41),                  (7.1)

by computing its Weierstrass equation, discriminant/conductor, bad set, torsion fields, and mod-41 image. Any success must then pass TC-A..TC-H/TC-S; any failure at (7.1) is the exact construction obstruction.

Status: stage1 natural-language/exact local arithmetic only. Lean/Project/kernel/comparator/independent review not run. target_accepted=false; complete C9/P6/ABC not proved.
