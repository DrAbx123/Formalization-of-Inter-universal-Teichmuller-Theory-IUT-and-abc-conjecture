# C9 attack: full Out(G_K) y1-column beyond D and Aut(K)

Task: task-180 (C9-FULL-OUT-COLUMN-ATTACK-20261025). Owner: logdescent. Date: 2026-10-25. C9 stage1 natural-language research only. Only this file written. No Lean/Project/target/other-owner edits. Consumer: n8-c9-output-region-source-route. P6 unproved; target_accepted=false.

Inputs: C9-GAMMA-COLUMN-ATTACK-20261025.md (SHA256 7BB5D789C5DFDA4CDDB9F39267D2AFCB961BBD369A2FD5983DAD2DC67378568C), C9-SYMPLECTIC-SOURCE-20261025.md (SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70), C9-MODP-BRANCH-PROOF-20261025.md (SHA256 AF543BBBC50E8EC8CF9909CD5675D830018254760ABC66410C81501A7227EADE), C9-IND1-GLOBAL-20261025.md (SHA256 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8), C9-MODP-GENERATOR-20261025.md (SHA256 8232226E983D95C4495864B7491A864750BF730B03611BC27FC5B5E25D39507C), C9-TAME-LOG-DOMAIN-20261025.md (SHA256 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06); Kondo 2025 arXiv:2512.09231v1 and Kondo 2026 arXiv:2605.25428v2, local snapshots, with the loci used there and in SYM/IND1.

## 0. Verdict

Q1, as posed, is not a well-defined finite question in the cited source. The reason is structural, not merely a missing computation:

1. In the tame low-ramification C9 type, every Kondo y_i lies in m=J: y_i=F(x_i) is the p-adic log of a unit, and log(O_K^x)=m=e J. Hence y_i maps to 0 in I/J=p^{-1}J/J. The y-basis is a Q_p-basis of k_+=K, not a basis of I/J. Therefore the phrase "alpha(y_1) has a nonzero W-component in the trace basis of I/J" is not literally meaningful unless one first supplies a non-source normalization of y_1 into I/J.
2. Full Out(G_K) acts on k_+ only as Q_p-linear automorphisms (Kondo 2026 Lemma 1.6: Out(G_K) -> GL_d(Q_p)). The cited papers do not prove that an arbitrary actual outer automorphism preserves O_K, J, I, or a p-integral lattice, nor that it induces an F_p-linear action on I/J. The branch criterion B=O_K vs B=I uses the locus O_K subset I and the span of gamma(O_K); for arbitrary gamma this is not defined inside I.
3. The mapping-class subgroup D and the field subgroup Aut(K) are the only documented families with a known relation to O_K/l. Their actions are compatible with the branch only under the extra source condition H_A and the inferred AbsTopIII/IUT III integral/naturality interface. Non-normal conjugates alpha Aut(K) alpha^{-1} preserve alpha(O_K), not O_K; without alpha(O_K)=O_K they do not act on O_K/J=O_K/J, so their columns on I/J are not defined.
4. Consequently no actual alpha in full Out(G_K) outside D and Aut(K) can be evaluated on Q1 in the cited source; B=I realizability is neither proved nor refuted. This is a stronger and more precise negative than "undetermined": the premise of Q1 needs a missing source-level integral action, and without it the full B branch itself is not well-posed.
5. If H_A is added as an explicit source hypothesis (full Gamma preserves O_K,J,I and acts on I/J), then Q1 reduces to the exact finite matrix question in C9-GAMMA-COLUMN-ATTACK section 6: for each actual generator alpha, compute the first column of its F_p matrix on I/J and check whether it has nonzero entries below the U-line. No cited source supplies those matrices. The task is then a finite representation computation, not a consequence of Kondo's theorems.

No arbitrary generator, no assumed B=I, and no target-containment claim is introduced.

## 1. The local objects and the type mismatch

Tame C9 type: p odd, K/Q_p tame totally ramified cyclic, e=ell odd, p>e+1, f=1, d=e=2g+1, O_K=Z_p[pi], pi^e=p u, u in Z_p^x, m=pi O_K, J=log(O_K^x)=m, I=p^{-1}J=m^{1-e}, l=O_K/J subset I/J. I/J is an e-dimensional F_p-vector space; l is the line 1 mod J.

Kondo 2025 defines F: G_K -> k_+ as the composite of abelianization/reciprocity, projection to O_K^x, and p-adic log, and y_i=F(x_i). For tame e<p-1, log is defined on O_K^x and log(O_K^x)=m (C9-TAME section 1). Thus

    y_i in m = J, hence [y_i]=0 in I/J for every i.        (1.1)

In particular y_1 is not a nonzero vector of I/J and cannot be a basis vector of the trace line U there. The 2025 trace basis (y_1,...,y_d) is a Q_p-basis of K_+; the 2026 symplectic basis is likewise a Q_p-basis of k_+. Neither is an F_p-basis of I/J. The "basis alignment" assumed in the earlier branch files is at best an alignment of Q_p bases plus a normalization by powers of pi; that normalization is not constructed in the cited papers. This is a correction to the literal wording of C9-GAMMA-COLUMN-ATTACK sections 2-3: the statement "D fixes y_1, and if l=U=<y_1> then D fixes l" is conditional on an identification that is not supplied. The underlying k_+ statement (D fixes x_1 and y_1) is correct; its implication to I/J requires the missing integral/normalization interface.

## 2. What full Out actually supplies

Kondo 2026 Lemma 1.6: the reconstruction gives a continuous closed homomorphism

    Phi: Out(G_K) -> Aut_{Q_p}(k_+(G_K)) ~ GL_d(Q_p).        (2.1)

This is Q_p-linear only. It does not state that Phi(alpha) preserves:
- the Z_p-lattice O_K inside K;
- the maximal ideal J=m;
- the fractional ideal I=p^{-1}J;
- the quotient I/J or O_K/J.

The corrected donor H=Phi^{-1}(Sp_{2g}(Z_p)) is defined by the Q_p-linear Phi image. Its action on the log-shell/unit side is matched to AbsTopIII/IUT III only through an inferred naturality interface (SYM section 5; IND1 TC-S). Even for H, the induced action on I/J is not a Kondo theorem. For full Out, there is no such interface at all in the cited papers.

The branch definition B=closed Z_p-span of union gamma(O_K) requires gamma(O_K) to lie in a common ambient Z_p-lattice (or at least in I). The cited papers do not prove gamma(O_K) subset I for arbitrary gamma in Out(G_K). If gamma(O_K) is not in I, B is not a subspace of I and the dichotomy B=O_K/B=I is not defined; this is precisely the failure of (H_A) at the level of full Out.

## 3. Mapping-class D

For odd d=41, Kondo 2025 Section 2 assigns a_i -> x_{2i}, b_i -> x_{2i+1}; hence every element of D=closed<rho(Mod)> fixes x_1 and y_1=F(x_1) in k_+. This is a correct k_+ statement. It does not imply an action on I/J unless:

(A) the y-basis/normalization is aligned with an integral basis of I/J, and
(B) the action is Z_p-integral on that basis.

Neither (A) nor (B) is in Kondo 2025/2026. Therefore D's first column on I/J is not computed; only its Q_p matrix on k_+ has first column e_1 in the y-basis. The earlier conclusion B_D=O_K under alignment is conditional on the missing interface, not a paper theorem.

## 4. Field subgroup Aut(K) and non-normal conjugates

Field automorphisms sigma in Aut(K) preserve O_K, m, J, I and fix l=O_K/J because sigma(1)=1 on the residue field. Thus Aut(K) itself does act on I/J and fixes l; on higher m-adic layers it may act by zeta^k on pi^k, so not necessarily identity. This much is actual field theory, independent of Kondo.

Kondo 2025 Theorem I (finite Galois k/Q_p, p odd, d>1; our e=41 case qualifies) proves that the set of Out(G_K)-conjugates of Aut(K) is infinite, in particular Aut(K) is not normal. For alpha in Out(G_K), the conjugate alpha sigma alpha^{-1} is an actual outer automorphism. On the level of field lattices it preserves alpha(O_K), not O_K. Its action on O_K/J is defined only if alpha(O_K)=O_K (or at least alpha^{-1}(O_K) is used consistently); the cited papers do not prove this for the conjugating alpha. Therefore:

- The conjugate fixes alpha(l), not necessarily l.
- It has a well-defined first column on O_K/J only after a source-level lattice comparison.
- Theorem I supplies existence/non-normality, not the value alpha(l) or alpha(O_K). No explicit matrix in the trace basis is given.
- A conjugate by an element alpha in D (if D acts on I/J and fixes l) would fix l; but that again uses the missing H_A/interface.

Thus Theorem I does not yield an actual B=I generator. It only shows the outer automorphism group is larger than the field-theoretic subgroup, without giving its action on the integral lattice.

## 5. Exact question Q1, reformulated

Original Q1 (ill-posed in cited source): does there exist actual alpha in Out(G_K) outside D and Aut(K) such that alpha(y_1) has nonzero W-component / some m_{i1} nonzero in the trace basis?

Corrected source-conditional Q1: assume the extra source hypothesis

    (H_A-full) every actual gamma in the considered full Gamma preserves O_K, J, I,
    and induces an F_p-linear action on I/J compatible with the AbsTopIII/IUT III
    log-shell/unit interface.

Then Q1 is exactly:

    exists gamma in Gamma and i>=2 with m_{i1}(gamma) != 0,       (5.1)

where M_gamma is the F_p matrix on a trace-adapted basis of I/J (first column = gamma(1 mod J)). If (5.1), then B=I (the Sp(W)-orbit generated by H/D, if H is included, spans W). If not, and if v=0 for the trace line, then B=O_K.

Without (H_A-full), (5.1) is not a question about the cited Out action; it is a question about a not-yet-constructed integral lift. No cited source computes this lift.

## 6. Can non-normal conjugates give B=I?

We can state the exact conditional:

- If alpha in Out(G_K) satisfies alpha(O_K)=O_K, alpha(J)=J, and alpha(l) != l, then alpha is an actual B=I generator (after applying the trace/U/W criterion). Such alpha would be a genuine element outside the parabolic stabilizer P(l).
- Kondo Theorem I proves non-normality, not the existence of such alpha. Its conjugates alpha sigma alpha^{-1} fix alpha(l); if alpha(l) != l, they move l; but alpha(l) is not computed and alpha(O_K)=O_K is not proved.
- No cited theorem produces an explicit alpha with alpha(l) != l. The only explicit automorphisms in Kondo 2025 Section 1 construction (e.g. phi with phi(x_2)=x_2 x_1, phi(x_1)=x_1) fix x_1 and y_1 in k_+; they are not shown to act on I/J, and even if they did, the x_1-fixing suggests a parabolic/unipotent W action rather than a lower first-column action.
- Therefore B=I realizability via full Out/non-normal conjugates is not proved; B=O_K for full Out is also not proved.

## 7. What is actually proved / inferred / missing

Proved (papers/local algebra):
- Phi: Out(G_K) -> GL_d(Q_p) continuous closed; k_+ reconstruction (Kondo 2026 Lemma 1.6).
- Sp_{2g}(Z_p) subset Phi(Out(G_K)); H=Phi^{-1}(Sp) closed (Kondo 2026 Definition 3.2/Lemma 3.3; SYM).
- Kondo 2025 Section 2 assignment for odd d; mapping-class generators fix x_1,y_1 in k_+.
- Kondo 2025 Theorem I: infinite Out-conjugates of Aut(K), non-normality.
- Field automorphisms fix l=O_K/J; local trace/U/W decomposition and the finite matrix criterion (BRANCH/GAMMA).
- y_i in J for tame e<p-1; y_i=0 in I/J.

Inferred/conditional:
- The AbsTopIII/IUT III interface that turns Phi(H) into an action on the log-shell/I/J.
- Basis/normalization alignment between the Kondo y-basis and an integral basis of I/J.
- The statement B_D=O_K or D fixes l; it requires the interface and alignment, not just fixing y_1 in k_+.
- Any use of D-conjugates of Aut(K) to fix l.

Missing:
- A proof or source hypothesis that full Out(G_K) preserves O_K,J,I and acts on I/J.
- Explicit integral lattices / normalizations for the Kondo y-basis and symplectic basis.
- Actual matrices of full Out generators on I/J, in particular full Gamma beyond D and Aut(K).
- Values alpha(l) for non-normal conjugates, or a proof they fix l.
- Therefore no B=I generator is produced; no B=O_K conclusion for full barGamma.
- TC-A..TC-H + TC-S target conditions remain open; no target containment.

## 8. If one insists on a pure group-level formulation

Without any lattice/interface, the only well-defined group-level question is:

    Does there exist alpha in Out(G_K) outside D and Aut(K) with a known value Phi(alpha)(y_1) not in <y_1>?    (8.1)

But Phi(alpha) is only Q_p-linear; Phi(alpha)(y_1) is a vector in k_+. Since y_1 in J, this vector has no direct I/J meaning. If Phi(alpha)(y_1) has nonzero component away from the y_1-line in the Kondo y-basis, that is a Q_p statement, not a mod-p line statement; it does not by itself give B=I. The conversion from (8.1) to B=I needs an integral lift/normalization, which is exactly the missing interface. Thus even the group-level Q1 variant is not sufficient.

## 9. Conclusion

- The literal Q1 is ill-posed from the cited source: y_1 lies in J and vanishes in I/J; full Out is only Q_p-linear and has no constructed integral action on I/J.
- Under the explicit extra hypothesis H_A-full, Q1 becomes the finite matrix condition (5.1), but no actual matrices/generators beyond D and Aut(K) are supplied; non-normal conjugates from Kondo Theorem I do not compute alpha(l) or lattice preservation.
- B=I realizability remains unproved. B=O_K for full barGamma is also unproved. The exact remaining gap is the integral lift/naturality H_A-full plus explicit full Gamma matrices, not a missing citation about non-normality.
- No arbitrary generator, no arbitrary B=I assumption, no target containment. target_accepted=false; P6 unproved.

## 10. Acceptance

Only C9-FULL-OUT-COLUMN-ATTACK-20261025.md written. Natural-language self-review done. Lean/Project/kernel/comparator/independent review not run; not applicable. The correction of the literal y_1-in-I/J identification is explicitly recorded; the earlier GAMMA file remains valid only under its stated alignment/interface caveat.
