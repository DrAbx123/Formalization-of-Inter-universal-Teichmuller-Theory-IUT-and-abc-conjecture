# C9 attack: actual Gamma first column and B=I realizability

Task: task-165 (C9-GAMMA-COLUMN-ATTACK-20261025). Owner: logdescent. Date: 2026-10-25. Stage1 natural-language/exact-matrix research only. Only this file written. No Lean/Project/target/other-owner edits. Consumer: n8-c9-output-region-source-route. P6 unproved; target_accepted=false.

Corrections obeyed: SYM/task-147 (rho not a homomorphism, no splitting, boundary-word substitutions are not automatically actual Galois automorphisms, H=Phi^{-1}(Sp), basis alignment inferred, trace target Tr_{K/K^(d=1)}); IND1/task-149 (TAME section 5 (11)-(14) not a target proof; full Ind1 is a procession automorphism group; F(Hull) subset H_C is not implied by a ring isomorphism; TC-A..TC-H + TC-S needed). No target-containment claim is made.

## 0. Verdict

1. The documented mapping-class source D fixes x_1. For odd d=2g+1, Kondo 2025 Section 2 assigns a_i -> x_{2i}, b_i -> x_{2i+1}; x_0,x_1,sigma,tau are not hit. Hence every rho(mapping class) fixes x_1; in the y-basis y_i=F(x_i), every element of D has first column (a,0,...,0).
2. If the inferred basis alignment holds and l=O_K/J equals U=<y_1>, the whole D fixes l. Then B_D=O_K. So the mapping-class source cannot realize B=I; not merely H, but all of D fixes the trace line.
3. If alignment fails and l has nonzero W-component v, H subset D already gives B=I by the Sp(W)-orbit. This is not an extra D-generator moving l; it is v != 0.
4. The field-theoretic subgroup Aut(K) fixes l: field automorphisms preserve O_K and J, and act as identity on O_K/J (sigma(1)=1). Thus Aut(K) cannot realize B=I. A general outer conjugate alpha Aut(K) alpha^{-1} fixes alpha(l); if alpha is outside D and alpha(l) != l, it may move l, but no source computes alpha(l).
5. Therefore no documented actual source generator (mapping-class D, field subgroup Aut(K), or D-conjugates of Aut(K) when v=0) has a nonzero lower first-column entry. Full B=I would require an actual outer automorphism outside these families; this is not supplied by the cited papers. Full barGamma remains UNDETERMINED.
6. Explicit e=41, p=12301 check: p=41*300+1, d=41=2g+1, g=20. Every Dehn-twist generator fixes x_1, so its 41x41 matrix is block diag(1,A), A in Sp_40, first column (1,0,...,0). A finite matrix I+E_{2,1} would give B=I but moves x_1; it is not in D and not obtained from the mapping-class assignment. Hence the suggested explicit Dehn twist does not produce B=I.

## 1. Inputs

- TAME = tmp/sheaf/n8/closure/C9-TAME-LOG-DOMAIN-20261025.md, SHA256 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06. Used only for local type and branch statement; sections 2/5 not treated as proof.
- SYM = tmp/sheaf/n8/closure/C9-SYMPLECTIC-SOURCE-20261025.md, SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70.
- IND1 = tmp/sheaf/n8/closure/C9-IND1-GLOBAL-20261025.md, SHA256 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8.
- BRANCH = tmp/sheaf/n8/closure/C9-MODP-BRANCH-PROOF-20261025.md, SHA256 AF543BBBC50E8EC8CF9909CD5675D830018254760ABC66410C81501A7227EADE.
- GEN = tmp/sheaf/n8/closure/C9-MODP-GENERATOR-20261025.md, SHA256 8232226E983D95C4495864B7491A864750BF730B03611BC27FC5B5E25D39507C.
- AUDIT = tmp/sheaf/n8/closure/C9-AUDIT-BRANCH-20261025.md, 239 lines; classifies task-155 B=O_K as conditional subgroup theorem, not full barGamma.
- Kondo 2026 arXiv:2605.25428v2: Definition 3.2, Lemma 3.3, Lemma 1.3, Lemma 1.6, Theorem 2.6 proof.
- Kondo 2025 arXiv:2512.09231v1: Theorem D, Theorem 1.3, Theorem E, Theorem I, Section 2 assignment S2.Ex62, Remark 2.16, Theorem 2.17, Remark 2.18.
- IUT I Section 0, Definition 4.10, Proposition 4.11; IUT III Proposition 1.2(vi), Proposition 3.2, Theorem 3.11(i), Corollary 3.12; AbsTopIII Def 5.4(iii), Prop 5.8(i)-(iii).

Local type: p odd, K/Q_p tame totally ramified cyclic, e=ell odd, p>e+1, f=1, d=e=2g+1, O_K=Z_p[pi], pi^e=p u (u in Z_p^x), m=pi O_K, J=m, I=p^{-1}J=m^{1-e}, l=O_K/J a line in I/J. This file stays in this tame type; e>=p-1 changes J and is not covered.

## 2. First-column criterion

Choose trace-adapted F_p-basis (e_1,...,e_e) of I/J with e_1=1 mod J, U=<e_1>=l, W=ker Tr=<e_2,...,e_e>. For gamma in Gamma let M_gamma=(m_ij) be its mod-p matrix; the first column is gamma(e_1).

    B=O_K  <=>  m_{i1}=0 for all i>=2 and all gamma.        (2.1)
    B=I    <=>  some gamma has some m_{i1} != 0, i>=2.      (2.2)

Equivalently, B=I iff some actual gamma maps l to a line with nonzero W-component. This criterion is independent of other columns; a nonzero W-entry in a non-first column does not by itself give B=I. The mapping-class matrices below have first column e_1, even though they act nontrivially on W.

If alignment exists, identify 2025 y-basis with 2026 symplectic basis; otherwise use the change-of-basis matrix T and the formula in BRANCH section 3.2.

## 3. Mapping-class source fixes x_1

Kondo 2025 Section 2 fixes generators a_1,b_1,...,a_g,b_g,c of pi_1(S minus P) and uses JW generators sigma,tau,x_0,...,x_d. For odd d, the assignment (local snapshot formula S2.Ex62, around lines 1774-1787) is

    a_i -> x_{2i},   b_i -> x_{2i+1},   i=1,...,g.        (3.1)

Thus x_0,x_1,sigma,tau are fixed by the assignment. The mapping class group is generated by Dehn twists phi_i, phi_i', phi_i''; each acts on pi_1 by an automorphism fixing the boundary delta, and via the JW presentation gives an actual outer automorphism of G_K. rho is a set-theoretic map, not a group homomorphism (Remark 2.18), but each individual actual automorphism induced by the assignment fixes x_1.

Define D as the closed subgroup of Out(G_K) topologically generated by rho(Mod(S minus P)). Since every generator fixes x_1, every element of D fixes x_1.

Let y_i=F(x_i), where F is the composite G_K -> O_K^x -> k_+ from Kondo 2025. Under the naturality F(alpha(x))=alpha_+F(x) (Kondo 2026 Theorem 2.6 proof gives alpha_+ log = log alpha^times; SYM/IND1 mark the C9 concrete interface as inferred), fixing x_1 gives

    alpha(y_1)=y_1 for every alpha in D.        (3.2)

Hence in the y-basis every alpha in D has first column (1,0,...,0). This is stronger than the old H-only statement: the entire mapping-class source D, not just H=Phi^{-1}(Sp), fixes the y_1 line.

Consequences:
- If the basis alignment l=U=<y_1> holds, then alpha(l)=l for all alpha in D; B_D=O_K.
- If the alignment fails and l has nonzero W-component v, then H subset D already gives B=I by Sp(W)-irreducibility. No extra D-generator is needed.
- If v=0, D cannot move l; if v!=0, H already does. So D has no generator with nonzero lower first column beyond H; B=I is exactly the v!=0 branch or comes from outside D.

## 4. Field subgroup Aut(K) fixes l

For sigma in Aut(K): sigma preserves O_K, m, J, I. On O_K/J=O_K/m, sigma(1)=1, so sigma fixes l=O_K/J. This uses only field automorphism and total ramification. sigma may act nontrivially on higher m-adic layers (if sigma(pi)=zeta pi, zeta in mu_e, then pi^k maps to zeta^k pi^k), so it need not be identity on I/J; but it fixes l.

For alpha in Out(G_K), the conjugate alpha sigma alpha^{-1} fixes alpha(l). If alpha(l)=l, this conjugate also fixes l; if alpha(l)!=l, it fixes a different line. Kondo 2025 Theorem I gives infinitely many Out-conjugates of Aut(K) (non-normality), but does not compute alpha(l) in the trace/2026 basis. Therefore non-normality alone does not give B=I.

When alpha is in D and v=0, D fixes l, so alpha sigma alpha^{-1} also fixes l. Thus the subgroup generated by D and Aut(K) fixes l in the v=0 alignment case. Whether Out(G_K) is generated by D and Aut(K) is not proved by Kondo 2025; Theorem I only proves non-normality, not generation.

## 5. Explicit e=41, p=12301

Take p=12301 (prime; 12301-1=41*300), e=41, K=Q_p(pi), pi^41=p. Then p>e+1, e< p-1, tame; d=41=2g+1, g=20.

By (3.1), a_i maps to x_{2i}, b_i to x_{2i+1}, i=1,...,20. Every Dehn twist phi_i,phi_i',phi_i'' fixes x_1. Therefore every mapping-class generator has y-basis matrix

    M = diag(1, A),  A in Sp_40(Z_p) (mod p in Sp_40(F_p)),   (5.1)

with first column (1,0,...,0). A concrete W-matrix can be A=I+E_{2,3} (a standard symplectic transvection; p>2 gives det A=1). This only changes W coordinates y_2,y_3 and leaves y_1 fixed. So the explicit e=41 Dehn twist does not produce a nonzero lower first-column entry, and cannot give B=I.

The finite matrix I+E_{2,1} (first column e_1+e_2) would give B=I by (2.2), but it moves y_1 to y_1+y_2, i.e. it moves x_1. It is not in D and is not induced by the mapping-class assignment. It is only a finite witness that the B=I criterion is non-empty, not an actual source.

Thus at e=41/p=12301 the mapping-class and field-theoretic source families give no B=I generator; an actual alpha outside them with alpha(y_1)=y_1+w, w != 0, is required.

## 6. Full Gamma status and exact remaining question

Documented source families:
- D: fixes y_1; first column e_1 in y-basis; v=0 gives B=O_K, v!=0 gives B=I via H/D.
- Aut(K): fixes l; D-conjugates fix l when v=0.
- Kondo Theorem I Out-conjugates of Aut(K): each fixes alpha(l); no alpha(l) computation; not a B=I generator unless alpha(l)!=l, which is unproved.

Exact remaining questions, equivalent:
(Q1) Does there exist an actual alpha in Out(G_K) (or its finite image Gamma) such that alpha(y_1) has nonzero W-component?
(Q2) Equivalently, in the 2025 trace basis (or after explicit T), does some actual generator have a nonzero entry m_{i1}, i>=2?
(Q3) Does Out(G_K) have generators outside D and Aut(K), and what are their first columns on I/J?

Current answers:
- D: no (section 3).
- Aut(K): no (section 4).
- D-conjugates of Aut(K): no when v=0 (D fixes l).
- General Out elements: unknown; no paper computes their y-basis/I/J matrix.
So full barGamma B branch = UNDETERMINED. B=I is not proved realizable; B=O_K for full barGamma is also not proved. If Q1 has a positive answer, then B=I; if Q1 is false (and v=0), then B=O_K.

No target F(Hull) subset H_C, no h_C>=Q_C, and no TC-A..TC-H/TC-S step is claimed.

## 7. Proved / inferred / unproved

Proved from papers and local algebra:
- Assignment (3.1) for odd d; mapping-class generators fix x_1.
- H=Phi^{-1}(Sp) closed, Phi(H)=Sp (Kondo 2026).
- Trace kernel y-basis description (Kondo 2025 Theorem 1.3/Theorem E) for Tr_{K/K^(d=1)}; in the tame totally ramified case K^(d=1)=Q_p.
- Trace/U/W decomposition and matrix criterion (2.1)/(2.2).
- Field automorphisms fix l; D fixes y_1 under F-naturality.

Inferred/conditional:
- F-naturality alpha_+ log = log alpha^times and the interpretation y_1=F(x_1).
- Basis alignment 2025 trace basis = 2026 symplectic basis, l=U.
- If F is not natural, even D may move y_1; cited papers give no counterexample.
- Kondo Theorem I conjugates fix l when conjugated by D and v=0; general conjugates uncomputed.

Unproved:
- Full Out generator set beyond D and Aut(K), and their first columns.
- Q1 for full Gamma.
- Basis-alignment matrix T and v.
- B=O_K or B=I for full barGamma.
- Any target containment; TC-A..TC-H + TC-S remain open.

## 8. Exact computation tasks for e=41/p=12301

1. Write the 2025 y-basis and the 2026 symplectic basis; compute T and decide whether T e_1 is in the y_1 line (v=0) or has nonzero W-component (v!=0).
2. If v!=0: record B=I from H/D; no extra generator needed.
3. If v=0: enumerate actual generators of Out(G_K): Dehn twists from D, field automorphisms Aut(K), and any actual elements constructed by Kondo Theorem I proof. Compute alpha_+(y_1) in the y-basis and check its W-coordinates.
4. If all documented generators have zero W-coordinates and no generation theorem covers Out(G_K), then full B remains UNDETERMINED; do not declare B=O_K.
5. A positive actual alpha with nonzero W-coordinate gives B=I; record its Dehn-twist/field-conjugate source. Do not use arbitrary GL_41(F_p) matrices, boundary-word substitutions, or the e=5,p=5 finite model as actual source.
6. Any downstream target use requires TC-A..TC-H + TC-S; local branch values are not target inequalities.

## 9. Acceptance

- Only C9-GAMMA-COLUMN-ATTACK-20261025.md written; no Lean/Project/target/other-owner edits.
- Natural-language self-review done. Lean/Project/kernel/comparator/independent review not run; not applicable.
- Full barGamma branch remains UNDETERMINED; mapping-class D and field Aut(K) are excluded as B=I generators; explicit e=41 Dehn twist has first column e_1. target_accepted=false.
