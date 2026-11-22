# C9 stage1: source generators on O_K/J mod p

Task: task-153. Date: 2026-10-25. Owner/executor: transport.
Stage: natural-language research only. No Lean, Project, target or axiom changes.
Consumer: n8-c9-output-region-source-route.

Status: exact finite question isolated; the cited source results do NOT determine
whether the actual finite image barGamma preserves l=O_K/J. The correct actual
donor is H=Phi^{-1}(Sp_{2g}(Z_p)), not the image of a homomorphism rho and not
a free-group boundary-word substitution. The basis alignment needed to identify
l with the fixed line U is an inferred convention, not a stated cross-paper
theorem. Therefore B=O_K vs B=I remains UNDETERMINED at stage1.

This file supersedes, for the finite mod-p question, the corresponding
speculation in C9-TAME-LOG-DOMAIN-20261025.md section 6. It depends on the
correction file C9-SYMPLECTIC-SOURCE-20261025.md and does not copy the flawed
section-2 construction.

## 0. Sources and correction dependency

Read:

- C9-SYMPLECTIC-SOURCE-20261025.md, 313 lines,
  SHA256 3F98F68A5E143DCD51ED6790B1C839AE7B8811E4E418D48B02E37E7C4D5B9C70.
  This is the authoritative correction: rho is not a homomorphism, no
  splitting is known, boundary-word-preserving free substitutions are not
  actual Galois automorphisms, the source is the mapping class/Dehn-twist rho,
  and the 2025 trace basis vs 2026 symplectic basis alignment is inferred.
- C9-TAME-LOG-DOMAIN-20261025.md, 250 lines,
  SHA256 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06.
  Used for the local type and the two branch formula, with the section-2/6
  caveats corrected below.
- C9-SOURCE-SYMPLECTIC-SPAN-CERTIFICATE-20261025.json, 9173 lines,
  SHA256 8DAD68C6D38FB89BD4CC1105A81484E5FB09F0AD7E9413B4C78D143344290DB0.
  Existing lattice-span certificate; it does NOT compute the line O_K/J.

Paper snapshots:

- Kondo 2605.25428v2 (2026), local HTML SHA
  fe7c464e2ae09ffc85c4b02cad8b10b7eebef351113975a34c53a62169a27d86.
  Loci: Theorem 1.2, Lemma 1.3, Lemma 1.6, Definition 3.2, Lemma 3.3,
  proof of Theorem 2.6.
- Kondo 2512.09231v1 (2025), local HTML SHA
  ff39006cf92ec22e1a39caa89fee9b86080953861d7ac6405e6919338c5c9e6f.
  Loci: Theorem D, Theorem 1.3 (trace kernel), Section 2 (rho, Dehn twists),
  Remark 2.16, Theorem 2.17, Remark 2.18.
- Motizuki AbsTopIII, local SHA
  9926aea8b283c8c9e34750e1d3aa1618beb2650ecff5325d224c4fe627b44388.
  Loci: Def5.4(iii), Prop5.8(i)-(iii).
- IUT III, local SHA
  876ebc732cad5dca89c1446a6055018583512254e3ff5ab333797175ebe9181f.
  Loci: Def1.1(i), Rmk1.1.1(i), Prop1.2(vi), Prop3.2, Thm3.11.

## 0.1 Correction 2 dependency (task-149)

C9-IND1-GLOBAL-20261025.md (531 lines,
SHA256 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8)
corrects the next layer: equations (11)-(14) of C9-TAME section 5 are not a
target proof. Full Ind1 is a procession automorphism group, not a finite label
translation. The target-container step needs TC-A..TC-H plus TC-S (corrected
symplectic donor, basis alignment, trace target, low-ramification, local
naturality). A ring isomorphism alone does not give F(Hull(...)) subset H_C.

This file only addresses the finite line component of TC-S. It makes no
target-containment claim, no F(Hull) inclusion, and does not use TAME section 5
as actual. Any downstream B=O_K/B=I use remains conditional on the TC-A..TC-H
target-container conditions and on the missing finite line coordinate below.

## 1. Exact local setup

Let K/Q_p be finite of odd degree d=e=2g+1>=5, tame totally ramified cyclic,
with p>e+1, pi^e=p u, u in Z_p^times, maximal ideal m_K=pi O_K.
Put:

    J = m_K = pi O_K,
    I = p^{-1} J,
    l = O_K/J  (a line in I/J),
    B = closed Z_p-span of the union of gamma(O_K) over actual gamma in the
        additive image Gamma of Aut(G_K).

Then J subset O_K subset I, and B/J is an F_p-subspace of I/J. The task is to
decide whether B/J is l (B=O_K) or all of I/J (B=I).

The original C9-TAME section 6 correctly states this dichotomy but incorrectly
suggests that the answer follows from the trace/Sp data already assembled. The
finite line coordinate is not supplied by the cited Kondo theorems.

## 2. Corrected source donor

The 2026 paper gives (Definition 3.2 and Lemma 3.3):

    for odd d=2g+1, g=(d-1)/2,
    Sp_{2g}(Z_p) -> GL_d(Q_p), A |-> diag(1,A),

and Phi(Out(G_K)) contains this embedded Sp_{2g}(Z_p). Here
Phi: Out(G_K) -> GL_d(Q_p) is the continuous closed reconstruction map of
Lemma 1.6.

The correct actual source subgroup is:

    H = Phi^{-1}(Sp_{2g}(Z_p)) subset Out(G_K),

so Phi(H)=Sp_{2g}(Z_p) and H is closed. This uses only that Phi(Out) contains
Sp and that Sp is closed; it does NOT assert a homomorphic section, a splitting,
or that H is isomorphic to Sp. It also does not assert that the map rho of the
2025 paper is a homomorphism; 2025 Remark 2.18 explicitly leaves that open.

Consequences under the basis-alignment convention of the correction file:

- in the 2026 basis, y_1,...,y_d of Lemma 1.3,
  k_+ = U direct-sum W, U=<y_1>, W=<y_2,...,y_d>;
- Phi(H) acts as diag(1,Sp_{2g}(Z_p)); U is fixed pointwise, W carries the
  standard symplectic representation;
- if the 2025 trace basis equals this 2026 basis, W=ker Tr_{K/K^{(d=1)}} by
  2025 Theorem 1.3, and for the tame totally ramified C9 type K^{(d=1)}=Q_p,
  so the trace is Tr_{K/Q_p}; it is nonzero on U and zero on W.

All three bullets are an assembled inference, not a single theorem in either
Kondo paper. In particular, the correction file flags that the two papers use
different normal forms for the Jannsen-Wingberg relation, so the identity of
the 2025 trace basis with the 2026 symplectic basis is a convention assumption.

Do NOT use the C9-TAME section-2 claims:

- rho is not a homomorphism and no section Sp -> Out(G_K) is known;
- a free-group automorphism preserving the JW boundary word need not be an
  actual Galois automorphism. The actual source is the mapping class/Dehn
  twist rho of 2025 Section 2, with image only a closed subgroup after closure.
- Phi(Out) contains Sp; it is not proved equal to Sp or to all of GL_d.

## 3. The line l and the two abstract branches

Assume the basis alignment for the remainder of this section, purely as an
explicit conditional model. Write I/J as an F_p-vector space with a
decomposition

    I/J = Ubar direct-sum Wbar,
    dim Ubar=1, dim Wbar=2g=e-1,

induced by the trace decomposition. The subgroup H acts trivially on Ubar and
by Sp_{2g}(F_p) on Wbar.

Because Trace_{K/Q_p}(1)=e not 0 in F_p (p>e), the line l=O_K/J has nonzero
trace; equivalently its Ubar coordinate is nonzero in the trace-adapted model.
But this only says l is not contained in Wbar. It does not say l=Ubar.

Two abstract possibilities are consistent with all trace/Sp information:

1. l=Ubar. Then every element of H fixes l. Since B/J is H-stable and contains
   l, and the Sp representation on Wbar is irreducible, B/J cannot acquire a
   proper Wbar-subspace beyond 0; hence B=O_K.
2. l contains a nonzero Wbar component. Write l = <u+w> with 0!=w in Wbar.
   The standard Sp_{2g}(F_p)-orbit of a nonzero vector spans Wbar, while Ubar
   is fixed; hence the H-orbit of l spans all of I/J, and B=I.

The finite mod-p question is therefore exactly:

    Does the actual line l=O_K/J lie in Ubar?

Equivalently:

    Are all Wbar-coordinates of the class of 1 in O_K/J zero in the actual
    2026/2025 trace-adapted basis?

No cited source answers this. The trace theorem gives only the trace
functional and the Wbar subspace; it does not give the coordinates of the
particular line O_K/J in the reconstructed basis.

## 4. Why Kondo's theorems alone do not decide

The 2026 theorem gives:

- a basis y_1,...,y_d (Lemma 1.3),
- an embedded Sp and containment Phi(Out) contains Sp (Lemma 3.3),
- a reconstructed Q_p-vector space k_+ with an actual Out action.

It does not give:

- an explicit identification of the abstract basis y_i with the actual
  trace/power/unit basis of K in which O_K and J are written;
- the coordinates of the line O_K/J in that basis;
- the finite matrix of the full image Gamma on the line l beyond the Sp
  subgroup (and even the Sp subgroup is only known after the basis-alignment
  convention).

The 2025 trace theorem gives:

- for odd d, ker Tr_{K/K^{(d=1)}} = <y_2,...,y_d>; Tr nonzero on <y_1>.

It does not give the Wbar-coordinate of 1 in O_K/J. A line with nonzero trace
can be Ubar or Ubar plus any nonzero Wbar vector; both have the same trace
nonzero and are indistinguishable from the trace functional alone.

Therefore a proof of B=O_K or B=I cannot be extracted from the cited source
theorems without the basis/coordinate datum. The existing C9 span certificate
computes symplectic lattice spans; it does not compute the line l.

## 5. Exact finite mod-p certificate for the model (not the actual K)

The following finite model shows that trace plus Sp data alone are insufficient.
It is a counterexample to any source-only derivation that ignores the l
coordinate. It is NOT an instantiation of the actual K and does not assert the
actual branch.

Take e=5, p=5 for a minimal model (the actual C9 type has p>e+1; this is only a
finite representation test). Let

    Ubar = F_5 e_1,  Wbar = F_5^4 with standard symplectic form,
    H = diag(1, Sp_4(F_5)),
    l_fix = <e_1>,
    l_move = <e_1+e_2>.

Both lines have nonzero trace functional e_1. For l_fix, the H-orbit has span
dimension 1. For l_move, the Sp_4(F_5)-orbit of e_2 is the full set of
5^4-1=624 nonzero vectors of Wbar; the H-orbit span is all 5 dimensions.
Thus the two lines satisfy the same trace and Sp hypotheses but give B=O_K and
B=I respectively.

The exact finite check used:

    nonzero Wbar vectors: 624
    Sp_4(F_5)-orbit of e_2: 624 (transitive)
    span<H l_fix>/J = 1
    span<H l_move>/J = 5

For the actual e=41,p=12301 type, enumerating GL_41(F_p) is not the task and is
not attempted. The actual computation must be a coordinate computation of the
line l in the actual trace-adapted basis, not a search through all matrices.

## 6. Exact certificate required for the actual branch

The missing datum can be stated in three equivalent forms:

(A) Basis alignment matrix. Let Y=(y_1,...,y_e) be the 2026 basis of k_+, and
let E=(e_1,...,e_e) be the actual trace/power basis used for O_K,J. Give the
matrix M in GL_e(Z_p) (or its reduction in GL_e(F_p)) with Y = E M. Then the
coordinates of 1 in the Y-basis are the first column of M^{-1}; l lies in Ubar
iff its Wbar coordinates vanish.

(B) Finite line vector. Give the vector lambda in F_p^e representing
l=O_K/J in I/J in the trace-adapted basis. The branch is:

    B=O_K  iff lambda_2=...=lambda_e=0;
    B=I    iff some lambda_i (i>=2) is nonzero.

(C) Finite matrix/orbit. Give the finite image barGamma subset GL_e(F_p) and
compute the orbit of the line lambda. If the orbit is {lambda}, B=O_K; if the
orbit contains a vector with nonzero Wbar part together with the Sp orbit, then
B=I.

None of (A),(B),(C) is supplied by the cited Kondo papers or by the existing
span certificate. This is the precise remaining source-generator gap.

Two additional caveats:

- Even the trace basis identification (2025 vs 2026) is an inferred convention;
  if it fails, U is a different line and the fixed line cannot be identified
  with the trace line without a further compatibility theorem.
- The full finite image Gamma may be larger than H; H fixing l does not
  automatically give B=O_K unless the whole barGamma fixes l. Conversely, one
  actual element moving l together with the Sp orbit gives B=I. The full finite
  image is not computed in the sources.

## 7. Proved vs inferred vs missing

Proved in the cited papers:

- Phi is continuous and closed, and k_+(G) is a Q_p-vector space of dimension
  d (Kondo 2026 Lemma 1.6 and surrounding text).
- y_1,...,y_d is a basis (Kondo 2026 Lemma 1.3).
- The embedded Sp_{2g}(Z_p) is contained in Phi(Out(G_K)) (Definition 3.2,
  Lemma 3.3; proof via the mapping class rho, closure, and closed image).
- rho is a set-theoretic map from the mapping class group, not known to be a
  homomorphism; 2025 Remark 2.18; Dehn-twist identification in Remark 2.16 and
  Mod -> Sp_{2g}(Z) in Theorem 2.17.
- Trace kernel formula (2025 Theorem 1.3), for Tr_{k/k^{(d=1)}}.
- Unit/log compatibility diagram (Kondo 2026 Theorem 2.6 proof).

Inferred/conditional in the C9 assembly:

- The 2025 trace basis equals the 2026 symplectic basis.
- H=Phi^{-1}(Sp) acts as diag(1,Sp), U fixed, W standard.
- For the tame totally ramified case, Tr_{k/k^{(d=1)}}=Tr_{K/Q_p}.
- J=m_K and H preserves J; low-ramification e<p-1 from the prior package.
- The standard-lattice/orbit-generation and volume-gain formulas of C9-TAME
  sections 3-5, which are consequences outside the Kondo theorems.

Missing for the present finite question:

- The actual line coordinates lambda of O_K/J in the trace-adapted basis.
- The basis-alignment matrix between the 2025 and 2026 bases.
- The full finite image barGamma on I/J (beyond the Sp subgroup H).
- Any actual computation/certificate of the branch B=O_K or B=I.

## 8. Verdict

source_generator_status = UNDETERMINED

The actual finite image question is not answered by the cited sources. The
correct source donor H=Phi^{-1}(Sp) is actual and closed, but it only predicts a
fixed Ubar line after a basis-alignment convention; it does not identify
O_K/J with that line. Trace nonzero is compatible with both B=O_K and B=I.
The C9-TAME section-6 dichotomy (B=O_K or B=I) survives, but its attempted
resolution via trace/Sp is not justified.

Do not report either branch as proved. Do not use the original C9-TAME
section-2 boundary-word substitution as a source of Sp matrices; use the
mapping-class rho / H construction and flag the basis-alignment and full-image
gaps above.

Target acceptance: false. Complete C9 global P6 remains open.

## 9. Exact next finite computation

For a concrete actual K of the C9 tame type (e=41,p=12301 local realization),
compute one of:

1. The coordinates of 1 in the 2026 y-basis after fixing the 2025/2026 basis
   convention; then apply the lambda criterion.
2. The matrix of Phi on the trace-adapted basis together with the actual line
   generator; then compute the finite orbit under the actual generators.
3. A direct module computation in the actual K: express O_K/J inside
   I/J=p^{-1}J/J, transport through the AbsTopIII reconstruction, and compute
   its image modulo p under the actual Aut(G_K) generators.

The computation must use actual source automorphisms (mapping-class rho/H), not
arbitrary GL matrices and not boundary-word substitutions. A certificate must
record the basis convention, the generator matrices, and the resulting line
orbit; without these, the branch remains undetermined.

## 10. References with exact local anchors

- Kondo 2026, Theorem 1.2 (JW presentation), Lemma 1.3 (y-basis), Lemma 1.6
  (Phi continuous closed), Definition 3.2 (diag(1,Sp) embedding), Lemma 3.3
  (containment), Theorem 2.6 proof (unit/log diagram).
- Kondo 2025, Theorem D (JW presentation), Theorem 1.3 (trace kernel),
  Section 2 (rho/Dehn twists), Remark 2.16, Theorem 2.17, Remark 2.18.
- AbsTopIII, Def5.4(iii), Prop5.8(i)-(iii).
- IUT III, Def1.1(i), Rmk1.1.1(i), Prop1.2(vi), Prop3.2, Thm3.11.
- C9-SYMPLECTIC-SOURCE-20261025.md (correction; authoritative for this task).
- C9-TAME-LOG-DOMAIN-20261025.md sections 1,3-5 and section 6 dichotomy, with
  the corrections listed above.

No Lean/Project/kernel/comparator/independent review was run for this task.
target_accepted=false.