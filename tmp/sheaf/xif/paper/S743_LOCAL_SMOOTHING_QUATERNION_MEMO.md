# S743 (Task P): the 2026 local-smoothing proof, quaternionic Monge–Ampère, and transfer to the Θ-pilot / p-adic log-volume target

Date: 2026-10-30. Status: **literature research only**. No Lean claim, no new axiom, no target change, no fake object.
Read first: [TASK_LEDGER.md](TASK_LEDGER.md) (current exact-missing list, not the obsolete completion-carrier gaps).

## 0. One-paragraph answer

The most recent all-dimensions local-smoothing proof (OpenAI, *Local smoothing for the Euclidean wave equation*, October 25, 2026) **does use a genuine algebraic structure: the quaternion division algebra H, quaternionic Hermitian matrices, the Moore determinant/cofactor, and a quaternionic Monge–Ampère equation on each spatial fiber**. It does **not** use Clifford algebras (0 occurrences), spinors, octonions, or a quaternion algebra over a number field. The earlier three-dimensional proof in the same repository (September 24, 2026) uses a different, combinatorial/entropy argument and has **zero** quaternion/Monge occurrences. The transferable content is a package of archimedean real-analysis devices (Gaussian localization by imaginary translation; a Gram/Hermitian encoding of a positive semidefinite tensor; a determinant equation with a rank-one background; a divergence-form cofactor identity; a two-circle logarithmic loss). **None of these can directly close the paper-faithful Θ-pilot hull-log identity or construct the q[2u]/root stack**: the local-smoothing theorem is an existential-constant L^p inequality with ε-loss, while the IUT target is an exact equality of procession-normalized Haar log-volumes and an actual root unit in a finite extension. The algebraic structures are also unrelated: H is the real division algebra of the analytic proof, not an arithmetic quaternion algebra, and the finite quadratic Gauss sums / Θ-labels of the IUT side do not appear in the paper (the word "theta" occurs once there, as a symbol in a PDE calculation; "p-adic" occurs zero times).

## 1. Primary sources and release status

| Item | URL | What it is |
|---|---|---|
| All-dimensions paper (Oct 25, 2026) | <https://github.com/openai/math/blob/main/preprints/Local-smoothing-for-the-Euclidean-wave-equation-October-25-2026/paper.pdf> | 59 pp., author line "OpenAI"; proves Sogge local smoothing for all n ≥ 2, plus Bochner–Riesz, restriction, Kakeya, Stein square function |
| 3D paper (Sep 24, 2026) | <https://github.com/openai/math/blob/main/preprints/Critical-local-smoothing-for-the-three-dimensional-wave-equation-September-24-2026/paper.pdf> | 165 pp., author line "OpenAI"; critical L^3 local smoothing in R^3; different proof style |
| Formalization scope note | <https://github.com/openai/math/blob/main/lean/docs/079.md> | lists the six comparator targets and the two papers |
| Comparator statements | <https://github.com/openai/math/blob/main/lean/ComparatorChallenges/LocalSmoothing.lean> | six theorem statements, each with `sorry` by design (statement reference, not a proof hole); `euclidean_local_smoothing` is an `∃ C, 0 < C ∧ ... ≤ C * ...` statement |
| Repository history | <https://github.com/openai/math/blob/main/history.md> | Oct 26, 2026 entry: "releasing the model output directly"; proof uses "an auxiliary partial differential equation"; also Kakeya/restriction claims |
| Lean quaternion development | <https://github.com/openai/math/blob/main/lean/OAI/Analysis/Calculus/Quaternion/Algebra.lean>, <https://github.com/openai/math/blob/main/lean/OAI/Analysis/Calculus/Quaternion/Gram.lean>, <https://github.com/openai/math/blob/main/lean/OAI/Analysis/Calculus/Quaternion/CofactorDivergence.lean> | `Q := Quaternion ℝ`, `hessianMap`, `outer`, `hessianMap_rankOne`, `hessianMap_trace`, `quaternionGram_quadratic`, `quaternionGram_pos` |
| Press coverage / framing | <https://www.theverge.com/ai-artificial-intelligence/1019143/openai-eth-kaseya-science-math-physics> | Oct 26, 2026; OpenAI releases model output directly; external math advisers recommended against this release practice |
| 2D background (GWZ) | <https://doi.org/10.4007/annals.2020.192.2.6> ; <https://arxiv.org/abs/1909.10693> | Guth–Wang–Zhang, *A sharp square function estimate for the cone in R^3*, Ann. of Math. 192 (2020), 551–581 |
| Local-smoothing survey | <https://doi.org/10.1007/978-3-030-72058-2_2> | Beltran–Hickman–Sogge, *Sharp local smoothing estimates for Fourier integral operators* |
| Quaternionic MA background | <https://doi.org/10.1007/BF02930695> ; <https://doi.org/10.1016/j.aim.2013.03.021> | Alesker, *Quaternionic Monge–Ampère equations* (2003); *Solvability ... flat hyperKähler metric* (2013) |

Status caveat: these are **model outputs**, not peer-reviewed papers. The repository says the output is released directly; `history.md` also records that earlier batches had withdrawals/repairs. The Lean formalization exists in the same repository, but the comparator file is deliberately `sorry`-ed and I did **not** compile the actual proof development. Treat the theorem as "claimed, with a formalization artifact in the repository", not as an independently verified fact.

## 2. The recent proof in one page

The all-dimensions paper proves:

* **Theorem 1.1**: for n ≥ 2, 2 ≤ p < ∞, ε > 0,
  `||U(T) f||_{L^p(R^n × [1,2])} ≤ C_{n,p,ε} ||J^{s_+(p)+ε} f||_{L^p(R^n)}`, with `s_+(p) = max(0, (n−1)/2 − n/p)`; at p = 2 one may take ε = 0.
* **Theorem 1.2 (critical annular estimate)**: at `p = p_c = 2n/(n−1)`, with `P_N = φ(D/N)`,
  `||U(T) P_N f||_{L^p(R^n × I)} ≤ C_{n,φ} [log(2+N)]^{2/p} ||f||_{L^p}`.
  Interpolation and frequency summation over annuli give Theorem 1.1 (Section 7).
* Consequences: Bochner–Riesz (Theorem 10.1), Stein square function (Theorem 11.1), spherical/cone restriction (Corollary 9.3), Kakeya maximal and Hausdorff dimension (Corollary 9.1), paraboloid/Schrödinger (Corollary 12.1).

The mechanism, in the paper's own order:

1. **Imaginary translation → Gaussian window** (Section 1.4, Section 2.1). Translating by `−iρ(1, ω)` multiplies a mode of frequency ξ by
   `exp[−ρ|ξ| |ξ/|ξ| − ω|^2 / 2]`,
   an angular Gaussian of width `(ρN)^{−1/2}`. The symmetric first-order wave system supplies the light rays; the sum of two fluxes gives the imaginary displacement.
2. **Positive conserved tensor** (Proposition 2.2). Two flows built from the continued wave give a positive semidefinite tensor whose real columns have zero divergence; its time component still detects the wave on the cap; in the scalar case it is the Husimi density.
3. **Quaternionic encoding** (Section 2.3, eq. (2.6)). Target triples lie in `D = span_R(1, i, j) ⊂ H`. A quaternionic Hermitian matrix `A` is converted to a real tensor by
   `A^R_{μα,νβ} = Re(ē_α A_{μν} e_β)`, `(e_0,e_1,e_2) = (1,i,j)`.
   For `A = χχ*` this is the Gram matrix of the rows `e_α χ_μ`; the real four-square tensor becomes a rank-one quaternionic Gram matrix.
4. **Quaternionic Hessian calculus** (Section 3.1, Lemma 3.1). For a real C² function u,
   `G_a(u) = Σ_α e_α ∂_{aα} u`, `H_{ab}(u) = Σ_{α,β} e_α ē_β ∂_{aα}∂_{bβ} u`.
   Then `H(u)` is Hermitian, `tr H(u) = Δu`, the real Hessian map sends `ξξ^t ↦ gg*` and nonnegative real forms to nonnegative quaternionic forms, and for a holomorphic map F,
   `H(Σ_ν |F_ν|^2) = 4 J*J` (eq. (3.4)).
5. **Moore determinant/cofactor** (Section 3.2, Lemma 3.2). `det A` is the Moore determinant, the product of the real eigenvalues with quaternionic multiplicity; `C(A)` is the cofactor, `C(A) = (det A) A^{−1}` for `A > 0`, and `det(A + t vv*) = det A + t v*C(A)v`. Alesker's theorem makes the real tensor of the cofactor of a positive quaternionic Hessian have divergence-free columns (Lemma 3.3, eq. (3.12)); this puts the linearized Monge–Ampère operator in divergence form.
6. **Determinant equation with a rank-one background** (Section 1.4, Section 4). On each spatial fiber solve
   `det H_fib(λ|Φ|^2 + u) = λ μ`, `u|_∂ = 0`.
   The background `λ|Φ|^2` is rank one: its Hessian has one nonzero eigenvalue λ, so adding αI gives determinant `(β + α) α^{n−1}`. Density `μ ≥ m` then forces the depth of u to be at least `const · r^2 · m^{1/(n−1)}`; the energy `∫(−u)μ` detects `m^{n/(n−1)}`, and since μ recovers a square of the wave the exponent is `2n/(n−1) = 2p_c/(p_c−1)`.
7. **Aubin–Mabuchi correction** (Section 1.4, Section 4.3). A correction to `∫(−u)μ` makes the full determinant cancel under differentiation in (T, τ), while leaving the corrected energy comparable; this is the classical Aubin–Mabuchi energy.
8. **Two circles / thin cylinder** (Section 1.3, Section 6, Appendix B). The reduction
   `∫ ||U(T)f||_p^p dT ≲ a^{−2} ∫ H(T,2a) dT ≲ [log(2/h)]^2 a^{−2} H(0,4a) ≲ [log(2/h)]^2 ||f||_p^p`
   uses a scalar differential inequality between the circles of radius 2a and 4a; this is where the `log(2+N)` loss comes from.

## 3. Does it use quaternion / Clifford / other algebraic structures?

Textual counts in the two downloaded PDFs (extracted with pypdf; scripts are scratch, see Section 8):

| Keyword | All-dim paper (Oct 25) | 3D paper (Sep 24) |
|---|---:|---:|
| `quaternion` | 43 | 0 |
| `Monge` | 12 | 0 |
| `Clifford` | 0 | 0 |
| `p-adic` | 0 | 0 |
| `theta` | 1 (symbol Θ in a PDE calculation) | 0 |
| `decoupling` | 2 | 7 |
| `polynomial partitioning` | 0 | 2 |
| `broad` | 1 | 11 |
| `wave packet` | 1 | 4 |
| `Heisenberg` | 0 | 5 |

Answer:

* **Quaternion: yes, essentially.** The proof uses the real quaternion division algebra H, its units i, j, k, quaternionic Hermitian matrices, the Moore determinant, the quaternionic cofactor, and a quaternionic Hessian/Monge–Ampère equation. In the Lean development this is literally `Quaternion ℝ` (`OAI/Analysis/Calculus/Quaternion/Algebra.lean`), with `hessianMap`, `outer`, `hessianMap_rankOne`, `hessianMap_trace`, and the Gram identities in `Gram.lean`.
* **Clifford: no.** There is no Clifford algebra, Dirac operator, spinor, or spin geometry in either paper. The quaternion algebra is used as a 4-dimensional real algebra to package four real squares and to make a determinant equation; the paper does not invoke the Clifford presentation of H.
* **Arithmetic quaternion algebra: not the same object.** The H of the proof is the real division algebra. It has no relation to a quaternion algebra over Q (the arithmetic object that can appear in Shimura-curve/IUT contexts) and supplies no arithmetic class, no Brauer class, no local invariant.
* **Other structures:** symmetric first-order systems (Friedrichs), compensated integrability (Serre/Tartar), Husimi density, complex structure on the Fourier plane (`C_i`), holomorphic maps and `J*J`, Aubin–Mabuchi energy. The 3D paper instead uses a long combinatorial/entropy argument (cylinder experiments, entropy profiles, replica budgets, planar incidences); its quaternion/Monge count is zero.
* The paper's own title/abstract is purely Euclidean harmonic analysis; there is no number-theoretic, p-adic, or log-geometric object.

## 4. Transferable "transform/diagonalization" techniques

Notation: "Θ-side" means the paper Θ-pilot hull log / finite quadratic Gauss sum / Θ-labels; "p-adic side" means the normalized Haar log-volume on the root/extension hull. The exact current gaps are those in [TASK_LEDGER.md](TASK_LEDGER.md) (ConcreteSourceQIdentification; qPilot → product-hull containment; paper hull equality `rootExtensionProductImageHull = paper holomorphic/lambda-O hull`; the four `PaperXiFSourceLink` fields; the `StepXIContract` fields). Note that `PaperRootHullFormulaGap` is listed in the ledger as an **obsolete completion carrier** ("impossible by S342 completion root; do not fill"); it is not the current target.

### T1. Imaginary translation → Gaussian window (Sec. 1.4, 2.1)

What it does: turns a directional frequency cap into a Gaussian weight `exp[−ρ|ξ| |ξ̂ − ω|^2/2]`; this is a phase-space localization (Husimi density), used to keep the interference of a superposition before squaring.

Θ-side: The finite quadratic Gauss sum is `Σ_j ψ(a j^2)` with ψ an additive character of `ZMod N`, and the Θ-pilot value is `q^{j^2/(2l)}` times a root of unity. The paper's Gaussian is a continuous archimedean weight with a free parameter ρ; it is not a finite quadratic exponential and it produces an inequality, not an exact sum. The repo's S689 memo already shows the μ_{2l}-orbit average of every nonzero Θ-label is exactly zero, so a Gaussian/Fourier averaging device cannot recover a positive normalization. **Verdict: no direct use for Θ Gaussian sums; at most a smoothing heuristic, not an identity.**

p-adic side: an imaginary translation is an archimedean Fourier device; there is no non-archimedean analogue in the paper and no Haar measure on a p-adic group. **Verdict: reject.**

### T2. Quaternionic Gram encoding of a positive semidefinite tensor (Sec. 2.3, eq. (2.6); Prop. 2.2)

What it does: converts a real four-square tensor B into a quaternionic Hermitian A via `A^R_{μα,νβ} = Re(ē_α A_{μν} e_β)`, with `A = χχ*` a rank-one Gram matrix; this is a genuine "diagonalization" of the tensor into a rank-one object over H, and it is what makes the determinant computation possible.

Θ-side: the IUT tensor/hull side has a real tensor carrier (S653 `RootThetaTensorHullCarrierGap`, S690 coefficient expansion), but the Θ-pilot objects are labels `j ∈ Z/(2l)` and one-dimensional q-powers, not a real n×n PSD tensor. A quaternionic Gram encoding would be a new auxiliary structure with no map to the paper labels; it cannot produce `paperRootThetaHullLog`. **Verdict: no direct use; possible template for a finite-dimensional tensor lemma only.**

p-adic side: the encoding is over R; the determinant is a real determinant; no p-adic valuation or Haar measure. **Verdict: reject for the log-volume identity.**

### T3. Quaternionic Hessian calculus (Sec. 3.1, Lemma 3.1, eq. (3.1)–(3.4))

What it does: gives a Hermitian Hessian with `tr H(u) = Δu`, the rank-one rule `ξξ^t ↦ gg*`, positivity preservation, and the holomorphic identity `H(Σ|F_ν|^2) = 4J*J`. This is the "diagonalization" that turns a real Hessian into a quaternionic Hermitian form whose determinant can be controlled.

Θ-side: no Hessian, no holomorphic map, no real PDE in the Θ-pilot target. The finite Gauss sum has no continuous second derivative to encode. **Verdict: no direct use.**

p-adic side: a p-adic Monge–Ampère theory exists in non-archimedean pluripotential theory, but this paper does not use it, and no theorem identifies its measure with the procession-normalized IUT hull log. The repo already rejected the Berkovich/pluricanonical-measure route in S728 for exactly this missing comparison. **Verdict: reject as paper-faithful; would require a new comparison theorem.**

### T4. Moore determinant/cofactor and divergence form (Sec. 3.2–3.3, Lemmas 3.2–3.3; Alesker)

What it does: defines the real-valued determinant of a quaternionic Hermitian matrix as the product of its real eigenvalues; gives the cofactor identity `C(A) = (det A)A^{−1}`, `det(A + t vv*) = det A + t v*C(A)v`; proves the cofactor has divergence-free columns, putting the linearized Monge–Ampère operator in divergence form and enabling integration by parts.

Θ-side: the only genuinely reusable mathematical content is finite-dimensional linear algebra. If a future target needed a quaternionic determinant/cofactor identity on a tensor carrier, this is a ready template (and the Lean files exist). But the current Θ-pilot/root-stack gap is not a determinant identity; it is an equality of arithmetic log-volumes. **Verdict: reusable only as a standalone linear-algebra lemma, not for the exact gap.**

p-adic side: no. The cofactor divergence is an archimedean PDE identity; p-adic log-volume is an additive Haar measure, not a determinant of a Hessian. **Verdict: reject.**

### T5. Determinant equation with rank-one background (Sec. 1.4, Sec. 4)

What it does: solves `det H_fib(λ|Φ|^2 + u) = λμ` with Dirichlet data. The rank-one background has one nonzero eigenvalue λ, so the determinant is `(β+α)α^{n−1}`; this yields the depth bound `~ m^{1/(n−1)}` and the exponent `2n/(n−1)`.

Θ-side: this is the engine of the L^p exponent; it has no arithmetic content. The Θ-pilot exponent is `j^2/(2l)`, a rational quadratic exponent fixed by the label, not a solution of a PDE. **Verdict: no direct use.**

p-adic side: a p-adic determinant equation would be a different theory (non-archimedean MA), not the paper's; no comparison to the IUT normalization. **Verdict: reject.**

### T6. Aubin–Mabuchi correction / total derivative (Sec. 1.4, Sec. 4.3)

What it does: corrects `∫(−u)μ` so that the full determinant cancels under differentiation in (T, τ); the corrected energy is comparable to the original and is a total derivative. This is a "calibration" identity, not an exact arithmetic identity.

Θ-side: the Θ-side log-volume is already a normalized Haar log; there is no PDE energy to correct. A formal analogy "make the cocycle exact" is not a theorem and would be a target change. **Verdict: no.**

p-adic side: no. **Verdict: reject.**

### T7. Two circles / thin cylinder / annular logarithm (Sec. 1.3, Sec. 6, Appendix B)

What it does: relates the energy on the circle of radius 2a to the circle of radius 4a through a scalar differential inequality, producing `[log(2/h)]^2`; the critical annular estimate has `[log(2+N)]^{2/p}`. This is the only place where a logarithm appears, and it is a **loss**, not a volume.

Θ-side: the Θ-pilot target is an exact `Real.log` of a Haar volume; the local-smoothing log is an analytic loss factor in an inequality. Same word, different object. **Verdict: no direct use; only a heuristic for why logs appear in multi-scale estimates.**

p-adic side: the two-circle argument is archimedean; p-adic log-volume has no radius parameter of this kind. **Verdict: reject.**

### T8. Frequency-annulus reduction (Sec. 1.3, Sec. 7.2)

What it does: reduces the full local-smoothing theorem to the critical annular estimate at `p_c` and sums over dyadic annuli.

Θ-side: the Θ-labels are finite (`j ∈ Z/(2l)`), not a dyadic frequency decomposition; there is no annulus parameter. **Verdict: no direct use.**

p-adic side: no. **Verdict: reject.**

## 5. Assessment against the actual exact gaps

| Current exact gap (TASK_LEDGER) | Can the local-smoothing package fill it? | Reason |
|---|---|---|
| `ConcreteSourceQIdentification` (`sourceQPilotSignedLog = localSignedLog C3.q`) | No | The paper has no arithmetic source, no q, no C3, no signed log. Its objects are Euclidean functions and L^p norms. |
| qPilot → `RootExtensionProductCarrier` containment/log comparison | No | The paper's "energy" is an L^p spacetime norm; the qPilot containment is a set/log comparison on an arithmetic product carrier. No map between them. |
| Paper hull equality `rootExtensionProductImageHull = paper holomorphic/lambda-O hull` | No | This is an exact equality of sets/Haar logs; the paper gives inequalities with ε-loss and no hull object. |
| `PaperXiFSourceLink` fields (source_identifications, qPilotLogVolume_eq_paper, link_identification, link_implies_inclusion) | No | These are identifications of paper objects; the paper has no Θ-link, no qPilot, no IQ hull. |
| `Paper StepXIContract` fields (qSigned/thetaSigned/targetSigned/ipl/she/apt) | No | Same categorical mismatch: the paper is harmonic analysis, not IUT. |
| `PaperRootHullFormulaGap` | No (and per ledger this is an **obsolete completion carrier**; do not fill) | Even the ledger says the completion root is impossible by S342; the current target is the extension/product hull, not this gap. |

Categorical reasons, independent of the details:

1. **Equality vs inequality.** The paper's Theorem 1.1 and its Lean comparator are of the form `∃ C > 0, ... ≤ C * ...` with an ε-loss; the exact gap needs an object identity (`... = ...`). No amount of L^p technique produces an exact Haar-log identity.
2. **Archimedean vs p-adic.** The paper has zero `p-adic` occurrences, no non-archimedean valuation, no Berkovich space, no Haar measure on a p-adic group. Its measure is Lebesgue measure on R^n and its determinant is a real determinant.
3. **Real/quaternionic determinant vs arithmetic labels.** The Θ-side data are finite labels `j ∈ Z/(2l)`, q-powers `q^{j^2/(2l)}`, and a μ_{2l} root ambiguity; the paper's determinant is over an n×n real/quaternionic matrix. There is no functor from one to the other in the paper.
4. **No root stack / no q[2u].** The paper never constructs a root, a Kummer cover, a root stack, or a finite extension carrying `q[2u]`. The actual q[2u] carrier in the repo is `TwoLthRootKummerActual` (`hodgeTwoLthRoot^(2l) = qVAlgClosedUnit`) and the root stack is S356/S392; the local-smoothing paper has no analogue.
5. **Verification status.** The paper is model output, not peer-reviewed; the Lean comparator is `sorry`-ed by design and I did not compile the actual proof development. Even if the theorem is true, it is a theorem about a different subject.

## 6. Narrow, honest reuse in Lean

If (and only if) a future target needs a **quaternionic linear-algebra** lemma, the following are the only reusable pieces I found:

* `OAI/Analysis/Calculus/Quaternion/Algebra.lean`: `Q := Quaternion ℝ`; `gradientMap`, `hessianMap`, `outer`; `hessianMap_rankOne`, `hessianMap_tensor`, `hessianMap_trace`, `hessianMap_isHermitian`, `outer_isHermitian`, `outer_eq_zero_iff`.
* `OAI/Analysis/Calculus/Quaternion/Gram.lean`: `quaternionGram_quadratic`, `quaternionGram_nonneg`, `quaternionGram_pos`, `quaternionGram_kernel`.
* `OAI/Analysis/Calculus/Quaternion/CofactorDivergence.lean` and the surrounding `OAI/Analysis/Calculus/Quaternion/*` files: the cofactor/divergence identities (Lemma 3.3 of the paper).
* Mathlib has `Quaternion ℝ`, but I found no Mathlib Moore determinant / quaternionic Monge–Ampère development. The OpenAI files are the only formalization of these identities in this checkout's dependency set.

This does **not** reduce the paper gap. Importing any of it into the Θ-pilot/root-stack files would add a new dependency without a consumer; per the project rules ("each package names an actual consumer; no import for its own sake"), do not do it.

## 7. What would be needed for a legitimate transfer (and why it is not present)

To use any of T1–T8 for the exact gap, one would need at least:

1. A map from the IUT Θ-pilot/root-stack carrier to the paper's Euclidean/quaternionic objects (or a common generalization).
2. A theorem that the paper's analytic energy/log equals the procession-normalized Haar log of the IUT hull — not just an inequality, and with the exact `(2l)` normalization.
3. A construction of the actual `q[2u]` root unit in the finite extension from the analytic data — the paper has no roots.

None of these exists in the paper, the repository, or the cited literature I checked. The paper is self-contained Euclidean harmonic analysis; the IUT side is arithmetic geometry. The missing bridges are not "implementation details" — they are the exact gap.

## 8. Not run / caveats

* I did **not** compile `openai/math` (no `lake build`), and I did **not** verify the proof of Theorem 1.1. I read the PDFs and the Lean source; the comparator statements are `sorry`-ed by design. `proof_body_checked` and `kernel_closed` are **not** claimed here.
* The PDFs were downloaded from the repository on 2026-10-30 and text-extracted with `pypdf`; local copies are `tmp/sheaf/xif/paper/_external_local_smoothing_all.pdf` and `..._3d.pdf` (plus `.txt`). These are external artifacts, not repo source.
* The `quaternion`/`Monge` counts are keyword counts on the extracted text, not a semantic proof that every occurrence is essential; I read the surrounding contexts (Sections 2.3, 3.1–3.3, 1.4) and the roles are as described.
* The 3D paper is a different proof from the all-dimensions paper; if a task says "the recent proof", specify which one. The all-dimensions paper (Oct 25) is the one with the quaternionic Monge–Ampère; the 3D paper (Sep 24) is not.
* The repo's `history.md` says the output is released directly; The Verge reports the external math advisers' recommendation against this release practice. This is a status caveat, not a mathematical judgment.

## 9. Recommendation

**Reject the local-smoothing/quaternionic-Monge–Ampère direction as a tool for the paper-faithful Θ-pilot hull log, the q[2u] carrier, or the root stack.** It is a genuinely interesting algebraic-analytic technique, but it is archimedean, inequality-based, and has no arithmetic objects; it cannot fill `ConcreteSourceQIdentification`, the hull equality, the `PaperXiFSourceLink` fields, or the `StepXIContract` fields. The only legitimate reuse is a standalone quaternionic linear-algebra lemma if a concrete tensor target later needs one; that is not the current gap, and it should not be imported speculatively.

Do not replace:
* `PaperRootHullFormulaGap` (already obsolete per ledger) with any PDE determinant equation;
* `rootNormedExtension` / `TwoLthRootKummerActual` with a quaternionic Gram matrix;
* the procession-normalized Haar log with an L^p energy.

No fake object, no target change, no new axiom.
