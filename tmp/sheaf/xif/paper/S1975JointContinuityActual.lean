import tmp.sheaf.xif.paper.S1962R1AbstractActionActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S1975: joint continuity of the `G_v`-action on the ind-topological `Ψ~` — exact first missing

Layer: **O** (original Theta-link / q-pilot), local nonarchimedean input to the
S1927 global packet.  Consumer: the S1962 R1 package
(`R1JointContinuousActionMissing`, S1962R1AbstractActionActual.lean), whose
module doc records joint continuity on the limit as the *second* R1 missing.

## The target

S1962 defines, for an actual one-column finite place `v : FinitePrimePlace 2 7`,

  `R1JointContinuousActionMissing v` := the action map
  `G_v × Ψ~ → Ψ~` is jointly continuous, where `Ψ~ = SourceUnitPerfection (QPlace v)`
  carries `psiTildeIndTopology v` (the actual final topology of the genuine
  finite local subfields) and `G_v = Θ ≃ₐ[NormalizedCompletion] Θ`
  (`Θ = SourceAlgebraicClosure (QPlace v)`) carries the Krull topology.

`Iut.Foundations.SourceDefinition52LocalJointContinuity` proves joint
continuity **stagewise**; its own doc says: "Joint continuity on the single
`TopModuleCat` limit carrier would require a separate continuity-with-parameters
theorem and is not an automatic consequence of its colimit universal property,
which only controls linear maps out of the colimit."

## What this file proves (all unconditional, no `sorry`, no `axiom`)

The whole transport chain is carried out on the actual carriers, and the exact
analytic input that is *missing* is isolated as a named proposition.
`Ψ~` is homeomorphic to `Θ` (`sourceUnitPerfectionIndHomeomorph`), the action
is the transported actual Galois action (`sourceUnitPerfectionEquiv_galois_smul`),
and the finite local subfields are the ind stages, so everything is done on `Θ`
with `sourceAlgebraicFieldIndTopology`.

1. `norm_galois_smul`: every actual `G_v`-automorphism is an isometry for the
   (spectral) norm of `Θ`.  This is the real content of "the action is
   compatible with the finite-stage metrics"; it is *not* assumed, it is
   `spectralNorm_algHom_eq` plus the tree's identification of the norm of `Θ`
   with the spectral norm.
2. `isOpen_ind_ball`: absolute-value balls `{y | ‖y - z‖ < ε}` are open for the
   ind topology.  (Only this direction is formal; see below.)
3. `ind_le_norm`: every norm-open set is ind-open, i.e. the tree's definition of
   the ind topology gives one inclusion.  This is the *only* inclusion that the
   final-topology characterisation `isOpen_algebraicFieldIndTopology_iff`
   yields.
4. `jointContinuousGaloisEvaluation_of_ballNeighborhood`: if the ind topology has
   the ball-neighbourhood property, then the actual evaluation map
   `G_v × Θ → Θ` is jointly continuous for the ind topology.  The proof is the
   genuine continuity-with-parameters argument: at `(σ₀, y₀)` take the open
   coset `σ₀ · Gal(Θ/E)` of the open stabiliser of `y₀` (open by
   `stabilizer_isOpen_of_isIntegral`) and the ind-open ball `{y | ‖y - y₀‖ < ε}`
   around `y₀`; for `σ` in the coset and `y` in the ball,
   `σ y - σ₀ y₀ = σ (y - y₀)`, hence `‖σ y - σ₀ y₀‖ = ‖y - y₀‖ < ε` by (1).
5. `r1JointContinuous_of_ballNeighborhood`: the same statement transported to
   `Ψ~` through `sourceUnitPerfectionIndHomeomorph`, i.e. exactly
   `R1JointContinuousActionMissing v`.

## The exact first missing

The single missing input, called `IndCarrierBallNeighborhood (QPlace v)` below, is

  every ind-open set containing `z` contains an absolute-value ball around `z`.

`indCarrierBallNeighborhood_iff` proves that this is **literally the statement
that the ind topology is the norm topology**
(`sourceAlgebraicFieldIndTopology = inferInstance`), and `ind_le_norm` shows the
tree supplies only the other inequality.  So the missing gap is a *strict*
refinement statement: it is not a restatement of the definition, and it cannot
be obtained from `isOpen_algebraicFieldIndTopology_iff`, which only says which
sets are open, not that balls are neighbourhoods.

This is the honest report: **no continuity on the limit is asserted here, and
`R1JointContinuousActionMissing v` itself remains open.**  In particular:

* no `IndCarrierBallNeighborhood` instance is postulated,
* no `Continuous`/`IsTopologicalGroup`/`ContinuousSMul` instance for the action
  on the limit is postulated,
* `R1JointContinuousActionMissing` is *derived* from the missing input only as
  an explicit hypothesis (`r1JointContinuous_of_ballNeighborhood`).

### Research note (not formalised — recorded so the next package does not redo it)

The ball-neighbourhood property is **not** a formality.  `Θ = ℚ̄_p`-style: let
`F_0 ⊂ F_1 ⊂ ⋯` be a cofinal chain of finite subextensions with
`[F_n : K] → ∞` (e.g. `F_n = K(p^{1/2^n})` completed inside `Θ`, whose value
group is `p^{ℤ/2^n}`), and put `r_n = p^{-n} ↓ 0`.  Define opens `U_n ⊆ F_n` by

* `U_0 := B(z, r_0)`,
* `U_{n+1} := B(z, r_{n+1}) ∪ ⋃_{y ∈ U_n} B_{F_{n+1}}(y, δ_y)` with
  `0 < δ_y ≤ min(|y|, dist(y, F_n ∖ U_n))/2`.

Then each `U_n` is open in `F_n`, `U_{n+1} ∩ F_n = U_n` (the `δ_y` cut each ball
inside the level of its centre, and `B(z,r_{n+1}) ⊆ U_n`), so
`φ := ⋃_n U_n` is ind-open and `φ ∩ F_n = U_n`; and `s(U_n) := dist(z, F_n ∖ U_n)`
equals the smallest admissible level above `r_n`, i.e.
`p^{-(n+1)+1/2^{n+1}} → 0`.  Hence `z ∈ φ` while no absolute-value ball around
`z` lies in `φ`: **`IndCarrierBallNeighborhood` is false for this carrier**,
and by `indCarrierBallNeighborhood_iff` the ind topology is strictly finer than
the norm topology.

Consequently the ball route to joint continuity is dead, and the same
construction suggests the S1962 statement itself may be false: for
`O = φ` and any candidate neighbourhood `U = Gal(Θ/E)`, the conjugates of a
`y ∈ V ∩ F_n` lie in fields `σ(F_n)` of depth `M(n)` (which grows at least like
the degree of the Galois closure, hence faster than `n`), while `φ` misses every
level outside `|F_{M(n)-1}^×|`; so `U • V ⊆ φ` should fail.  Neither the
counterexample for `φ` at `(id, 0)` nor the converse is formalised here.  The
actionable next step is a **counterexample package** for
`R1JointContinuousActionMissing` (or a genuinely `G`-stable refinement of the
ind topology), not another continuity estimate.  This file asserts neither the
target nor its negation.

## Source locations

* IUT III, Definition 1.1, (i), text l.1259-1351 (`Ψ~`, ind-topological field,
  the `G_v(†Π_v)`-action).
* IUT I, Definition 5.2 (v)-(vi) (finite-stage Galois action and its
  continuity), as formalised in `SourceDefinition52LocalJointContinuity`.
* Upstream actual sources: `FinitePlaceSourceAlgebraicClosure` (spectral norm),
  `FinitePlaceSourceAlgebraicUnitPerfection` (the action),
  `FinitePlaceSourceIndTopology` (the ind topology and the homeomorphism),
  `Mathlib/FieldTheory/KrullTopology.lean` (Krull topology as the group filter
  basis of finite-dimensional fixing subgroups).
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual
open scoped Topology

namespace LeanFormal.IUT.XiFPaper.S1975JointContinuityActual

variable {K : Type*} [Field K] [NumberField K]
variable (place : NumberField.FinitePlace K)

/-! ## 0. The actual carriers -/

/-- The actual algebraic closure of the completion, i.e. `Θ` such that
`Ψ~ ≃ₜ Θ` (`sourceUnitPerfectionIndHomeomorph`). -/
abbrev Theta := SourceAlgebraicClosure place

/-- The actual local Galois group `G_v`, with the Krull topology
(`Mathlib.FieldTheory.KrullTopology`, the group filter basis of
`E.fixingSubgroup` for finite-dimensional `E`). -/
abbrev Gv := SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
  SourceAlgebraicClosure place

/-- The ind topology of the genuine finite local subfields on the actual
algebraic closure (the topology transported to `Ψ~`). -/
abbrev indTopology : TopologicalSpace (Theta place) := sourceAlgebraicFieldIndTopology place

/-! ## 1. The actual action is by isometries for the spectral norm -/

/-- **Every actual `G_v`-automorphism of `Θ` preserves the spectral norm.**
`Θ` is the algebraic closure of the completion with the spectral norm, so
`‖x‖ = spectralNorm ℚ_[p] Θ x` definitionally, and the spectral norm is
invariant under `ℚ_[p]`-algebra maps out of an algebraic extension
(`spectralNorm_algHom_eq`).  This is the compatibility of the action with the
finite-stage metrics that the joint-continuity argument needs; it is proved,
not assumed. -/
theorem norm_galois_smul (σ : Gv place) (x : Theta place) : ‖σ x‖ = ‖x‖ := by
  rw [show ‖σ x‖ = spectralNorm (PadicScalarField place) (SourceAlgebraicClosure place) (σ x)
      from rfl,
    show ‖x‖ = spectralNorm (PadicScalarField place) (SourceAlgebraicClosure place) x
      from rfl]
  exact LeanFormal.IUT.IUTII.Frobenioid.Example36.spectralNorm_algHom_eq
    (K := PadicScalarField place) (A := SourceAlgebraicClosure place)
    (B := SourceAlgebraicClosure place)
    (σ.restrictScalars (PadicScalarField place)) x

/-! ## 2. Balls are ind-open, and the formal inclusion of topologies -/

/-- **Absolute-value balls are open for the ind topology.**  This is the only
direction that the final-topology characterisation
`isOpen_algebraicFieldIndTopology_iff` gives for free: on every finite local
subfield `F` the trace of the ball is a ball of `F`, which is open there
because the inclusion `F ↪ Θ` is an isometry
(`isometry_intermediateField_inclusion`). -/
theorem isOpen_ind_ball (z : Theta place) {ε : ℝ} (hε : 0 < ε) :
    IsOpen[indTopology place] {y | ‖y - z‖ < ε} := by
  rw [isOpen_algebraicFieldIndTopology_iff]
  intro F
  have hcont : Continuous fun y : F.val => ((y : SourceAlgebraicClosure place) - z) :=
    (isometry_intermediateField_inclusion F.val).continuous.sub continuous_const
  exact isOpen_lt (continuous_norm.comp hcont) continuous_const

/-- **The ind topology is finer than the norm topology**: every norm-open set is
ind-open.  This is the inclusion that `isOpen_algebraicFieldIndTopology_iff`
amounts to, and the only one available in the tree. -/
theorem ind_le_norm :
    sourceAlgebraicFieldIndTopology place ≤
      (inferInstance : TopologicalSpace (Theta place)) := by
  rw [TopologicalSpace.le_def]
  intro O hO
  rw [isOpen_algebraicFieldIndTopology_iff]
  intro F
  exact hO.preimage (isometry_intermediateField_inclusion F.val).continuous

/-! ## 3. The exact first missing input -/

/-- **The exact first missing (S1975).**  Every ind-open set containing `z`
contains an absolute-value ball around `z`.

This is *not* a restatement of the definition of the ind topology: the
definition says which sets are open, and openness is a condition on every
finite subfield separately, with a ball radius a priori depending on the
subfield.  `indCarrierBallNeighborhood_iff` below shows that this proposition is
exactly the statement that the ind topology coincides with the spectral norm
topology. -/
def IndCarrierBallNeighborhood : Prop :=
  ∀ (O : Set (Theta place)),
    IsOpen[sourceAlgebraicFieldIndTopology place] O →
      ∀ z ∈ O, ∃ ε : ℝ, 0 < ε ∧ ∀ y, ‖y - z‖ < ε → y ∈ O

/-- The ball-neighbourhood property is available as soon as the ind topology is
the norm topology. -/
theorem ballNeighborhood_of_ind_eq_norm
    (h : sourceAlgebraicFieldIndTopology place =
      (inferInstance : TopologicalSpace (Theta place))) :
    IndCarrierBallNeighborhood place := by
  intro O hO z hz
  have hnorm : @IsOpen _ (inferInstance : TopologicalSpace (Theta place)) O := by
    rw [← h]
    exact hO
  rw [Metric.isOpen_iff] at hnorm
  obtain ⟨ε, hε, hball⟩ := hnorm z hz
  exact ⟨ε, hε, fun y hy => hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hy)⟩

/-- Conversely the ball-neighbourhood property forces the ind topology to be the
norm topology: it makes every ind-open set norm-open. -/
theorem norm_le_ind_of_ballNeighborhood (h : IndCarrierBallNeighborhood place) :
    (inferInstance : TopologicalSpace (Theta place)) ≤
      sourceAlgebraicFieldIndTopology place := by
  rw [TopologicalSpace.le_def]
  intro O hO
  rw [Metric.isOpen_iff]
  intro z hz
  obtain ⟨ε, hε, hεO⟩ := h O hO z hz
  exact ⟨ε, hε, fun y hy => hεO y (by rw [← dist_eq_norm]; exact hy)⟩

/-- **The exact first missing is the reverse inclusion of topologies.**  So the
gap in S1962 is not "one more continuity argument" but the statement that the
final topology of the finite local subfields is already the norm topology;
`ind_le_norm` is the other, formal, inequality. -/
theorem indCarrierBallNeighborhood_iff :
    IndCarrierBallNeighborhood place ↔
      sourceAlgebraicFieldIndTopology place =
        (inferInstance : TopologicalSpace (Theta place)) := by
  constructor
  · intro h
    exact le_antisymm (ind_le_norm place) (norm_le_ind_of_ballNeighborhood place h)
  · intro h
    exact ballNeighborhood_of_ind_eq_norm place h

/-! ## 4. The reduction: the missing input implies joint continuity on the limit -/

/-- The joint evaluation map of the actual `G_v`-action on the algebraic
closure, with the ind topology on the target.  This is the transport of
`R1JointContinuousActionMissing` along `sourceUnitPerfectionIndHomeomorph`. -/
def JointContinuousGaloisEvaluation : Prop :=
  letI := sourceAlgebraicFieldIndTopology place
  Continuous fun p : Gv place × Theta place => p.1 p.2

/-- **Continuity with parameters for the actual action, from the missing ball
input.**  At a point `(σ₀, y₀)` the neighbourhood of `σ₀` is the open coset
`σ₀ · Gal(Θ/E)` of the stabiliser of `y₀` (open because `y₀` generates a
finite-dimensional subextension, `stabilizer_isOpen_of_isIntegral`), and the
neighbourhood of `y₀` is an ind-open ball.  On that product,
`σ y - σ₀ y₀ = σ (y - y₀)`, so the isometry `norm_galois_smul` transports the
smallness of `y - y₀` to `σ y - σ₀ y₀`, which lands in the prescribed
ind-open set. -/
theorem jointContinuousGaloisEvaluation_of_ballNeighborhood
    (h : IndCarrierBallNeighborhood place) :
    JointContinuousGaloisEvaluation place := by
  letI := sourceAlgebraicFieldIndTopology place
  change Continuous fun p : Gv place × Theta place => p.1 p.2
  rw [continuous_def]
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro ⟨σ₀, y₀⟩ hmem
  obtain ⟨ε, hε, hεO⟩ := h O hO (σ₀ y₀) hmem
  rw [nhds_prod_eq]
  have hH : IsOpen (MulAction.stabilizer (Gv place) y₀ : Set (Gv place)) :=
    stabilizer_isOpen_of_isIntegral y₀
  have hUopen : IsOpen {σ : Gv place | σ₀⁻¹ * σ ∈ MulAction.stabilizer (Gv place) y₀} :=
    hH.preimage (continuous_const.mul continuous_id)
  have hUne : {σ : Gv place | σ₀⁻¹ * σ ∈ MulAction.stabilizer (Gv place) y₀} ∈ 𝓝 σ₀ :=
    hUopen.mem_nhds (by simp)
  have hVopen : IsOpen {y : Theta place | ‖y - y₀‖ < ε} := isOpen_ind_ball place y₀ hε
  have hVne : {y : Theta place | ‖y - y₀‖ < ε} ∈ 𝓝 y₀ :=
    hVopen.mem_nhds (by simpa using hε)
  refine Filter.mem_of_superset (Filter.prod_mem_prod hUne hVne) ?_
  rintro ⟨σ, y⟩ ⟨hσ, hy⟩
  have hmemH : σ₀⁻¹ * σ ∈ MulAction.stabilizer (Gv place) y₀ := hσ
  have hτ : ((σ₀⁻¹ * σ : Gv place)) y₀ = y₀ := by
    have h := (MulAction.mem_stabilizer_iff).mp hmemH
    rwa [AlgEquiv.smul_def, AlgEquiv.mul_apply] at h
  have hσeq : σ = σ₀ * (σ₀⁻¹ * σ) := by group
  have hfix : σ y₀ = σ₀ y₀ := by rw [hσeq, AlgEquiv.mul_apply, hτ]
  have hdiff : σ y - σ₀ y₀ = σ (y - y₀) := by
    rw [← hfix, ← map_sub]
  have hnorm : ‖σ y - σ₀ y₀‖ = ‖y - y₀‖ := by
    rw [hdiff, norm_galois_smul place σ (y - y₀)]
  exact hεO (σ y) (by rw [hnorm]; simpa using hy)

/-! ## 5. Transport to `Ψ~` and to the S1962 target -/

/-- The transported action on `Ψ~` is the actual Galois action on `Θ`
conjugated by the actual ind-topological homeomorphism
`Ψ~ ≃ₜ Θ`.  This is `sourceUnitPerfectionEquiv_galois_smul` rewritten through
the homeomorphism; no continuity is used. -/
theorem psiTilde_smul_eq_homeomorph_conj (σ : Gv place)
    (x : SourceUnitPerfection place) :
    letI := sourceUnitPerfectionGaloisAction place
    letI := sourceUnitPerfectionIndTopology place
    letI := sourceAlgebraicFieldIndTopology place
    σ • x = (sourceUnitPerfectionIndHomeomorph place).symm
      (σ ((sourceUnitPerfectionIndHomeomorph place) x)) := by
  letI := sourceUnitPerfectionGaloisAction place
  letI := sourceUnitPerfectionIndTopology place
  letI := sourceAlgebraicFieldIndTopology place
  have h := sourceUnitPerfectionIndHomeomorph_galois_smul place σ x
  have h2 := congrArg (sourceUnitPerfectionIndHomeomorph place).symm h
  simpa using h2

/-- **Joint continuity on the limit, on `Ψ~` itself**, obtained from the
algebraic-closure model by conjugating with the actual ind-topological
homeomorphism `Ψ~ ≃ₜ Θ`. -/
theorem jointContinuous_psiTilde (h : JointContinuousGaloisEvaluation place) :
    letI := sourceUnitPerfectionGaloisAction place
    letI := sourceUnitPerfectionIndTopology place
    Continuous fun p : Gv place × SourceUnitPerfection place => p.1 • p.2 := by
  letI := sourceUnitPerfectionGaloisAction place
  letI := sourceUnitPerfectionIndTopology place
  letI := sourceAlgebraicFieldIndTopology place
  have hconj : (fun p : Gv place × SourceUnitPerfection place => p.1 • p.2) =
      (fun q : Gv place × Theta place =>
          (sourceUnitPerfectionIndHomeomorph place).symm (q.1 q.2)) ∘
        (fun p : Gv place × SourceUnitPerfection place =>
          (p.1, sourceUnitPerfectionIndHomeomorph place p.2)) := by
    funext p
    exact psiTilde_smul_eq_homeomorph_conj place p.1 p.2
  rw [hconj]
  have heval : Continuous fun q : Gv place × Theta place => q.1 q.2 := h
  refine ((sourceUnitPerfectionIndHomeomorph place).symm.continuous.comp heval).comp ?_
  exact continuous_fst.prodMk ((sourceUnitPerfectionIndHomeomorph place).continuous.comp
    continuous_snd)

/-- **S1975 main reduction, in the exact form of the S1962 missing.**
`IndCarrierBallNeighborhood (QPlace v)` implies S1962's
`R1JointContinuousActionMissing v`.

The hypothesis is *not* discharged anywhere in this file: it is the exact first
missing, and (by `indCarrierBallNeighborhood_iff`) it is the statement that the
ind topology is the norm topology.  In particular this theorem does not assert
joint continuity, it localises it. -/
theorem r1JointContinuous_of_ballNeighborhood (v : FinitePrimePlace 2 7)
    (h : IndCarrierBallNeighborhood (QPlace v)) :
    R1JointContinuousActionMissing v := by
  have hΩ := jointContinuousGaloisEvaluation_of_ballNeighborhood (QPlace v) h
  have hΨ := jointContinuous_psiTilde (QPlace v) hΩ
  exact hΨ

/-! ## 6. Axiom probes -/

#print axioms norm_galois_smul
#print axioms isOpen_ind_ball
#print axioms ind_le_norm
#print axioms indCarrierBallNeighborhood_iff
#print axioms jointContinuousGaloisEvaluation_of_ballNeighborhood
#print axioms jointContinuous_psiTilde
#print axioms r1JointContinuous_of_ballNeighborhood

end LeanFormal.IUT.XiFPaper.S1975JointContinuityActual

end