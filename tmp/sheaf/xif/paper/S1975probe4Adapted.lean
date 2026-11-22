import tmp.sheaf.xif.paper.S1962R1AbstractActionActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open scoped Topology

namespace Probe4

variable {K : Type*} [Field K] [NumberField K]
variable (place : NumberField.FinitePlace K)

abbrev Theta := SourceAlgebraicClosure place
abbrev Gv := SourceAlgebraicClosure place ≃ₐ[NormalizedCompletion place]
  SourceAlgebraicClosure place

theorem isOpen_ind_ball (z : Theta place) {ε : ℝ} (hε : 0 < ε) :
    IsOpen[sourceAlgebraicFieldIndTopology place] {y | ‖y - z‖ < ε} := by
  rw [isOpen_algebraicFieldIndTopology_iff]
  intro F
  have hcont : Continuous fun y : F.val => ((y : SourceAlgebraicClosure place) - z) :=
    (isometry_intermediateField_inclusion F.val).continuous.sub continuous_const
  exact isOpen_lt (continuous_norm.comp hcont) continuous_const

theorem norm_galois_smul
    (σ : Gv place) (x : Theta place) : ‖σ x‖ = ‖x‖ := by
  rw [show ‖σ x‖ = spectralNorm (PadicScalarField place) (SourceAlgebraicClosure place) (σ x) from rfl,
    show ‖x‖ = spectralNorm (PadicScalarField place) (SourceAlgebraicClosure place) x from rfl]
  exact LeanFormal.IUT.IUTII.Frobenioid.Example36.spectralNorm_algHom_eq
    (K := PadicScalarField place) (A := SourceAlgebraicClosure place)
    (B := SourceAlgebraicClosure place)
    (σ.restrictScalars (PadicScalarField place)) x

/-- The exact missing analytic input (ball-neighborhood form of the ind topology). -/
def IndCarrierBallNeighborhood : Prop :=
  ∀ (O : Set (Theta place)),
    IsOpen[sourceAlgebraicFieldIndTopology place] O →
      ∀ z ∈ O, ∃ ε : ℝ, 0 < ε ∧ ∀ y, ‖y - z‖ < ε → y ∈ O

/-- The joint evaluation map on the algebraic-closure model, ind topology target. -/
def JointContinuousGaloisEvaluation : Prop :=
  letI := sourceAlgebraicFieldIndTopology place
  Continuous fun p : Gv place × Theta place => p.1 p.2

instance algebraIsIntegralTheta : Algebra.IsIntegral (NormalizedCompletion place) (Theta place) :=
  inferInstance

theorem jointContinuous_of_ballNeighborhood (h : IndCarrierBallNeighborhood place) :
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

end Probe4
