import tmp.sheaf.n8.closure.EtaPAdicDetHaarScalingActual
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Eta determinant/index bridge attempt 2

Mathlib CardQuotient proves, for a free Z-module basis bE and an additive
subgroup N with a basis bN,

  N.index = natAbs (bE.det bN)

and, over a Q-vector space with lattice closures,

  L1.relIndex L2 = |b2.det b1|.

These are the available determinant/index theorems.  They are stated over Z
(ordinary absolute value) or over Q, not over Q_p with the p-adic norm, and do
not identify the Q_p-linear determinant of an arbitrary f with the index of
its lattice image.  That p-adic basis-change/determinant comparison remains the
exact missing bridge.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false
set_option linter.deprecated false

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.EtaTensorBlockDetActual
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGaussianActionVolumeFromDetActual
open LeanFormal.IUT.N8Closure.EtaPAdicDetHaarScaling
open LeanFormal.IUT.N8Closure.EtaPAdicDetHaarScalingActual
open scoped TensorProduct

namespace LeanFormal.IUT.N8Closure.EtaDetIndexBridgeActual2

universe u v

variable {p : Nat} [Fact p.Prime]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type) [∀ i, NormedField (A i)]
  [∀ i, NormedAlgebra ℚ_[p] (A i)] [∀ i, FiniteDimensional ℚ_[p] (A i)]
variable (j : ι)

abbrev E : Type := (⨂[ℚ_[p]] (i : ι), A i)

variable [MeasurableSpace (E (p := p) A)] [BorelSpace (E (p := p) A)]

/-- Actual Mathlib index/determinant theorem available: index of a full-rank
Z-subgroup equals natAbs of the basis-change determinant. -/
theorem mathlib_index_eq_natAbs_det
    {M : Type u} [AddCommGroup M] {κ : Type v} [DecidableEq κ] [Fintype κ]
    (bM : Module.Basis κ ℤ M) (N : AddSubgroup M) (bN : Module.Basis κ ℤ N) :
    N.index = (bM.det (bN ·)).natAbs :=
  AddSubgroup.index_eq_natAbs_det bM N bN

/-- Actual Mathlib relative-index/determinant theorem over Q. -/
theorem mathlib_relIndex_eq_abs_det
    {V : Type u} [AddCommGroup V] [Module ℚ V]
    (L₁ L₂ : AddSubgroup V) (H : L₁ ≤ L₂)
    {κ : Type v} [DecidableEq κ] [Fintype κ]
    (b₁ b₂ : Module.Basis κ ℚ V)
    (h₁ : L₁ = AddSubgroup.closure (Set.range b₁))
    (h₂ : L₂ = AddSubgroup.closure (Set.range b₂)) :
    L₁.relIndex L₂ = |b₂.det b₁| :=
  AddSubgroup.relIndex_eq_abs_det L₁ L₂ H b₁ b₂ h₁ h₂

/-- Exact p-adic missing bridge: determinant/Haar scaling for additive Haar on
the Q_p tensor block. -/
def MissingPAdicDetHaarScalingBridge : Prop :=
  PAdicDetHaarScalingTheorem (p := p) A

/-- The missing p-adic bridge is exactly the p-adic determinant/Haar scaling
theorem. -/
theorem missingBridge_iff_target :
    MissingPAdicDetHaarScalingBridge (p := p) A ↔
      PAdicDetHaarScalingTheorem (p := p) A :=
  Iff.rfl

/-- Conditional Gaussian action-volume closure from the missing p-adic
determinant/index bridge. -/
theorem gaussianActionVolume_of_pAdicDetIndexBridge
    (h : MissingPAdicDetHaarScalingBridge (p := p) A)
    (μ : Measure (E (p := p) A)) [μ.IsAddHaarMeasure]
    (g : A j) (S : Set (E (p := p) A))
    (hnorm : Algebra.norm ℚ_[p] g ≠ 0)
    (hSmeas : MeasurableSet S) (hSpos : 0 < μ S) (hSfin : μ S < ⊤) :
    normalizedLogVolume (p := p) A μ
        (gaussianAction (p := p) A j g '' S) -
      normalizedLogVolume (p := p) A μ S =
      Real.log ‖(Algebra.norm ℚ_[p] g : ℚ_[p])‖ /
        (factorDim (p := p) A j : Real) :=
  gaussianActionVolume_of_pAdicDetHaarScaling (p := p) A j
    ((missingBridge_iff_target (p := p) A).mp h)
    μ g S hnorm hSmeas hSpos hSfin

end LeanFormal.IUT.N8Closure.EtaDetIndexBridgeActual2
