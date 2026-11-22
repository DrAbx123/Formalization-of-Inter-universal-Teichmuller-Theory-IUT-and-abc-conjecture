import tmp.sheaf.xif.paper.S782FiniteRootStackExtensionActual
import tmp.sheaf.xif.paper.S902RootStackDVRInstancesActual
import tmp.sheaf.xif.paper.S1121RootStackNormedFieldActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Analysis.Normed.Algebra.Basic

/-! # S1116: actual DVR instance and uniformizer for E = rootStackExtension -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators Pointwise NNReal Valued

namespace LeanFormal.IUT.XiFPaper.S1116ERootStackDVRInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open LeanFormal.IUT.XiFPaper.S902RootStackDVRInstancesActual
open LeanFormal.IUT.LocalFieldIntegralUnits

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
noncomputable instance s1116NormedAlgebraL :
    NormedAlgebra (rootNormedExtension T b) (rootStackExtension T b) where
  norm_smul_le r x := by
    change ‖(algebraMap (rootNormedExtension T b) (rootStackExtension T b) r) *
        (x : rootStackExtension T b)‖ ≤
      ‖r‖ * ‖(x : rootStackExtension T b)‖
    rw [norm_mul]
    have h : ‖(algebraMap (rootNormedExtension T b) (rootStackExtension T b) r :
        rootStackExtension T b)‖ = ‖r‖ := rfl
    rw [h]
noncomputable instance s1116Valued :
    Valued (rootStackExtension T b) ℝ≥0 :=
  NormedField.toValued
noncomputable instance s1116NormedAlgebraQp :
    NormedAlgebra ℚ_[(qVFamTensorP T b)] (rootStackExtension T b) :=
  NormedAlgebra.restrictScalars ℚ_[(qVFamTensorP T b)]
    (rootNormedExtension T b) (rootStackExtension T b)
noncomputable instance s1116NontriviallyNormedField :
    NontriviallyNormedField (rootStackExtension T b) where
  non_trivial := by
    refine ⟨(algebraMap ℚ_[(qVFamTensorP T b)] (rootStackExtension T b)
      ((qVFamTensorP T b : ℚ_[(qVFamTensorP T b)])))⁻¹, ?_⟩
    rw [norm_inv, norm_algebraMap', Padic.norm_p, inv_inv]
    have hprime : Nat.Prime (qVFamTensorP T b) := Fact.out
    exact_mod_cast hprime.one_lt

theorem rootStackIntegers_compactSpace :
    CompactSpace (Integers (rootStackExtension T b)) := by
  letI : IsUltrametricDist (rootStackExtension T b) :=
    s902RootStackUltrametric (l := l) T b
  have hcompact : IsCompact (Integers (rootStackExtension T b) :
      Set (rootStackExtension T b)) := by
    have heq : (Integers (rootStackExtension T b) : Set (rootStackExtension T b)) =
        Metric.closedBall (0 : rootStackExtension T b) 1 := by
      ext x
      change x ∈ (NormedField.valuation (K := rootStackExtension T b)).integer ↔
        x ∈ Metric.closedBall (0 : rootStackExtension T b) 1
      rw [mem_integers_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [heq]
    exact isCompact_closedBall (0 : rootStackExtension T b) 1
  exact isCompact_iff_compactSpace.mp hcompact

noncomputable instance rootStackIntegersIsDVR :
    IsDiscreteValuationRing (Integers (rootStackExtension T b)) := by
  letI : IsUltrametricDist (rootStackExtension T b) :=
    s902RootStackUltrametric (l := l) T b
  letI : CompactSpace (Integers (rootStackExtension T b)) :=
    rootStackIntegers_compactSpace (l := l) T b
  obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial
    (α := rootStackExtension T b)
  have hxne : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hx
    linarith
  have hxinv : ‖x⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hx
  have hn : (Valued.v : Valuation (rootStackExtension T b) ℝ≥0).IsNontrivial :=
    (Valuation.isNontrivial_iff_exists_lt_one
      (v := (Valued.v : Valuation (rootStackExtension T b) ℝ≥0))).mpr
      ⟨x⁻¹, inv_ne_zero hxne, by
        rw [NormedField.v_eq_valuation, NormedField.valuation_apply]
        rw [← NNReal.coe_lt_coe]
        simpa using hxinv⟩
  letI : (Valued.v : Valuation (rootStackExtension T b) ℝ≥0).IsNontrivial := hn
  exact Valued.integer.isDiscreteValuationRing_of_compactSpace
    (K := rootStackExtension T b) (Γ₀ := ℝ≥0)

noncomputable def rootStackUniformizer :
    Integers (rootStackExtension T b) :=
  (IsDiscreteValuationRing.exists_irreducible
    (Integers (rootStackExtension T b))).choose

theorem rootStackUniformizer_irreducible :
    Irreducible (rootStackUniformizer T b) :=
  (IsDiscreteValuationRing.exists_irreducible
    (Integers (rootStackExtension T b))).choose_spec

end LeanFormal.IUT.XiFPaper.S1116ERootStackDVRInstanceActual

end
