import tmp.sheaf.xif.paper.PaperRootExtensionValuedActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-! # Actual discrete valuation on the finite root extension -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

noncomputable section
open scoped BigOperators Pointwise NNReal Valued

namespace LeanFormal.IUT.XiFPaper.PaperRootExtensionDiscreteValuationActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionValuedActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The integer ring of L is compact (it is the closed unit ball, and L is proper). -/
theorem rootIntegers_compactSpace : CompactSpace (Integers (rootNormedExtension T b)) := by
  have hcompact : IsCompact (Integers (rootNormedExtension T b) :
      Set (rootNormedExtension T b)) := by
    have heq : (Integers (rootNormedExtension T b) : Set (rootNormedExtension T b)) =
        Metric.closedBall (0 : rootNormedExtension T b) 1 := by
      ext x
      change x ∈ (NormedField.valuation (K := rootNormedExtension T b)).integer ↔
        x ∈ Metric.closedBall (0 : rootNormedExtension T b) 1
      rw [mem_integers_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    rw [heq]
    exact isCompact_closedBall (0 : rootNormedExtension T b) 1
  exact isCompact_iff_compactSpace.mp hcompact

/-- Actual DVR structure on the integer ring of L. -/
noncomputable instance rootIntegersIsDVR :
    IsDiscreteValuationRing (Integers (rootNormedExtension T b)) := by
  letI : CompactSpace (Integers (rootNormedExtension T b)) :=
    rootIntegers_compactSpace (T := T) (b := b)
  obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial
    (α := rootNormedExtension T b)
  have hxne : x ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hx
    linarith
  have hxinv : ‖x⁻¹‖ < 1 := by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ hx
  have hn : (Valued.v : Valuation (rootNormedExtension T b) ℝ≥0).IsNontrivial :=
    (Valuation.isNontrivial_iff_exists_lt_one
      (v := (Valued.v : Valuation (rootNormedExtension T b) ℝ≥0))).mpr
      ⟨x⁻¹, inv_ne_zero hxne, by
        rw [NormedField.v_eq_valuation, NormedField.valuation_apply]
        rw [← NNReal.coe_lt_coe]
        simpa using hxinv⟩
  letI : (Valued.v : Valuation (rootNormedExtension T b) ℝ≥0).IsNontrivial := hn
  exact Valued.integer.isDiscreteValuationRing_of_compactSpace
    (K := rootNormedExtension T b) (Γ₀ := ℝ≥0)

/-- An actual uniformizer of L (an irreducible element of the integer ring). -/
noncomputable def rootUniformizer :
    Integers (rootNormedExtension T b) :=
  (IsDiscreteValuationRing.exists_irreducible
    (Integers (rootNormedExtension T b))).choose

/-- The uniformizer is irreducible. -/
theorem rootUniformizer_irreducible :
    Irreducible (rootUniformizer T b) :=
  (IsDiscreteValuationRing.exists_irreducible
    (Integers (rootNormedExtension T b))).choose_spec

/-- The actual discrete valuation on L, obtained from the maximal ideal of the
integer ring. -/
noncomputable def rootDiscreteValuation :
    Valuation (rootNormedExtension T b) (WithZero (Multiplicative ℤ)) :=
  (IsDiscreteValuationRing.maximalIdeal
    (Integers (rootNormedExtension T b))).valuation (rootNormedExtension T b)


end LeanFormal.IUT.XiFPaper.PaperRootExtensionDiscreteValuationActual

end