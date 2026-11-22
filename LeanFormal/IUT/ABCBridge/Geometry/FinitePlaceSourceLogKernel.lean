import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceLogShell
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel

/-!
# The torsion kernel on the actual arithmetic completion

The kernel theorem is transported through the proved isomorphism of the
actual completed integer rings. It applies to the project's original
`CompletionIntegers place`, not an assumed local source type.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem completionUnitLog_eq_zero_iff_isOfFinOrder (place : NumberField.FinitePlace K)
    (u : (CompletionIntegers place)ˣ) :
    completionUnitLog place u = 0 ↔ IsOfFinOrder u := by
  change normalizedCompletionRingEquiv place
    (unitLog ((normalizedCompletionUnitsEquiv place).symm u)) = 0 ↔ _
  rw [← map_zero (normalizedCompletionRingEquiv place),
    (normalizedCompletionRingEquiv place).injective.eq_iff,
    unitLog_eq_zero_iff_isOfFinOrder (p := (completionRationalPrime place).val)]
  exact Function.Injective.isOfFinOrder_iff
    (f := (normalizedCompletionUnitsEquiv place).symm.toMonoidHom)
    (normalizedCompletionUnitsEquiv place).symm.injective

theorem completionUnitLogHom_ker_eq_torsion (place : NumberField.FinitePlace K) :
    (completionUnitLogHom place).ker = CommGroup.torsion (CompletionIntegers place)ˣ := by
  ext u
  change completionUnitLog place u = 0 ↔ IsOfFinOrder u
  exact completionUnitLog_eq_zero_iff_isOfFinOrder place u

/-- The actual arithmetic quotient by torsion, with the induced logarithm. -/
def completionUnitLogTorsionQuotientHom (place : NumberField.FinitePlace K) :
    ((CompletionIntegers place)ˣ ⧸ CommGroup.torsion (CompletionIntegers place)ˣ) →*
      Multiplicative (Completion place) :=
  QuotientGroup.lift _ (completionUnitLogHom place) (by
    intro u hu
    change completionUnitLog place u = 0
    exact (completionUnitLog_eq_zero_iff_isOfFinOrder place u).mpr hu)

theorem completionUnitLogTorsionQuotientHom_mk (place : NumberField.FinitePlace K)
    (u : (CompletionIntegers place)ˣ) :
    completionUnitLogTorsionQuotientHom place (QuotientGroup.mk u) =
      Multiplicative.ofAdd (completionUnitLog place u) := rfl

theorem completionUnitLogTorsionQuotientHom_injective (place : NumberField.FinitePlace K) :
    Function.Injective (completionUnitLogTorsionQuotientHom place) := by
  intro a b
  refine Quotient.inductionOn₂' a b ?_
  intro u v h
  change completionUnitLogHom place u = completionUnitLogHom place v at h
  apply Quotient.sound'
  rw [QuotientGroup.leftRel_apply, ← completionUnitLogHom_ker_eq_torsion place,
    MonoidHom.mem_ker, map_mul, map_inv, ← h, inv_mul_cancel]

end

end LeanFormal.IUT.NumberFieldFinitePlace
