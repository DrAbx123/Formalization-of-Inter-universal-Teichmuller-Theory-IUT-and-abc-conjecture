/- Route 7.2, unramified case: the actual local different order equals the additive order of
the derivative of the monogenic generator. -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalUnramifiedCaseActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalUnramifiedOrderActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalMonogenicLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalUnramifiedCaseActual

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [IsDedekindDomain (Integers L)]

/-- Unramified case: the local different order is the additive order of the derivative of the
monogenic generator. -/
theorem localDifferentOrder_eq_addVal_derivative_of_unramified
    (hunram : IsLocalRing.maximalIdeal (Integers L) =
      Ideal.span ({(p : Integers L)} : Set (Integers L))) :
    ∃ M : MonogenicIntegers (p := p) (L := L),
      localDifferentOrder (p := p) (L := L) =
        (IsDiscreteValuationRing.addVal (Integers L)
          (aeval M.x (derivative (minpoly ℤ_[p] M.x)))).toNat := by
  obtain ⟨M⟩ := nonempty_monogenicIntegers_of_unramified (p := p) (L := L) hunram
  refine ⟨M, ?_⟩
  haveI : IsDiscreteValuationRing (Integers L) := integersIsDiscreteValuationRing (p := p) (L := L)
  have hdiff : localDifferentIdeal (p := p) (L := L) =
      Ideal.span {aeval M.x (derivative (minpoly ℤ_[p] M.x))} :=
    localDifferentIdeal_eq_span_derivative_of_monogenic M
  have hassoc : Associated (localDifferentGenerator (p := p) (L := L))
      (aeval M.x (derivative (minpoly ℤ_[p] M.x))) := by
    rw [localDifferentGenerator]
    rw [hdiff]
    exact Submodule.IsPrincipal.associated_generator_span_self _
  rw [localDifferentOrder]
  exact congrArg ENat.toNat (IsDiscreteValuationRing.addVal_eq_iff_associated.mpr hassoc)

#print axioms localDifferentOrder_eq_addVal_derivative_of_unramified
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalUnramifiedOrderActual
