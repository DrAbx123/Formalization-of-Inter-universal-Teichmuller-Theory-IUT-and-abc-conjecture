/- Route 7.2: for a monogenic integer ring, the local different order is the additive order
of the derivative of the generator. -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalMonogenicLocalActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1UniversalMonogenicOrderActual

open Polynomial
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalMonogenicLocalActual

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
  [IsDedekindDomain (Integers L)] [IsDiscreteValuationRing (Integers L)]

/-- Monogenic case: the local different order is the additive order of f'(generator). -/
theorem localDifferentOrder_eq_addVal_derivative_of_monogenic
    (M : MonogenicIntegers (p := p) (L := L)) :
    localDifferentOrder (p := p) (L := L) =
      (IsDiscreteValuationRing.addVal (Integers L)
        (aeval M.x (derivative (minpoly ℤ_[p] M.x)))).toNat := by
  haveI : IsDiscreteValuationRing (Integers L) := integersIsDiscreteValuationRing (p := p) (L := L)
  have hdiff : localDifferentIdeal (p := p) (L := L) =
      Ideal.span {aeval M.x (derivative (minpoly ℤ_[p] M.x))} :=
    localDifferentIdeal_eq_span_derivative_of_monogenic M
  have hassoc : Associated (localDifferentGenerator (p := p) (L := L))
      (aeval M.x (derivative (minpoly ℤ_[p] M.x))) := by
    have hgen : Submodule.IsPrincipal.generator (localDifferentIdeal (p := p) (L := L)) =
        Submodule.IsPrincipal.generator
          (Ideal.span {aeval M.x (derivative (minpoly ℤ_[p] M.x))}) :=
      congrArg (fun I : Ideal (Integers L) => Submodule.IsPrincipal.generator I) hdiff
    rw [localDifferentGenerator, hgen]
    exact Submodule.IsPrincipal.associated_generator_span_self _
  rw [localDifferentOrder]
  exact congrArg ENat.toNat
    ((IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr hassoc)

#print axioms localDifferentOrder_eq_addVal_derivative_of_monogenic
end LeanFormal.IUT.XiFPaper.Mzk1G1UniversalMonogenicOrderActual
