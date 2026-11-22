import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmQuotientTopology
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmRationalization
import LeanFormal.IUT.Foundations.LocalFields.ContinuousRationalPadicScalars
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1Ind1UnitQuotientActual
open LeanFormal.IUT LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

universe uK uL
variable {K : Type uK} [NormedField K] [IsUltrametricDist K]
variable {L : Type uL} [NormedField L] [IsUltrametricDist L]
variable {p : Nat} [Fact p.Prime]
variable [CharZero K] [CompleteSpace K] [ProperSpace K]
variable [CharZero L] [CompleteSpace L] [ProperSpace L]
variable [NormedAlgebra ℚ_[p] K] [NormedAlgebra ℚ_[p] L]

/-- A continuous unit-quotient action induces an isomorphism of the actual
logarithm ranges.  This is step (1) of the Ind1 construction: it uses the
proved torsion quotient/log-image equivalence, not a chosen field isomorphism. -/
def unitLogQuotientEquivOfMulEquiv
    (β : ((Integers K)ˣ ⧸ CommGroup.torsion (Integers K)ˣ) ≃*
      ((Integers L)ˣ ⧸ CommGroup.torsion (Integers L)ˣ)) :
    (unitLogHom (K := K) (p := p)).range ≃*
      (unitLogHom (K := L) (p := p)).range :=
  (unitLogTorsionQuotientEquivRange (K := K) (p := p)).symm.trans
    (β.trans (unitLogTorsionQuotientEquivRange (K := L) (p := p)))

#print axioms unitLogQuotientEquivOfMulEquiv
end LeanFormal.IUT.XiFPaper.Mzk1Ind1UnitQuotientActual