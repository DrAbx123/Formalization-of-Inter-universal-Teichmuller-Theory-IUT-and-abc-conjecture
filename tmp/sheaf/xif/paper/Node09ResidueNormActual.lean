import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange

namespace LeanFormal.IUT.XiFPaper.Node09ResidueNormActual

/-- Exact interface for the rational base residue norm: the only missing input
is the identification of the ideal absolute norm with the rational prime. -/
theorem residueNormBase_rat_eq_of_absNorm
    (place : NumberField.FinitePlace ℚ)
    (h : Ideal.absNorm place.maximalIdeal.asIdeal =
      (completionRationalPrime place).val) :
    residueNormBase place = ((completionRationalPrime place).val : ℝ) := by
  unfold residueNormBase
  rw [h]

/-- Exact remaining missing for the rational residue norm identification. -/
def Node09ResidueNormRemainingMissing : List String :=
  [ "habsNorm: Ideal.absNorm place.maximalIdeal.asIdeal = (completionRationalPrime place).val for rational places",
    "comap transport: absNorm_lower gives the statement for the comap place; rewriting comap to place failed (instance/motive), so the direct rational absNorm equality is recorded as the exact missing input" ]

end LeanFormal.IUT.XiFPaper.Node09ResidueNormActual
