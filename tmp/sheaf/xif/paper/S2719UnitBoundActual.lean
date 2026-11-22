import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceArithmeticThetaPilotBridge
import tmp.sheaf.xif.paper.S2715CThetaPaperScaleActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual

namespace LeanFormal.IUT.XiFPaper.S2719UnitBoundActual

def thetaPilotTheorem110RHS (l : PrimeGeFive)
    (dmod logDifferentFtpd logConductorFtpd eStarMod etaPrm : Real) : Real :=
  (1 + 20 * dmod / (l.value : Real)) *
      (logDifferentFtpd + logConductorFtpd) +
    20 * (eStarMod * (l.value : Real) + etaPrm)

def thetaPilotArithmeticUpperTerm (l : PrimeGeFive)
    (absoluteLogQ dmod logDifferentFtpd logConductorFtpd eStarMod etaPrm : Real) : Real :=
  (((l.value : Real) + 1) / (4 * absoluteLogQ)) *
      ((1 + 12 * dmod / (l.value : Real)) *
        (logDifferentFtpd + logConductorFtpd) +
      10 * (eStarMod * (l.value : Real) + etaPrm))

theorem unit_bound_of_degree_bound
    {K : Type uK} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι → Type wV}
    {places : (i : ι) → Va i → FinitePlaceAtPrime K p}
    {tuple : (i : ι) → Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (degreeMap : Additive (ArithmeticTensorTupleBlock places tuple)ˣ →+ Real)
    (C : Real)
    (hdeg : ∀ a : (ArithmeticTensorTupleBlock places tuple)ˣ,
      (a : ArithmeticTensorTupleBlock places tuple) ∈
        arithmeticTupleCanonicalHull places tuple →
          degreeMap (Additive.ofMul a) ≤ C) :
    ∃ C : Real, ∀ a : (ArithmeticTensorTupleBlock places tuple)ˣ,
      (a : ArithmeticTensorTupleBlock places tuple) ∈
        arithmeticTupleCanonicalHull places tuple →
          degreeMap (Additive.ofMul a) ≤ C :=
  ⟨C, hdeg⟩

#check thetaPilotTheorem110RHS
#check thetaPilotArithmeticUpperTerm
#check unit_bound_of_degree_bound
#print axioms unit_bound_of_degree_bound

end LeanFormal.IUT.XiFPaper.S2719UnitBoundActual
end
