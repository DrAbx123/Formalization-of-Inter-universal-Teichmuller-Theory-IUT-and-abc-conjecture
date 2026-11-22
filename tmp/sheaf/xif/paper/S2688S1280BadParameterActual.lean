import tmp.sheaf.xif.paper.SourceQvCandidateActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.SourceQvCandidateActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2688S1280BadParameterActual

local instance s2688GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2688FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- The actual S1280 bad-place q parameter, taken from the closed source q_v
theorem via SourceQvCandidateActual.  This is the literal parameter field of
BadPlaceUniformizationContract for S1280Selection. -/
noncomputable def S2688S1280BadParameter (l : PrimeGeFive) :
    forall (w : NumberField.FinitePlace (S1280Arithmetic l).F),
      NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
        (S1280Selection l).V_mod_bad ->
      NumberFieldFinitePlace.FinitePlaceQCandidate w :=
  fun w hw =>
    sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
      ((S1280ReductionCards l).splitMultiplicativeReduction w hw)

/-- The parameter is exactly the SourceQvCandidate selected from the closed
source q_v theorem, hence not an arbitrary Classical.choice of DVR data. -/
theorem S2688S1280BadParameter_eq (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad) :
    S2688S1280BadParameter l w hw =
      sourceQvCandidate (F := (S1280Arithmetic l).F) w (S1280Arithmetic l).curve
        ((S1280ReductionCards l).splitMultiplicativeReduction w hw) := rfl

/-- The q of the actual S1280 bad parameter is nonzero. -/
theorem S2688S1280BadParameter_q_ne_zero (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad) :
    (S2688S1280BadParameter l w hw).q ≠ 0 :=
  (S2688S1280BadParameter l w hw).q_ne_zero

#check S2688S1280BadParameter
#check S2688S1280BadParameter_eq
#check S2688S1280BadParameter_q_ne_zero
#print axioms S2688S1280BadParameter_eq
end LeanFormal.IUT.XiFPaper.S2688S1280BadParameterActual
end
