import tmp.sheaf.xif.paper.S2806TateParameterActual
import tmp.sheaf.xif.paper.S2786PlaceBlockActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceTateComparisonSynthesis
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlaceTateComparisonConstruction
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2806TateParameterActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

local instance s2814GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual

variable (P : SourcePlaceSelection S2786Arithmetic)

/-- Uniform q-candidate for every bad place, from S2806. -/
noncomputable def S2814Parameter
    (w : NumberField.FinitePlace S2786Arithmetic.F)
    (_hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ P.V_mod_bad) :
    NumberFieldFinitePlace.FinitePlaceQCandidate w :=
  S2806Candidate (show NumberField.FinitePlace GaussianField from w)

/-- The order is 1, hence coprime to 5. -/
theorem S2814_order_coprime
    (w : NumberField.FinitePlace S2786Arithmetic.F)
    (_hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ P.V_mod_bad) :
    Nat.Coprime (S2814Parameter P w _hw).order S2771FiveLabel.value := by
  change Nat.Coprime (S2806Candidate w).order 5
  exact S2806Candidate_order_coprime w

/-- The contract with realization supplied as an explicit hypothesis.  This is
the only genuine remaining input: no CurveIndexedTateUniformization constructor
exists. -/
noncomputable def S2814BadPlaceContract_of_realization
    (hreal : forall (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Parameter P w _hw)) :
    BadPlaceUniformizationContract P where
  parameter := S2814Parameter P
  realization := hreal
  order_coprime := S2814_order_coprime P

#check S2814Parameter
#check S2814_order_coprime
#check S2814BadPlaceContract_of_realization
#print axioms S2814_order_coprime
#print axioms S2814BadPlaceContract_of_realization

end LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual
end
