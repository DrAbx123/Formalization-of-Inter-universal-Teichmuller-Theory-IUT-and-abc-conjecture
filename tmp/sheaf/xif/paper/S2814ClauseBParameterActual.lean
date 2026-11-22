import tmp.sheaf.xif.paper.S2813ClauseA37ReadyActual
import tmp.sheaf.xif.paper.S2786PlaceBlockActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceTateComparisonSynthesis
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import tmp.sheaf.xif.paper.S2806TateParameterActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlaceTateComparisonConstruction
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2813ClauseA37ReadyActual
open LeanFormal.IUT.XiFPaper.S2806TateParameterActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2814ClauseBParameterActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The exact uniformizer q-parameter of S2806 at a Gaussian finite place. -/
noncomputable def S2814Param (w : NumberField.FinitePlace GaussianField) :
    FinitePlaceQCandidate w :=
  S2806Candidate w

/-- Conditional bad-place contract: parameter is actual, order_coprime and
realization are the two explicit gaps. -/
noncomputable def S2814Contract
    (S : SourceSignQuotientData S2786Arithmetic)
    (hreal : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈
        S2786PlaceSelection.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Param w)) :
    BadPlaceUniformizationContract S2786PlaceSelection where
  parameter := fun w _hw => S2814Param w
  realization := hreal
  order_coprime := by
    intro w _hw
    rw [show S2771FiveLabel.value = 5 by rfl]
    exact S2806Candidate_order_coprime w

#check S2814Param
#check S2814Contract
#print axioms S2814Contract

end LeanFormal.IUT.XiFPaper.S2814ClauseBParameterActual
end
