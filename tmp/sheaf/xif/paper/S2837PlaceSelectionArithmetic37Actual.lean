import tmp.sheaf.xif.paper.S2784KernelFieldActual
import tmp.sheaf.xif.paper.S2786PlaceBlockActual
import tmp.sheaf.xif.paper.S2786E37PrimeIdealsActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2786E37PrimeIdealsActual
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

local instance s2837GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2837PlaceSelectionArithmetic37Actual

abbrev A37 : InitialThetaArithmeticData S2771FiveLabel :=
  LeanFormal.IUT.XiFPaper.S2784KernelFieldActual.arithmetic37

/-- The SourcePlaceSelection for arithmetic37, retyped from S2786PlaceSelection.
Only the Fmod place block is involved; K does not enter. -/
noncomputable def S2837PlaceSelection : SourcePlaceSelection A37 where
  V_mod_bad := (S2786VmodBad : Set (NumberField.FinitePlace A37.Fmod))
  V_mod_bad_odd_residue_characteristic := by
    intro q hq
    exact S2786VmodBad_odd q hq
  V_mod_bad_nonempty := S2786VmodBad_nonempty

theorem S2837_V_mod_bad_eq :
    S2837PlaceSelection.V_mod_bad =
      ({S2786PlusPlace, S2786MinusPlace} :
        Set (NumberField.FinitePlace A37.Fmod)) := by
  rfl

theorem S2837_V_mod_bad_eq_S2786 :
    S2837PlaceSelection.V_mod_bad = S2786PlaceSelection.V_mod_bad := rfl

#check S2837PlaceSelection
#check S2837_V_mod_bad_eq
#print axioms S2837PlaceSelection
#print axioms S2837_V_mod_bad_eq

end LeanFormal.IUT.XiFPaper.S2837PlaceSelectionArithmetic37Actual
end
