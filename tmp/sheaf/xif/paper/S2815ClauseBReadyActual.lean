import tmp.sheaf.xif.paper.S2814ClauseBParameterActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceTateComparisonSynthesis

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlaceTateComparisonConstruction
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2814ClauseBParameterActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2815ClauseBReadyActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- ClauseB for E37/Q(i) from the conditional uniformization contract, given
the ClauseA datum, the common bad set, the multiplicative reductions, the
realization family, and the residue coprimality. -/
theorem S2815ClauseB
    (S : SourceSignQuotientData S2786Arithmetic)
    (C : SourceClauseA S2786Arithmetic S)
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
    (multiplicative : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad),
      S2786Arithmetic.curve.HasMultiplicativeReductionAt w)
    (hreal : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈
        S2786PlaceSelection.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Param w))
    (residueCoprime : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad),
      Nat.Coprime S2771FiveLabel.value
        (residueCharacteristic (comap (k := S2786Arithmetic.Fmod) w))) :
    SourceClauseB S2786Arithmetic S C :=
  sourceClauseB_of_uniformizationContract
    (A := S2786Arithmetic)
    (S := S) (CA := C)
    S2786PlaceSelection hV multiplicative
    (S2814Contract S hreal) residueCoprime

#check S2815ClauseB
#print axioms S2815ClauseB

end LeanFormal.IUT.XiFPaper.S2815ClauseBReadyActual
end
