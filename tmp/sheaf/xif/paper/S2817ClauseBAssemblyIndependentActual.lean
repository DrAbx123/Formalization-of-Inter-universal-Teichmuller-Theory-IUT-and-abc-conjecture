import tmp.sheaf.xif.paper.S2814BadPlaceContractActual
import tmp.sheaf.xif.paper.S2813ClauseA37ReadyActual
import tmp.sheaf.xif.paper.S2786PlaceBlockActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2813ClauseA37ReadyActual
open LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

local instance s2817GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2817ClauseBAssemblyIndependentActual

variable (S : SourceSignQuotientData S2786Arithmetic)
variable (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)

/-- Independent ClauseB assembly.  Multiplicative reduction and residue
coprimality are explicit inputs here; S2815/qside owns their derivation. -/
noncomputable def S2817ClauseB
    (hreal : forall (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈
        S2786PlaceSelection.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Parameter S2786PlaceSelection w _hw))
    (multiplicative : forall (w : NumberField.FinitePlace S2786Arithmetic.F),
      NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad →
        S2786Arithmetic.curve.HasMultiplicativeReductionAt w)
    (residueCoprime : forall (w : NumberField.FinitePlace S2786Arithmetic.F),
      NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (NumberFieldFinitePlace.residueCharacteristic
            (NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w))) :
    SourceClauseB S2786Arithmetic S (S2813ClauseA S) :=
  SourceClauseB.ofTateComparisonWitnesses
    multiplicative
    (fun w hw =>
      ⟨(S2814BadPlaceContract_of_realization S2786PlaceSelection hreal
        ).toTateUniformizationCards.witness
          w (hV ▸ hw)⟩)
    residueCoprime

#check S2817ClauseB
#print axioms S2817ClauseB

end LeanFormal.IUT.XiFPaper.S2817ClauseBAssemblyIndependentActual
end
