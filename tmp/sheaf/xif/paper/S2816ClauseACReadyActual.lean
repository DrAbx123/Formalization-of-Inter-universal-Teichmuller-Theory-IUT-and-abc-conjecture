import tmp.sheaf.xif.paper.S2817ClauseBAssemblyIndependentActual
import tmp.sheaf.xif.paper.S2774ClauseCFromDataActual
import tmp.sheaf.xif.paper.S2813ClauseA37ReadyActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2813ClauseA37ReadyActual
open LeanFormal.IUT.XiFPaper.S2817ClauseBAssemblyIndependentActual
open LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual
open LeanFormal.IUT.XiFPaper.S2774ClauseCFromDataActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2816ClauseACReadyActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- ClauseB assembled through the canonical independent S2817 assembly. -/
noncomputable def S2816ClauseB
    (S : SourceSignQuotientData S2786Arithmetic)
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
    (hreal : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈
        S2786PlaceSelection.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Parameter S2786PlaceSelection w _hw))
    (multiplicative : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad),
      S2786Arithmetic.curve.HasMultiplicativeReductionAt w)
    (residueCoprime : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad),
      Nat.Coprime S2771FiveLabel.value
        (residueCharacteristic (comap (k := S2786Arithmetic.Fmod) w))) :
    SourceClauseB S2786Arithmetic S (S2813ClauseA S) :=
  S2817ClauseB S hV hreal multiplicative residueCoprime

/-- ClauseC from S2774, using the S2817-backed ClauseB. -/
noncomputable def S2816ClauseC
    (S : SourceSignQuotientData S2786Arithmetic)
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
    (hreal : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈
        S2786PlaceSelection.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Parameter S2786PlaceSelection w _hw))
    (multiplicative : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad),
      S2786Arithmetic.curve.HasMultiplicativeReductionAt w)
    (residueCoprime : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad),
      Nat.Coprime S2771FiveLabel.value
        (residueCharacteristic (comap (k := S2786Arithmetic.Fmod) w)))
    (torsion23Rational : S2786Arithmetic.curve.Torsion23Rational)
    (torsionBasis : (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      S2786Arithmetic.curve.LTorsion S2771FiveLabel)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
          S2771FiveLabel S2786Arithmetic.curve torsionBasis).range)
    (kernelFieldIdentification :
      S2786Arithmetic.K ≃ₐ[S2786Arithmetic.F]
        (PuncturedEllipticCurve.galoisLTorsionKernelField
          S2771FiveLabel S2786Arithmetic.curve torsionBasis))
    (kernelFieldIdentificationRange :
      (Set.range fun x => (kernelFieldIdentification x :
        AlgebraicClosure S2786Arithmetic.F)) =
        (PuncturedEllipticCurve.galoisLTorsionKernelField
          S2771FiveLabel S2786Arithmetic.curve torsionBasis :
          Set (AlgebraicClosure S2786Arithmetic.F))) :
    SourceClauseC S2786Arithmetic S (S2813ClauseA S)
      (S2816ClauseB S hV hreal multiplicative residueCoprime) :=
  S2774_sourceClauseC
    (l := S2771FiveLabel)
    (A := S2786Arithmetic) (S := S)
    (C := S2813ClauseA S)
    (B := S2816ClauseB S hV hreal multiplicative residueCoprime)
    torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange

#check S2816ClauseB
#check S2816ClauseC
#print axioms S2816ClauseB
#print axioms S2816ClauseC

end LeanFormal.IUT.XiFPaper.S2816ClauseACReadyActual
end
