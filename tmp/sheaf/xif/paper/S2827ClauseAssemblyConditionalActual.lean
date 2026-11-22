import tmp.sheaf.xif.paper.S2823ClauseDConditionalActual
import tmp.sheaf.xif.paper.S2816ClauseACReadyActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2813ClauseA37ReadyActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2816ClauseACReadyActual
open LeanFormal.IUT.XiFPaper.S2823ClauseDConditionalActual
open LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual
open LeanFormal.IUT.XiFPaper.S2774ClauseCFromDataActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2827ClauseAssemblyConditionalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

noncomputable def S2827ClauseA
    (S : SourceSignQuotientData S2786Arithmetic) :
    SourceClauseA S2786Arithmetic S :=
  S2813ClauseA S

noncomputable def S2827ClauseB
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
    SourceClauseB S2786Arithmetic S (S2827ClauseA S) :=
  S2816ClauseB S hV hreal multiplicative residueCoprime

noncomputable def S2827ClauseC
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
    SourceClauseC S2786Arithmetic S (S2827ClauseA S)
      (S2827ClauseB S hV hreal multiplicative residueCoprime) :=
  S2816ClauseC S hV hreal multiplicative residueCoprime
    torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange

noncomputable def S2827ClauseD
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
          Set (AlgebraicClosure S2786Arithmetic.F)))
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2786Arithmetic) (S := S)) :
    SourceClauseD S2786Arithmetic S (S2827ClauseA S)
      (S2827ClauseB S hV hreal multiplicative residueCoprime)
      (S2827ClauseC S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange) :=
  S2823ClauseD kSide

noncomputable def S2827ClauseE
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
          Set (AlgebraicClosure S2786Arithmetic.F)))
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2786Arithmetic) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit S2786Arithmetic S
      (S2827ClauseA S)
      (S2827ClauseB S hV hreal multiplicative residueCoprime)
      (S2827ClauseC S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2827ClauseD S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)) :
    SourceClauseE S2786Arithmetic S (S2827ClauseA S)
      (S2827ClauseB S hV hreal multiplicative residueCoprime)
      (S2827ClauseC S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2827ClauseD S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide) :=
  S2823ClauseE localFamily

noncomputable def S2827ClauseF
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
          Set (AlgebraicClosure S2786Arithmetic.F)))
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2786Arithmetic) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit S2786Arithmetic S
      (S2827ClauseA S)
      (S2827ClauseB S hV hreal multiplicative residueCoprime)
      (S2827ClauseC S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2827ClauseD S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide))
    (boundary : SourceClauseFBoundaryUnit S2786Arithmetic S
      (S2827ClauseA S)
      (S2827ClauseB S hV hreal multiplicative residueCoprime)
      (S2827ClauseC S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2827ClauseD S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)
      (S2827ClauseE S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily)) :
    SourceClauseF S2786Arithmetic S (S2827ClauseA S)
      (S2827ClauseB S hV hreal multiplicative residueCoprime)
      (S2827ClauseC S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2827ClauseD S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)
      (S2827ClauseE S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily) :=
  S2823ClauseF boundary


/-- Full conditional ClauseAssembly for E37/Q(i), with every gap explicit. -/
noncomputable def S2827ClauseAssembly
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
          Set (AlgebraicClosure S2786Arithmetic.F)))
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2786Arithmetic) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit S2786Arithmetic S
      (S2827ClauseA S)
      (S2827ClauseB S hV hreal multiplicative residueCoprime)
      (S2827ClauseC S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2827ClauseD S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide))
    (boundary : SourceClauseFBoundaryUnit S2786Arithmetic S
      (S2827ClauseA S)
      (S2827ClauseB S hV hreal multiplicative residueCoprime)
      (S2827ClauseC S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2827ClauseD S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)
      (S2827ClauseE S hV hreal multiplicative residueCoprime
        torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily)) :
    SourceClauseAssembly S2786Arithmetic S where
  clauseA := S2827ClauseA S
  clauseB := S2827ClauseB S hV hreal multiplicative residueCoprime
  clauseC := S2827ClauseC S hV hreal multiplicative residueCoprime
    torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange
  clauseD := S2827ClauseD S hV hreal multiplicative residueCoprime
    torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange kSide
  clauseE := S2827ClauseE S hV hreal multiplicative residueCoprime
    torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily
  clauseF := S2827ClauseF S hV hreal multiplicative residueCoprime
    torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily boundary

#check S2827ClauseA
#check S2827ClauseB
#check S2827ClauseC
#check S2827ClauseD
#check S2827ClauseE
#check S2827ClauseF
#check S2827ClauseAssembly
#print axioms S2827ClauseAssembly

end LeanFormal.IUT.XiFPaper.S2827ClauseAssemblyConditionalActual
end
