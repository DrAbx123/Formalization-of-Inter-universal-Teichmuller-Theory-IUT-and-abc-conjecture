import tmp.sheaf.xif.paper.S2827ClauseAssemblyConditionalActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2827ClauseAssemblyConditionalActual
open LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2828SourceWitnessConditionalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The conditional source witness built from the S2827 clause assembly. -/
noncomputable def S2828Witness
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
    SourceClauseConstructionWitness S2771FiveLabel :=
  witnessOfClauseAssembly S2786Arithmetic S
    (S2827ClauseAssembly S hV hreal multiplicative residueCoprime
      torsion23Rational torsionBasis imageContainsSL2
      kernelFieldIdentification kernelFieldIdentificationRange
      kSide localFamily boundary)

/-- The native initial Theta data attached to the conditional witness. -/
noncomputable def S2828NativeData
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
    SourceNativeInitialThetaData S2771FiveLabel :=
  SourceClauseConstructionWitness.sourceData
    (S2828Witness S hV hreal multiplicative residueCoprime
      torsion23Rational torsionBasis imageContainsSL2
      kernelFieldIdentification kernelFieldIdentificationRange
      kSide localFamily boundary)

/-- The full SourceCompletion attached to the conditional witness. -/
noncomputable def S2828Completion
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
    SourceCompletion S2771FiveLabel :=
  SourceCompletion.ofSourceNative
    (S2828NativeData S hV hreal multiplicative residueCoprime
      torsion23Rational torsionBasis imageContainsSL2
      kernelFieldIdentification kernelFieldIdentificationRange
      kSide localFamily boundary)

#check S2828Witness
#check S2828NativeData
#check S2828Completion
#print axioms S2828Witness
#print axioms S2828NativeData
#print axioms S2828Completion

end LeanFormal.IUT.XiFPaper.S2828SourceWitnessConditionalActual
end
