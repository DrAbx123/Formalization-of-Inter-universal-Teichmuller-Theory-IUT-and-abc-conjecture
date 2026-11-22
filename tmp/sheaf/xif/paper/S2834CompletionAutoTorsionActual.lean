import tmp.sheaf.xif.paper.S2833SourceWitnessReducedActual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2832ClauseAssemblyReducedActual
open LeanFormal.IUT.XiFPaper.S2821ClauseBDerivationsActual
open LeanFormal.IUT.XiFPaper.S2833SourceWitnessReducedActual
open LeanFormal.IUT.XiFPaper.S2813ClauseA37ReadyActual
open LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2834CompletionAutoTorsionActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

noncomputable def S2834TorsionBasis :
    (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      S2786Arithmetic.curve.LTorsion S2771FiveLabel :=
  Classical.choice (S2771_rankTwoTorsionBasis S2786Arithmetic.curve)

/-- The conditional source witness built from the S2827 clause assembly. -/
noncomputable def S2834Witness
    (S : SourceSignQuotientData S2786Arithmetic)
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
    (hreal : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈
        S2786PlaceSelection.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Parameter S2786PlaceSelection w _hw))
    (torsion23Rational : S2786Arithmetic.curve.Torsion23Rational)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
          S2771FiveLabel S2786Arithmetic.curve (S2834TorsionBasis)).range)
    (kernelFieldIdentification :
      S2786Arithmetic.K ≃ₐ[S2786Arithmetic.F]
        (PuncturedEllipticCurve.galoisLTorsionKernelField
          S2771FiveLabel S2786Arithmetic.curve (S2834TorsionBasis)))
    (kernelFieldIdentificationRange :
      (Set.range fun x => (kernelFieldIdentification x :
        AlgebraicClosure S2786Arithmetic.F)) =
        (PuncturedEllipticCurve.galoisLTorsionKernelField
          S2771FiveLabel S2786Arithmetic.curve (S2834TorsionBasis) :
          Set (AlgebraicClosure S2786Arithmetic.F)))
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2786Arithmetic) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit S2786Arithmetic S
      (S2813ClauseA S)
      (S2821ClauseB S hV hreal)
      (S2832ClauseC S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide))
    (boundary : SourceClauseFBoundaryUnit S2786Arithmetic S
      (S2813ClauseA S)
      (S2821ClauseB S hV hreal)
      (S2832ClauseC S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)
      (S2832ClauseE S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily)) :
    SourceClauseConstructionWitness S2771FiveLabel :=
  witnessOfClauseAssembly S2786Arithmetic S
    (S2832ClauseAssembly S hV hreal
      torsion23Rational (S2834TorsionBasis) imageContainsSL2
      kernelFieldIdentification kernelFieldIdentificationRange
      kSide localFamily boundary)

/-- The native initial Theta data attached to the conditional witness. -/
noncomputable def S2834NativeData
    (S : SourceSignQuotientData S2786Arithmetic)
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
    (hreal : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈
        S2786PlaceSelection.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Parameter S2786PlaceSelection w _hw))
    (torsion23Rational : S2786Arithmetic.curve.Torsion23Rational)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
          S2771FiveLabel S2786Arithmetic.curve (S2834TorsionBasis)).range)
    (kernelFieldIdentification :
      S2786Arithmetic.K ≃ₐ[S2786Arithmetic.F]
        (PuncturedEllipticCurve.galoisLTorsionKernelField
          S2771FiveLabel S2786Arithmetic.curve (S2834TorsionBasis)))
    (kernelFieldIdentificationRange :
      (Set.range fun x => (kernelFieldIdentification x :
        AlgebraicClosure S2786Arithmetic.F)) =
        (PuncturedEllipticCurve.galoisLTorsionKernelField
          S2771FiveLabel S2786Arithmetic.curve (S2834TorsionBasis) :
          Set (AlgebraicClosure S2786Arithmetic.F)))
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2786Arithmetic) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit S2786Arithmetic S
      (S2813ClauseA S)
      (S2821ClauseB S hV hreal)
      (S2832ClauseC S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide))
    (boundary : SourceClauseFBoundaryUnit S2786Arithmetic S
      (S2813ClauseA S)
      (S2821ClauseB S hV hreal)
      (S2832ClauseC S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)
      (S2832ClauseE S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily)) :
    SourceNativeInitialThetaData S2771FiveLabel :=
  SourceClauseConstructionWitness.sourceData
    (S2834Witness S hV hreal
      torsion23Rational imageContainsSL2
      kernelFieldIdentification kernelFieldIdentificationRange
      kSide localFamily boundary)

/-- The full SourceCompletion attached to the conditional witness. -/
noncomputable def S2834Completion
    (S : SourceSignQuotientData S2786Arithmetic)
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
    (hreal : ∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : comap (k := S2786Arithmetic.Fmod) w ∈
        S2786PlaceSelection.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Parameter S2786PlaceSelection w _hw))
    (torsion23Rational : S2786Arithmetic.curve.Torsion23Rational)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
          S2771FiveLabel S2786Arithmetic.curve (S2834TorsionBasis)).range)
    (kernelFieldIdentification :
      S2786Arithmetic.K ≃ₐ[S2786Arithmetic.F]
        (PuncturedEllipticCurve.galoisLTorsionKernelField
          S2771FiveLabel S2786Arithmetic.curve (S2834TorsionBasis)))
    (kernelFieldIdentificationRange :
      (Set.range fun x => (kernelFieldIdentification x :
        AlgebraicClosure S2786Arithmetic.F)) =
        (PuncturedEllipticCurve.galoisLTorsionKernelField
          S2771FiveLabel S2786Arithmetic.curve (S2834TorsionBasis) :
          Set (AlgebraicClosure S2786Arithmetic.F)))
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2786Arithmetic) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit S2786Arithmetic S
      (S2813ClauseA S)
      (S2821ClauseB S hV hreal)
      (S2832ClauseC S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide))
    (boundary : SourceClauseFBoundaryUnit S2786Arithmetic S
      (S2813ClauseA S)
      (S2821ClauseB S hV hreal)
      (S2832ClauseC S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)
      (S2832ClauseE S hV hreal
        torsion23Rational (S2834TorsionBasis) imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily)) :
    SourceCompletion S2771FiveLabel :=
  SourceCompletion.ofSourceNative
    (S2834NativeData S hV hreal
      torsion23Rational imageContainsSL2
      kernelFieldIdentification kernelFieldIdentificationRange
      kSide localFamily boundary)

#check S2834Witness
#check S2834NativeData
#check S2834Completion
#print axioms S2834Witness
#print axioms S2834NativeData
#print axioms S2834Completion

end LeanFormal.IUT.XiFPaper.S2834CompletionAutoTorsionActual
end
