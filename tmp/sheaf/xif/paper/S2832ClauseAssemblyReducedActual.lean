import tmp.sheaf.xif.paper.S2821ClauseBDerivationsActual
import tmp.sheaf.xif.paper.S2813ClauseA37ReadyActual
import tmp.sheaf.xif.paper.S2774ClauseCFromDataActual
import tmp.sheaf.xif.paper.S2823ClauseDConditionalActual
import tmp.sheaf.xif.paper.S2817ClauseDEFScaffold
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2813ClauseA37ReadyActual
open LeanFormal.IUT.XiFPaper.S2821ClauseBDerivationsActual
open LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual
open LeanFormal.IUT.XiFPaper.S2774ClauseCFromDataActual
open LeanFormal.IUT.XiFPaper.S2823ClauseDConditionalActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

local instance s2832GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2832ClauseAssemblyReducedActual

variable (S : SourceSignQuotientData S2786Arithmetic)
variable (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
variable (hreal : forall (w : NumberField.FinitePlace S2786Arithmetic.F)
  (_hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈
    S2786PlaceSelection.V_mod_bad),
  CurveIndexedTateUniformization S2786Arithmetic.curve w
    (S2814Parameter S2786PlaceSelection w _hw))

abbrev C0 (S : SourceSignQuotientData S2786Arithmetic) :
    SourceClauseA S2786Arithmetic S := S2813ClauseA S

abbrev B0 (S : SourceSignQuotientData S2786Arithmetic)
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad)
    (hreal : forall (w : NumberField.FinitePlace S2786Arithmetic.F)
      (_hw : NumberFieldFinitePlace.comap (k := S2786Arithmetic.Fmod) w ∈
        S2786PlaceSelection.V_mod_bad),
      CurveIndexedTateUniformization S2786Arithmetic.curve w
        (S2814Parameter S2786PlaceSelection w _hw)) :
    SourceClauseB S2786Arithmetic S (C0 S) := S2821ClauseB S hV hreal

noncomputable def S2832ClauseC
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
    SourceClauseC S2786Arithmetic S (C0 S) (B0 S hV hreal) :=
  S2774_sourceClauseC
    (l := S2771FiveLabel)
    (A := S2786Arithmetic) (S := S) (C := C0 S) (B := B0 S hV hreal)
    torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange

noncomputable def S2832ClauseD
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
    SourceClauseD S2786Arithmetic S (C0 S) (B0 S hV hreal)
      (S2832ClauseC S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange) :=
  S2823ClauseD kSide

noncomputable def S2832ClauseE
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
    (localFamily : SourceClauseELocalFamilyUnit S2786Arithmetic S (C0 S)
      (B0 S hV hreal)
      (S2832ClauseC S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)) :
    SourceClauseE S2786Arithmetic S (C0 S) (B0 S hV hreal)
      (S2832ClauseC S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide) :=
  S2823ClauseE localFamily


noncomputable def S2832ClauseF
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
    (localFamily : SourceClauseELocalFamilyUnit S2786Arithmetic S (C0 S)
      (B0 S hV hreal)
      (S2832ClauseC S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide))
    (boundary : SourceClauseFBoundaryUnit S2786Arithmetic S (C0 S)
      (B0 S hV hreal)
      (S2832ClauseC S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)
      (S2832ClauseE S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily)) :
    SourceClauseF S2786Arithmetic S (C0 S) (B0 S hV hreal)
      (S2832ClauseC S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)
      (S2832ClauseE S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily) :=
  S2823ClauseF boundary

noncomputable def S2832ClauseAssembly
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
    (localFamily : SourceClauseELocalFamilyUnit S2786Arithmetic S (C0 S)
      (B0 S hV hreal)
      (S2832ClauseC S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide))
    (boundary : SourceClauseFBoundaryUnit S2786Arithmetic S (C0 S)
      (B0 S hV hreal)
      (S2832ClauseC S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange)
      (S2832ClauseD S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide)
      (S2832ClauseE S hV hreal torsion23Rational torsionBasis imageContainsSL2
        kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily)) :
    SourceClauseAssembly S2786Arithmetic S where
  clauseA := C0 S
  clauseB := B0 S hV hreal
  clauseC := S2832ClauseC S hV hreal torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange
  clauseD := S2832ClauseD S hV hreal torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange kSide
  clauseE := S2832ClauseE S hV hreal torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily
  clauseF := S2832ClauseF S hV hreal torsion23Rational torsionBasis imageContainsSL2
    kernelFieldIdentification kernelFieldIdentificationRange kSide localFamily boundary

#check S2832ClauseAssembly
#print axioms S2832ClauseAssembly

end LeanFormal.IUT.XiFPaper.S2832ClauseAssemblyReducedActual
end
