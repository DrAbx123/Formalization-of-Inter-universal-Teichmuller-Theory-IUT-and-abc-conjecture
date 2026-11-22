import tmp.sheaf.xif.paper.S2828SourceWitnessConditionalActual
import tmp.sheaf.xif.paper.S2821ClauseBDerivationsActual
import tmp.sheaf.xif.paper.S2806TateParameterActual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2827ClauseAssemblyConditionalActual
open LeanFormal.IUT.XiFPaper.S2828SourceWitnessConditionalActual
open LeanFormal.IUT.XiFPaper.S2821ClauseBDerivationsActual
open LeanFormal.IUT.XiFPaper.S2806TateParameterActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2814BadPlaceContractActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2829CompletionInputsAudit

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## Actual suppliers among the 13 S2828 inputs

Actual (only S and hV needed):

* multiplicative: S2829_multiplicative, from S2821_multiplicative / S2798.
* residueCoprime: S2829_residueCoprime, from S2821_residue_coprime.
* torsionBasis: S2829TorsionBasis, from S2771 rank-two basis.
-/

theorem S2829_multiplicative
    (S : SourceSignQuotientData S2786Arithmetic)
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad) :
    ∀ (w : NumberField.FinitePlace S2786Arithmetic.F),
      comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad →
        S2786Arithmetic.curve.HasMultiplicativeReductionAt w :=
  S2821_multiplicative S hV

theorem S2829_residueCoprime
    (S : SourceSignQuotientData S2786Arithmetic)
    (hV : S.V_mod_bad = S2786PlaceSelection.V_mod_bad) :
    ∀ (w : NumberField.FinitePlace S2786Arithmetic.F),
      comap (k := S2786Arithmetic.Fmod) w ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (residueCharacteristic
            (comap (k := S2786Arithmetic.Fmod) w)) :=
  S2821_residue_coprime S hV

noncomputable def S2829TorsionBasis :
    (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      S2786Arithmetic.curve.LTorsion S2771FiveLabel :=
  Classical.choice (S2771_rankTwoTorsionBasis S2786Arithmetic.curve)

/-! ## Exact gaps (simple Prop records; no fabricated data) -/

def S2829SignQuotientGap : Prop :=
  Nonempty (SourceSignQuotientData S2786Arithmetic)

def S2829HVGap (S : SourceSignQuotientData S2786Arithmetic) : Prop :=
  S.V_mod_bad = S2786PlaceSelection.V_mod_bad

def S2829HRealGap : Prop :=
  Nonempty (∀ (w : NumberField.FinitePlace S2786Arithmetic.F)
    (_hw : comap (k := S2786Arithmetic.Fmod) w ∈
      S2786PlaceSelection.V_mod_bad),
    CurveIndexedTateUniformization S2786Arithmetic.curve w
      (S2814Parameter S2786PlaceSelection w _hw))

def S2829Torsion23Gap : Prop :=
  Nonempty S2786Arithmetic.curve.Torsion23Rational

def S2829LargeImageGap
    (torsionBasis : (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      S2786Arithmetic.curve.LTorsion S2771FiveLabel) : Prop :=
  Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
    (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
      S2771FiveLabel S2786Arithmetic.curve torsionBasis).range

def S2829KernelFieldGap
    (torsionBasis : (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      S2786Arithmetic.curve.LTorsion S2771FiveLabel) : Prop :=
  Nonempty (S2786Arithmetic.K ≃ₐ[S2786Arithmetic.F]
    (PuncturedEllipticCurve.galoisLTorsionKernelField
      S2771FiveLabel S2786Arithmetic.curve torsionBasis))

def S2829KernelFieldRangeGap
    (torsionBasis : (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      S2786Arithmetic.curve.LTorsion S2771FiveLabel)
    (kernelFieldIdentification :
      S2786Arithmetic.K ≃ₐ[S2786Arithmetic.F]
        (PuncturedEllipticCurve.galoisLTorsionKernelField
          S2771FiveLabel S2786Arithmetic.curve torsionBasis)) : Prop :=
  (Set.range fun x => (kernelFieldIdentification x :
    AlgebraicClosure S2786Arithmetic.F)) =
    (PuncturedEllipticCurve.galoisLTorsionKernelField
      S2771FiveLabel S2786Arithmetic.curve torsionBasis :
      Set (AlgebraicClosure S2786Arithmetic.F))

def S2829KSideGap (S : SourceSignQuotientData S2786Arithmetic) : Prop :=
  Nonempty (S2817ClauseDScaffold (l := S2771FiveLabel)
    (A := S2786Arithmetic) (S := S))

#check S2829_multiplicative
#check S2829_residueCoprime
#check S2829TorsionBasis
#check S2829SignQuotientGap
#check S2829HVGap
#check S2829HRealGap
#check S2829Torsion23Gap
#check S2829LargeImageGap
#check S2829KernelFieldGap
#check S2829KernelFieldRangeGap
#check S2829KSideGap
#print axioms S2829_multiplicative
#print axioms S2829_residueCoprime
#print axioms S2829TorsionBasis

end LeanFormal.IUT.XiFPaper.S2829CompletionInputsAudit
end
