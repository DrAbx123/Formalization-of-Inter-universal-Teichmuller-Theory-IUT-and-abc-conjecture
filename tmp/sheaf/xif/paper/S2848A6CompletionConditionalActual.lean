import tmp.sheaf.xif.paper.S2846A6ClauseBFAssembly
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2846A6ClauseBFAssembly
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2848A6CompletionConditionalActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- A6 source witness from the S2846 conditional clause assembly. -/
noncomputable def S2848Witness
    (S : SourceSignQuotientData S2847A6)
    (multiplicative : ∀ (p : NumberField.FinitePlace S2847A6.F),
      comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        S2847A6.curve.HasMultiplicativeReductionAt p)
    (qWitness : ∀ (p : NumberField.FinitePlace S2847A6.F),
      (hp : comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad) →
        Nonempty (SourceTateComparisonWitness S2847A6 p))
    (residueCoprime : ∀ (p : NumberField.FinitePlace S2847A6.F),
      comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (residueCharacteristic (comap (k := S2847A6.Fmod) p)))
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
          S2771FiveLabel S2847A6.curve S2847Basis).range)
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2847A6) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit S2847A6 S
      (S2846A6ClauseA S)
      (S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      (S2846A6ClauseD S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        (S2846A6ClauseC S
          (S2846A6ClauseB S multiplicative qWitness residueCoprime)
          imageContainsSL2)
        kSide))
    (boundary : S2817ClauseFScaffold (l := S2771FiveLabel)
      (A := S2847A6) (S := S)
      (C := S2846A6ClauseA S)
      (B := S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (D := S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      (E := S2846A6ClauseD S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        (S2846A6ClauseC S
          (S2846A6ClauseB S multiplicative qWitness residueCoprime)
          imageContainsSL2)
        kSide)) :
    SourceClauseConstructionWitness S2771FiveLabel :=
  witnessOfClauseAssembly S2847A6 S
    (S2846A6ClauseAssembly S multiplicative qWitness residueCoprime
      imageContainsSL2 kSide localFamily boundary)

/-- A6 native initial Theta data from the conditional witness. -/
noncomputable def S2848NativeData
    (S : SourceSignQuotientData S2847A6)
    (multiplicative : ∀ (p : NumberField.FinitePlace S2847A6.F),
      comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        S2847A6.curve.HasMultiplicativeReductionAt p)
    (qWitness : ∀ (p : NumberField.FinitePlace S2847A6.F),
      (hp : comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad) →
        Nonempty (SourceTateComparisonWitness S2847A6 p))
    (residueCoprime : ∀ (p : NumberField.FinitePlace S2847A6.F),
      comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (residueCharacteristic (comap (k := S2847A6.Fmod) p)))
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
          S2771FiveLabel S2847A6.curve S2847Basis).range)
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2847A6) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit S2847A6 S
      (S2846A6ClauseA S)
      (S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      (S2846A6ClauseD S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        (S2846A6ClauseC S
          (S2846A6ClauseB S multiplicative qWitness residueCoprime)
          imageContainsSL2)
        kSide))
    (boundary : S2817ClauseFScaffold (l := S2771FiveLabel)
      (A := S2847A6) (S := S)
      (C := S2846A6ClauseA S)
      (B := S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (D := S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      (E := S2846A6ClauseD S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        (S2846A6ClauseC S
          (S2846A6ClauseB S multiplicative qWitness residueCoprime)
          imageContainsSL2)
        kSide)) :
    SourceNativeInitialThetaData S2771FiveLabel :=
  SourceClauseConstructionWitness.sourceData
    (S2848Witness S multiplicative qWitness residueCoprime
      imageContainsSL2 kSide localFamily boundary)

/-- A6 SourceCompletion. -/
noncomputable def S2848Completion
    (S : SourceSignQuotientData S2847A6)
    (multiplicative : ∀ (p : NumberField.FinitePlace S2847A6.F),
      comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        S2847A6.curve.HasMultiplicativeReductionAt p)
    (qWitness : ∀ (p : NumberField.FinitePlace S2847A6.F),
      (hp : comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad) →
        Nonempty (SourceTateComparisonWitness S2847A6 p))
    (residueCoprime : ∀ (p : NumberField.FinitePlace S2847A6.F),
      comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        Nat.Coprime S2771FiveLabel.value
          (residueCharacteristic (comap (k := S2847A6.Fmod) p)))
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
          S2771FiveLabel S2847A6.curve S2847Basis).range)
    (kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
      (A := S2847A6) (S := S))
    (localFamily : SourceClauseELocalFamilyUnit S2847A6 S
      (S2846A6ClauseA S)
      (S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      (S2846A6ClauseD S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        (S2846A6ClauseC S
          (S2846A6ClauseB S multiplicative qWitness residueCoprime)
          imageContainsSL2)
        kSide))
    (boundary : S2817ClauseFScaffold (l := S2771FiveLabel)
      (A := S2847A6) (S := S)
      (C := S2846A6ClauseA S)
      (B := S2846A6ClauseB S multiplicative qWitness residueCoprime)
      (D := S2846A6ClauseC S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        imageContainsSL2)
      (E := S2846A6ClauseD S
        (S2846A6ClauseB S multiplicative qWitness residueCoprime)
        (S2846A6ClauseC S
          (S2846A6ClauseB S multiplicative qWitness residueCoprime)
          imageContainsSL2)
        kSide)) :
    SourceCompletion S2771FiveLabel :=
  SourceCompletion.ofSourceNative
    (S2848NativeData S multiplicative qWitness residueCoprime
      imageContainsSL2 kSide localFamily boundary)

#check S2848Witness
#check S2848NativeData
#check S2848Completion
#print axioms S2848Witness
#print axioms S2848NativeData
#print axioms S2848Completion

end LeanFormal.IUT.XiFPaper.S2848A6CompletionConditionalActual
end
