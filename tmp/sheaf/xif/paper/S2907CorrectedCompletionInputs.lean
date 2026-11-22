import tmp.sheaf.xif.paper.S2856A6CoreWithInvolution
import tmp.sheaf.xif.paper.S2848A6CompletionConditionalActual
import tmp.sheaf.xif.paper.S2841A6PlaceSelectionActual
import tmp.sheaf.xif.paper.S2846A6ClauseBFAssembly
import tmp.sheaf.xif.paper.S2817ClauseDEFScaffold
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual

noncomputable section
open LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2856A6CoreWithInvolution
open LeanFormal.IUT.XiFPaper.S2857StackAutoForA6Actual
open LeanFormal.IUT.XiFPaper.S2855A6CoreFromD6ConditionalActual
open LeanFormal.IUT.XiFPaper.S2848A6CompletionConditionalActual
open LeanFormal.IUT.XiFPaper.S2841A6PlaceSelectionActual
open LeanFormal.IUT.XiFPaper.S2846A6ClauseBFAssembly
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2907CorrectedCompletionInputs

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

structure S2907CorrectedCompletionInputs
    (S : SourceSignQuotientDataCorrected S2847A6) where
  multiplicative : ∀ (p : NumberField.FinitePlace S2847A6.F),
    NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
      S2847A6.curve.HasMultiplicativeReductionAt p
  qWitness : ∀ (p : NumberField.FinitePlace S2847A6.F),
    (hp : NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad) →
      Nonempty (SourceTateComparisonWitness S2847A6 p)
  residueCoprime : ∀ (p : NumberField.FinitePlace S2847A6.F),
    NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
      Nat.Coprime S2771FiveLabel.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p))
  imageContainsSL2 :
    Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
      (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
        S2771FiveLabel S2847A6.curve S2847Basis).range
#check S2907CorrectedCompletionInputs

end LeanFormal.IUT.XiFPaper.S2907CorrectedCompletionInputs
end
