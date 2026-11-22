import tmp.sheaf.xif.paper.S2907ClauseECorrected
import tmp.sheaf.xif.paper.S2907CorrectedCompletionInputs
import tmp.sheaf.xif.paper.S2906CorrectedClauseABCD
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2907ClauseECorrected
open LeanFormal.IUT.XiFPaper.S2907CorrectedCompletionInputs
open LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD
open LeanFormal.IUT.XiFPaper.S2907bClauseDEActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2907ClauseFCorrected

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

noncomputable def S2907CanonicalKQuotientData
    (S : SourceSignQuotientDataCorrected S2847A6)
    (C : S2906ClauseACorrected S)
    (B : S2906ClauseBCorrected S C)
    (D : S2906ClauseCCorrected S C B) :
    TorsionRankOneQuotientData S2771FiveLabel
      (S2847A6.curve.baseChange S2847A6.K) where
  torsion_basis := (D.torsion_basis).trans
    (PuncturedEllipticCurve.initialThetaKToFTorsionTransport S2847A6).symm

noncomputable def S2907BoundaryOrigin
    (S : SourceSignQuotientDataCorrected S2847A6)
    (C : S2906ClauseACorrected S)
    (B : S2906ClauseBCorrected S C)
    (D : S2906ClauseCCorrected S C B)
    (originMap :
      {q : (S2907CanonicalKQuotientData S C B D).Quotient // q ≠ 0} →
        Iut.OrbicurveBoundaryCusp S.cK)
    (originMap_epsilon :
      originMap
        ⟨(S2907CanonicalKQuotientData S C B D).distinguishedClass,
          (S2907CanonicalKQuotientData S C B D).distinguishedClass_nonzero⟩ =
        S.epsilon) :
    TorsionQuotientBoundaryOrigin S2771FiveLabel S2847A6 S.cK where
  rank_one_quotient := S2907CanonicalKQuotientData S C B D
  originMap := originMap
  cusp := S.epsilon
  originMap_distinguishedClass := originMap_epsilon

structure S2907ClauseFScaffold
    (S : SourceSignQuotientDataCorrected S2847A6)
    (C : S2906ClauseACorrected S)
    (B : S2906ClauseBCorrected S C)
    (D : S2906ClauseCCorrected S C B)
    (E : S2906ClauseDCorrected S C B D) where
  originMap :
    {q : (S2907CanonicalKQuotientData S C B D).Quotient // q ≠ 0} →
      Iut.OrbicurveBoundaryCusp S.cK
  originMap_epsilon :
    originMap
      ⟨(S2907CanonicalKQuotientData S C B D).distinguishedClass,
        (S2907CanonicalKQuotientData S C B D).distinguishedClass_nonzero⟩ =
      S.epsilon
  cuspDecomposition : Iut.OrbicurveCuspidalDecompositionData E.c_groups.groups
  cuspDecomposition_origin :
    cuspDecomposition.cusp =
      (S2907BoundaryOrigin S C B D originMap originMap_epsilon).cusp

structure S2907ClauseFCorrected
    (S : SourceSignQuotientDataCorrected S2847A6)
    (C : S2906ClauseACorrected S)
    (B : S2906ClauseBCorrected S C)
    (D : S2906ClauseCCorrected S C B)
    (E : S2906ClauseDCorrected S C B D) where
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
  kSide : S2907ClauseDScaffold S
  localFamily : S2907ClauseEScaffold S C B D E
  boundary : S2907ClauseFScaffold S C B D E

#check S2907CanonicalKQuotientData
#check S2907BoundaryOrigin
#check S2907ClauseFScaffold
#check S2907ClauseFCorrected

end LeanFormal.IUT.XiFPaper.S2907ClauseFCorrected
end
