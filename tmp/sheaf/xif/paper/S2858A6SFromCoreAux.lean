import tmp.sheaf.xif.paper.S2856A6CoreWithInvolution
import tmp.sheaf.xif.paper.S2848A6CompletionConditionalActual
import tmp.sheaf.xif.paper.S2841A6PlaceSelectionActual
import tmp.sheaf.xif.paper.S2846A6ClauseBFAssembly
import tmp.sheaf.xif.paper.S2817ClauseDEFScaffold

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
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2858A6SFromCoreAux

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The 18 remaining geometric-core fields for S2856Core, with α,hα fixed. -/
structure S2858CoreInputs
    (α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (hα : α ≫ α = 𝟙 S2844D6F6BaseChangeActual.S2844X) where
  unique_elliptic_involution :
    ∀ inv : S2855HyperbolicOrbicurve.Hom S2855HyperbolicOrbicurve,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id S2855HyperbolicOrbicurve) →
      inv = S2857StackAuto α
  signAction : Iut.OrbicurveSignAction S2855HyperbolicOrbicurve
  signAction_inversion_eq_ellipticInvolution :
    signAction.inversion = S2857StackAuto α
  cF : Iut.HyperbolicOrbicurve S2847A6.F
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cF
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
  xFGroups : SourceOrbicurveGroupData S2855HyperbolicOrbicurve
    (Iut.AbsoluteGaloisProfinite S2847A6.F)
  cFGroups : SourceOrbicurveGroupData cF
    (Iut.AbsoluteGaloisProfinite S2847A6.F)
  fGroupInclusion : Iut.ProfiniteFundamentalGroupInclusion
    xFGroups.sequence.geometric xFGroups.sequence.arithmetic
    cFGroups.sequence.geometric cFGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite S2847A6.F) xFGroups.sequence cFGroups.sequence
  xK : Iut.HyperbolicOrbicurve S2847A6.K
  cK : Iut.HyperbolicOrbicurve S2847A6.K
  xKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K
    S2855HyperbolicOrbicurve
  cKExtension : SourceOrbicurveScalarExtension S2847A6.F S2847A6.K cF
  xKType : xK.signature = sourceTypeOneLTorsion S2771FiveLabel
  cKType : cK.signature = sourceTypeOneLTorsionPlusMinus S2771FiveLabel
  xK_eq_extension : xK = xKExtension.result
  cK_eq_extension : cK = cKExtension.result
  epsilon : Iut.OrbicurveBoundaryCusp cK

/-- S from the A6 geometric core with actual S2841 place selection. -/
noncomputable def S2858S
    {α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X}
    {hα : α ≫ α = 𝟙 S2844D6F6BaseChangeActual.S2844X}
    (I : S2858CoreInputs α hα) :
    SourceSignQuotientData S2847A6 :=
  (S2856Core α hα I.unique_elliptic_involution I.signAction
    I.signAction_inversion_eq_ellipticInvolution I.cF I.quotient
    I.quotientWitness I.xFGroups I.cFGroups I.fGroupInclusion I.xK I.cK
    I.xKExtension I.cKExtension I.xKType I.cKType I.xK_eq_extension
    I.cK_eq_extension I.epsilon).toSourceSignQuotientData S2841PlaceSelection

/-- Remaining completion inputs after replacing S by S2858S. -/
structure S2858CompletionInputs
    {α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X}
    {hα : α ≫ α = 𝟙 S2844D6F6BaseChangeActual.S2844X}
    (I : S2858CoreInputs α hα) where
  multiplicative : ∀ (p : NumberField.FinitePlace S2847A6.F),
    NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ (S2858S I).V_mod_bad →
      S2847A6.curve.HasMultiplicativeReductionAt p
  qWitness : ∀ (p : NumberField.FinitePlace S2847A6.F),
    (hp : NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ (S2858S I).V_mod_bad) →
      Nonempty (SourceTateComparisonWitness S2847A6 p)
  residueCoprime : ∀ (p : NumberField.FinitePlace S2847A6.F),
    NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ (S2858S I).V_mod_bad →
      Nat.Coprime S2771FiveLabel.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p))
  imageContainsSL2 :
    Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
      (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation
        S2771FiveLabel S2847A6.curve S2847Basis).range
  kSide : S2817ClauseDScaffold (l := S2771FiveLabel)
    (A := S2847A6) (S := S2858S I)
  localFamily : SourceClauseELocalFamilyUnit S2847A6 (S2858S I)
    (S2846A6ClauseA (S2858S I))
    (S2846A6ClauseB (S2858S I) multiplicative qWitness residueCoprime)
    (S2846A6ClauseC (S2858S I)
      (S2846A6ClauseB (S2858S I) multiplicative qWitness residueCoprime)
      imageContainsSL2)
    (S2846A6ClauseD (S2858S I)
      (S2846A6ClauseB (S2858S I) multiplicative qWitness residueCoprime)
      (S2846A6ClauseC (S2858S I)
        (S2846A6ClauseB (S2858S I) multiplicative qWitness residueCoprime)
        imageContainsSL2)
      kSide)
  boundary : S2817ClauseFScaffold (l := S2771FiveLabel)
    (A := S2847A6) (S := S2858S I)
    (C := S2846A6ClauseA (S2858S I))
    (B := S2846A6ClauseB (S2858S I) multiplicative qWitness residueCoprime)
    (D := S2846A6ClauseC (S2858S I)
      (S2846A6ClauseB (S2858S I) multiplicative qWitness residueCoprime)
      imageContainsSL2)
    (E := S2846A6ClauseD (S2858S I)
      (S2846A6ClauseB (S2858S I) multiplicative qWitness residueCoprime)
      (S2846A6ClauseC (S2858S I)
        (S2846A6ClauseB (S2858S I) multiplicative qWitness residueCoprime)
        imageContainsSL2)
      kSide)

/-- A6 completion with S replaced by S2858S. -/
noncomputable def S2858Completion
    {α : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X}
    {hα : α ≫ α = 𝟙 S2844D6F6BaseChangeActual.S2844X}
    (I : S2858CoreInputs α hα)
    (J : S2858CompletionInputs I) :
    SourceCompletion S2771FiveLabel :=
  S2848Completion (S2858S I) J.multiplicative J.qWitness
    J.residueCoprime J.imageContainsSL2 J.kSide J.localFamily J.boundary

#check S2858S
#check S2858Completion
#print axioms S2858S
#print axioms S2858Completion

end LeanFormal.IUT.XiFPaper.S2858A6SFromCoreAux
end