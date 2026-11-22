import tmp.sheaf.xif.paper.S2907bClauseDEActual
import tmp.sheaf.xif.paper.S2906CorrectedClauseABCD
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2907ClauseECorrected

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

structure S2907FiniteLocalSourceCorrected
    (S : SourceSignQuotientDataCorrected S2847A6)
    (C : S2906ClauseACorrected S)
    (B : S2906ClauseBCorrected S C)
    (D : S2906ClauseCCorrected S C B)
    (E : S2906ClauseDCorrected S C B D)
    (w : NumberField.FinitePlace S2847A6.K) where
  localCurve : PuncturedEllipticCurve (NumberFieldFinitePlace.Completion w)
  local_curve_eq_actual : localCurve = sourceFiniteLocalCurve S2847A6 w
  xExtension : SourceOrbicurveScalarExtension S2847A6.K
    (NumberFieldFinitePlace.Completion w) S.xK
  cExtension : SourceOrbicurveScalarExtension S2847A6.K
    (NumberFieldFinitePlace.Completion w) S.cK
  signAction : Iut.OrbicurveSignAction xExtension.result
  quotientMapExtension : SourceOrbicurveMorphismScalarExtension
    xExtension cExtension E.k_quotient.map
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cExtension.result
  quotient_map_eq_extension : quotient.map = quotientMapExtension.result
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
  xGroups : SourceOrbicurveGroupData xExtension.result
    (Iut.AbsoluteGaloisProfinite (NumberFieldFinitePlace.Completion w))
  cGroups : SourceOrbicurveGroupData cExtension.result
    (Iut.AbsoluteGaloisProfinite (NumberFieldFinitePlace.Completion w))
  local_group_inclusion : Iut.ProfiniteFundamentalGroupInclusion
    xGroups.sequence.geometric xGroups.sequence.arithmetic
    cGroups.sequence.geometric cGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite (NumberFieldFinitePlace.Completion w))
    xGroups.sequence cGroups.sequence
  xGlobalEmbedding : Iut.ProfiniteFundamentalExactSequenceEmbedding
    xGroups.sequence.geometric xGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite (NumberFieldFinitePlace.Completion w))
    E.x_groups.sequence.geometric E.x_groups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite S2847A6.K)
    xGroups.sequence E.x_groups.sequence
  cGlobalEmbedding : Iut.ProfiniteFundamentalExactSequenceEmbedding
    cGroups.sequence.geometric cGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite (NumberFieldFinitePlace.Completion w))
    E.c_groups.sequence.geometric E.c_groups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite S2847A6.K)
    cGroups.sequence E.c_groups.sequence
  galois_embedding_agreement : xGlobalEmbedding.galois.hom = cGlobalEmbedding.galois.hom

structure S2907InfiniteLocalSourceCorrected
    (S : SourceSignQuotientDataCorrected S2847A6)
    (C : S2906ClauseACorrected S)
    (B : S2906ClauseBCorrected S C)
    (D : S2906ClauseCCorrected S C B)
    (E : S2906ClauseDCorrected S C B D)
    (w : NumberField.InfinitePlace S2847A6.K) where
  localCurve : PuncturedEllipticCurve w.Completion
  local_curve_eq_actual : localCurve = sourceInfiniteLocalCurve S2847A6 w
  xExtension : SourceOrbicurveScalarExtension S2847A6.K w.Completion S.xK
  cExtension : SourceOrbicurveScalarExtension S2847A6.K w.Completion S.cK
  signAction : Iut.OrbicurveSignAction xExtension.result
  quotientMapExtension : SourceOrbicurveMorphismScalarExtension
    xExtension cExtension E.k_quotient.map
  quotient : Iut.OrbicurveSignInvariantMorphism signAction cExtension.result
  quotient_map_eq_extension : quotient.map = quotientMapExtension.result
  quotientWitness : Iut.OrbicurveSignQuotientWitness signAction quotient
  xGroups : SourceOrbicurveGroupData xExtension.result
    (Iut.AbsoluteGaloisProfinite w.Completion)
  cGroups : SourceOrbicurveGroupData cExtension.result
    (Iut.AbsoluteGaloisProfinite w.Completion)
  local_group_inclusion : Iut.ProfiniteFundamentalGroupInclusion
    xGroups.sequence.geometric xGroups.sequence.arithmetic
    cGroups.sequence.geometric cGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite w.Completion)
    xGroups.sequence cGroups.sequence
  xGlobalEmbedding : Iut.ProfiniteFundamentalExactSequenceEmbedding
    xGroups.sequence.geometric xGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite w.Completion)
    E.x_groups.sequence.geometric E.x_groups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite S2847A6.K)
    xGroups.sequence E.x_groups.sequence
  cGlobalEmbedding : Iut.ProfiniteFundamentalExactSequenceEmbedding
    cGroups.sequence.geometric cGroups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite w.Completion)
    E.c_groups.sequence.geometric E.c_groups.sequence.arithmetic
    (Iut.AbsoluteGaloisProfinite S2847A6.K)
    cGroups.sequence E.c_groups.sequence
  galois_embedding_agreement : xGlobalEmbedding.galois.hom = cGlobalEmbedding.galois.hom

structure S2907ClauseEScaffold
    (S : SourceSignQuotientDataCorrected S2847A6)
    (C : S2906ClauseACorrected S)
    (B : S2906ClauseBCorrected S C)
    (D : S2906ClauseCCorrected S C B)
    (E : S2906ClauseDCorrected S C B D) where
  selected_eq_V : S.V = S.V_section.selected
  selected_equiv : NumberFieldPlace S2847A6.Fmod ≃
    {v : NumberFieldPlace S2847A6.K // v ∈ S.V}
  finite_local : ∀ (v : {v : NumberFieldPlace S2847A6.K // v ∈ S.V})
    (hv : v.1.IsFinite),
    S2907FiniteLocalSourceCorrected S C B D E (selectedFinitePlace hv)
  infinite_local : ∀ (v : {v : NumberFieldPlace S2847A6.K // v ∈ S.V})
    (hv : v.1.IsInfinite),
    S2907InfiniteLocalSourceCorrected S C B D E (selectedInfinitePlace hv)

#check S2907FiniteLocalSourceCorrected
#check S2907InfiniteLocalSourceCorrected
#check S2907ClauseEScaffold

end LeanFormal.IUT.XiFPaper.S2907ClauseECorrected
end
