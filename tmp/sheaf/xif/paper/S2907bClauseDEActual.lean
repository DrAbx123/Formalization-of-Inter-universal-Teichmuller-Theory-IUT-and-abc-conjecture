import tmp.sheaf.xif.paper.S2907CorrectedCompletionInputs
import tmp.sheaf.xif.paper.S2817ClauseDEFScaffold
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2907CorrectedCompletionInputs
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2907bClauseDEActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- Corrected ClauseD scaffold: same literal K-side witnesses as S2817ClauseDScaffold,
but indexed by the corrected source package. -/
structure S2907ClauseDScaffold
    (S : SourceSignQuotientDataCorrected S2847A6) where
  kSignAction : Iut.OrbicurveSignAction S.xK
  kQuotient : Iut.OrbicurveSignInvariantMorphism kSignAction S.cK
  kQuotientWitness : Iut.OrbicurveSignQuotientWitness kSignAction kQuotient
  kQuotientExtension : SourceOrbicurveMorphismScalarExtension
    S.xKExtension S.cKExtension S.quotient.map
  kQuotientMapEqExtension : kQuotient.map = Iut.HyperbolicOrbicurve.Hom.cast
    S.xK_eq_extension.symm S.cK_eq_extension.symm kQuotientExtension.result
  kTorsionCover : SourceOrbicurveFiniteEtaleCover S.xK S.cK
  kTorsionCoverMapEqQuotient : kTorsionCover.map = kQuotient.map
  xGroups : SourceOrbicurveGroupData S.xK
    (Iut.AbsoluteGaloisProfinite S2847A6.K)
  cGroups : SourceOrbicurveGroupData S.cK
    (Iut.AbsoluteGaloisProfinite S2847A6.K)
  groupInclusion :
    Iut.ProfiniteFundamentalGroupInclusion
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.K) xGroups.sequence cGroups.sequence
  xToFGroups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      xGroups.sequence.geometric xGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.K)
      S.xFGroups.sequence.geometric S.xFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.F)
      xGroups.sequence S.xFGroups.sequence
  cToFGroups :
    Iut.ProfiniteFundamentalExactSequenceEmbedding
      cGroups.sequence.geometric cGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.K)
      S.cFGroups.sequence.geometric S.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.F)
      cGroups.sequence S.cFGroups.sequence

#check S2907ClauseDScaffold

end LeanFormal.IUT.XiFPaper.S2907bClauseDEActual
end
