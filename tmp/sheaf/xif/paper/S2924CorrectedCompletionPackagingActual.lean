import tmp.sheaf.xif.paper.S2907ClauseFCorrected
import tmp.sheaf.xif.paper.S2908CorrectedSActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD
open LeanFormal.IUT.XiFPaper.S2907ClauseFCorrected
open LeanFormal.IUT.XiFPaper.S2907bClauseDEActual
open LeanFormal.IUT.XiFPaper.S2907ClauseECorrected
open LeanFormal.IUT.XiFPaper.S2908CorrectedSActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2924CorrectedCompletionPackagingActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- Explicit corrected-completion input package: corrected S plus corrected
Clauses A-D and the packaged ClauseF, whose kSide/localFamily/boundary are
already actual structures. -/
structure S2924CorrectedCompletionInputs
    (S : SourceSignQuotientDataCorrected S2847A6) where
  clauseA : S2906ClauseACorrected S
  clauseB : S2906ClauseBCorrected S clauseA
  clauseC : S2906ClauseCCorrected S clauseA clauseB
  clauseD : S2906ClauseDCorrected S clauseA clauseB clauseC
  clauseF : S2907ClauseFCorrected S clauseA clauseB clauseC clauseD

namespace S2924CorrectedCompletionInputs

variable {S : SourceSignQuotientDataCorrected S2847A6}

noncomputable def kSide (I : S2924CorrectedCompletionInputs S) :
    S2907ClauseDScaffold S := I.clauseF.kSide

noncomputable def localFamily (I : S2924CorrectedCompletionInputs S) :
    S2907ClauseEScaffold S I.clauseA I.clauseB I.clauseC I.clauseD :=
  I.clauseF.localFamily

noncomputable def boundary (I : S2924CorrectedCompletionInputs S) :
    S2907ClauseFScaffold S I.clauseA I.clauseB I.clauseC I.clauseD :=
  I.clauseF.boundary

noncomputable def multiplicative (I : S2924CorrectedCompletionInputs S) :
    ∀ (p : NumberField.FinitePlace S2847A6.F),
      NumberFieldFinitePlace.comap (k := S2847A6.Fmod) p ∈ S.V_mod_bad →
        S2847A6.curve.HasMultiplicativeReductionAt p :=
  I.clauseF.multiplicative

noncomputable def xFGroups (I : S2924CorrectedCompletionInputs S) :
    SourceOrbicurveGroupData S.xF (Iut.AbsoluteGaloisProfinite S2847A6.F) :=
  S.xFGroups

noncomputable def cFGroups (I : S2924CorrectedCompletionInputs S) :
    SourceOrbicurveGroupData S.cF (Iut.AbsoluteGaloisProfinite S2847A6.F) :=
  S.cFGroups

noncomputable def fGroupInclusion (I : S2924CorrectedCompletionInputs S) :
    Iut.ProfiniteFundamentalGroupInclusion
      I.xFGroups.sequence.geometric I.xFGroups.sequence.arithmetic
      I.cFGroups.sequence.geometric I.cFGroups.sequence.arithmetic
      (Iut.AbsoluteGaloisProfinite S2847A6.F)
      I.xFGroups.sequence I.cFGroups.sequence :=
  S.fGroupInclusion

end S2924CorrectedCompletionInputs

#check S2924CorrectedCompletionInputs
#check S2924CorrectedCompletionInputs.kSide
#check S2924CorrectedCompletionInputs.localFamily
#check S2924CorrectedCompletionInputs.boundary
#print axioms S2924CorrectedCompletionInputs.kSide

end LeanFormal.IUT.XiFPaper.S2924CorrectedCompletionPackagingActual
end
