import tmp.sheaf.xif.paper.S2907ClauseFCorrected
import tmp.sheaf.xif.paper.S2907ClauseECorrected
import tmp.sheaf.xif.paper.S2907bClauseDEActual
import tmp.sheaf.xif.paper.S2906CorrectedClauseABCD
import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD
open LeanFormal.IUT.XiFPaper.S2907ClauseECorrected
open LeanFormal.IUT.XiFPaper.S2907ClauseFCorrected
open LeanFormal.IUT.XiFPaper.S2907bClauseDEActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2925SourceCompletionCorrectedActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- Corrected source completion for the A6 arithmetic data. Clause E/F are
corrected and do not go through the old SourceSignQuotientData. -/
structure SourceCompletionCorrected where
  arithmetic : InitialThetaArithmeticData S2771FiveLabel
  arithmetic_eq : arithmetic = S2847A6
  fbar : SourceFbarExtension S2847A6
  signQuotient : SourceSignQuotientDataCorrected S2847A6
  arithmeticPrelude : SourceArithmeticPrelude S2847A6
  arithmeticPrelude_placeSection :
    arithmeticPrelude.placeSection = signQuotient.V_section
  clauseA : S2906ClauseACorrected signQuotient
  clauseB : S2906ClauseBCorrected signQuotient clauseA
  clauseC : S2906ClauseCCorrected signQuotient clauseA clauseB
  clauseD : S2906ClauseDCorrected signQuotient clauseA clauseB clauseC
  clauseE : S2907ClauseEScaffold signQuotient clauseA clauseB clauseC clauseD
  clauseF : S2907ClauseFCorrected signQuotient clauseA clauseB clauseC clauseD

structure S2916Inputs
    (D : SourceSignQuotientDataCorrected S2847A6) where
  fbar : SourceFbarExtension S2847A6
  arithmeticPrelude : SourceArithmeticPrelude S2847A6
  arithmeticPrelude_placeSection :
    arithmeticPrelude.placeSection = D.V_section
  clauseA : S2906ClauseACorrected D
  clauseB : S2906ClauseBCorrected D clauseA
  clauseC : S2906ClauseCCorrected D clauseA clauseB
  clauseD : S2906ClauseDCorrected D clauseA clauseB clauseC
  clauseE : S2907ClauseEScaffold D clauseA clauseB clauseC clauseD
  clauseF : S2907ClauseFCorrected D clauseA clauseB clauseC clauseD

noncomputable def S2916Completion
    (D : SourceSignQuotientDataCorrected S2847A6)
    (I : S2916Inputs D) :
    SourceCompletionCorrected where
  arithmetic := S2847A6
  arithmetic_eq := rfl
  fbar := I.fbar
  signQuotient := D
  arithmeticPrelude := I.arithmeticPrelude
  arithmeticPrelude_placeSection := I.arithmeticPrelude_placeSection
  clauseA := I.clauseA
  clauseB := I.clauseB
  clauseC := I.clauseC
  clauseD := I.clauseD
  clauseE := I.clauseE
  clauseF := I.clauseF

#check SourceCompletionCorrected
#check S2916Inputs
#check S2916Completion

end LeanFormal.IUT.XiFPaper.S2925SourceCompletionCorrectedActual
end
