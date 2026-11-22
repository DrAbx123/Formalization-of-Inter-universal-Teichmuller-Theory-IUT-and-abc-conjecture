import tmp.sheaf.xif.paper.S2925SourceCompletionCorrectedActual
import tmp.sheaf.xif.paper.S2908CorrectedSActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD
open LeanFormal.IUT.XiFPaper.S2907ClauseECorrected
open LeanFormal.IUT.XiFPaper.S2907ClauseFCorrected
open LeanFormal.IUT.XiFPaper.S2907bClauseDEActual
open LeanFormal.IUT.XiFPaper.S2908CorrectedSActual
open LeanFormal.IUT.XiFPaper.S2925SourceCompletionCorrectedActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2926CorrectedCompletionPackagingActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- Explicit corrected-completion input: S2908 corrected S, S2906 clauses A-D,
and the S2907 ClauseF package (kSide/localFamily/boundary are actual). -/
structure S2926Inputs (S : SourceSignQuotientDataCorrected S2847A6) where
  fbar : SourceFbarExtension S2847A6
  arithmeticPrelude : SourceArithmeticPrelude S2847A6
  arithmeticPrelude_placeSection :
    arithmeticPrelude.placeSection = S.V_section
  clauseA : S2906ClauseACorrected S
  clauseB : S2906ClauseBCorrected S clauseA
  clauseC : S2906ClauseCCorrected S clauseA clauseB
  clauseD : S2906ClauseDCorrected S clauseA clauseB clauseC
  clauseF : S2907ClauseFCorrected S clauseA clauseB clauseC clauseD

namespace S2926Inputs

variable {S : SourceSignQuotientDataCorrected S2847A6}

noncomputable def kSide (I : S2926Inputs S) : S2907ClauseDScaffold S :=
  I.clauseF.kSide

noncomputable def localFamily (I : S2926Inputs S) :
    S2907ClauseEScaffold S I.clauseA I.clauseB I.clauseC I.clauseD :=
  I.clauseF.localFamily

noncomputable def boundary (I : S2926Inputs S) :
    S2907ClauseFScaffold S I.clauseA I.clauseB I.clauseC I.clauseD :=
  I.clauseF.boundary

end S2926Inputs

/-- Feed the S2926 package into S2925's corrected completion input. -/
noncomputable def S2926_toS2916Inputs
    (S : SourceSignQuotientDataCorrected S2847A6)
    (I : S2926Inputs S) : S2916Inputs S where
  fbar := I.fbar
  arithmeticPrelude := I.arithmeticPrelude
  arithmeticPrelude_placeSection := I.arithmeticPrelude_placeSection
  clauseA := I.clauseA
  clauseB := I.clauseB
  clauseC := I.clauseC
  clauseD := I.clauseD
  clauseE := I.clauseF.localFamily
  clauseF := I.clauseF

/-- Corrected completion from the explicit S2926 package. -/
noncomputable def S2926Completion
    (S : SourceSignQuotientDataCorrected S2847A6)
    (I : S2926Inputs S) : SourceCompletionCorrected :=
  S2916Completion S (S2926_toS2916Inputs S I)

#check S2926Inputs
#check S2926Inputs.kSide
#check S2926Inputs.localFamily
#check S2926Inputs.boundary
#check S2926_toS2916Inputs
#check S2926Completion
#print axioms S2926Completion

end LeanFormal.IUT.XiFPaper.S2926CorrectedCompletionPackagingActual
end
