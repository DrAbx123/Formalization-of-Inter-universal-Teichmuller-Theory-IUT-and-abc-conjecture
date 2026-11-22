import tmp.sheaf.xif.paper.S2925SourceCompletionCorrectedActual
import tmp.sheaf.xif.paper.S2926CorrectedCompletionPackagingActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2906CorrectedClauseABCD
open LeanFormal.IUT.XiFPaper.S2907ClauseECorrected
open LeanFormal.IUT.XiFPaper.S2907ClauseFCorrected
open LeanFormal.IUT.XiFPaper.S2907bClauseDEActual
open LeanFormal.IUT.XiFPaper.S2925SourceCompletionCorrectedActual
open LeanFormal.IUT.XiFPaper.S2926CorrectedCompletionPackagingActual
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2928CorrectedTConstructionActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

/-- Corrected native T data: corrected source record and corrected clauses. -/
structure SourceNativeInitialThetaDataCorrected where
  arithmetic : InitialThetaArithmeticData S2771FiveLabel
  arithmetic_eq : arithmetic = S2847A6
  fbar : SourceFbarExtension S2847A6
  source : SourceSignQuotientDataCorrected S2847A6
  arithmeticPrelude : SourceArithmeticPrelude S2847A6
  arithmeticPrelude_placeSection :
    arithmeticPrelude.placeSection = source.V_section
  clauseA : S2906ClauseACorrected source
  clauseB : S2906ClauseBCorrected source clauseA
  clauseC : S2906ClauseCCorrected source clauseA clauseB
  clauseD : S2906ClauseDCorrected source clauseA clauseB clauseC
  clauseE : S2907ClauseEScaffold source clauseA clauseB clauseC clauseD
  clauseF : S2907ClauseFCorrected source clauseA clauseB clauseC clauseD

/-- The corrected T extracted from a corrected completion. -/
noncomputable def S2928CorrectedT_ofCompletion
    (C : SourceCompletionCorrected) :
    SourceNativeInitialThetaDataCorrected where
  arithmetic := C.arithmetic
  arithmetic_eq := C.arithmetic_eq
  fbar := C.fbar
  source := C.signQuotient
  arithmeticPrelude := C.arithmeticPrelude
  arithmeticPrelude_placeSection := C.arithmeticPrelude_placeSection
  clauseA := C.clauseA
  clauseB := C.clauseB
  clauseC := C.clauseC
  clauseD := C.clauseD
  clauseE := C.clauseE
  clauseF := C.clauseF

/-- The corrected T from S2916Inputs via S2916Completion. -/
noncomputable def S2928CorrectedT
    (S : SourceSignQuotientDataCorrected S2847A6)
    (I : S2916Inputs S) :
    SourceNativeInitialThetaDataCorrected :=
  S2928CorrectedT_ofCompletion (S2916Completion S I)

/-- The corrected T from the S2926 packaged inputs. -/
noncomputable def S2928CorrectedT_ofS2926
    (S : SourceSignQuotientDataCorrected S2847A6)
    (I : S2926Inputs S) :
    SourceNativeInitialThetaDataCorrected :=
  S2928CorrectedT_ofCompletion (S2926Completion S I)

#check SourceNativeInitialThetaDataCorrected
#check S2928CorrectedT_ofCompletion
#check S2928CorrectedT
#check S2928CorrectedT_ofS2926

end LeanFormal.IUT.XiFPaper.S2928CorrectedTConstructionActual
end
