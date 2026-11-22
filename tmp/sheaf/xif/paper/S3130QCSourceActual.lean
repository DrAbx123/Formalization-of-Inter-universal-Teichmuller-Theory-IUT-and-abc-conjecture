import tmp.sheaf.xif.paper.S2321OUnitsChainFinalActual
import tmp.sheaf.xif.paper.S2280PaperVPrimeMatchActual
import tmp.sheaf.xif.paper.QVFamThetaImageActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3130QCSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2222PaperOUnitsMuAttachmentActual
open LeanFormal.IUT.XiFPaper.S2321OUnitsChainFinalActual
open LeanFormal.IUT.XiFPaper.S2245LogKummerActual
open LeanFormal.IUT.XiFPaper.S2280PaperVPrimeMatchActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual source data for Q_C at a fixed bad place b, conditional on the exact
    paper prime alignment. -/
structure S3130QCSourceData
    (h : LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) where
  qV : FinitePlaceQCandidate ((nativeBadLift T).lift b)
  qV_eq : qV = qVFamily T b
  qNorm : Real
  qNorm_eq : qNorm = qVFamilyQNorm T b
  oUnitsValue : S2219PaperOUnits T b
  oUnitsMu : S2219PaperOUnitsMu T b
  quotientMap : S2219PaperOUnits T b →* S2219PaperOUnitsMu T b
  quotientMap_eq : quotientMap = s2219QuotientMap T b
  attachment : S2222PaperOUnitsMuAttachment T b
  logKummer : S2245LogKummerRequired T b
  chain : S2321OUnitsChain T b
  chain_eq : chain = s2321OUnitsChainOfPrimeAlignment T b h
  logKummer_eq : logKummer = chain.logKummer

noncomputable def s3130QCSourceData
    (h : LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :
    S3130QCSourceData T b h where
  qV := qVFamily T b
  qV_eq := rfl
  qNorm := qVFamilyQNorm T b
  qNorm_eq := rfl
  oUnitsValue := 1
  oUnitsMu := s2219QuotientMap T b 1
  quotientMap := s2219QuotientMap T b
  quotientMap_eq := rfl
  attachment := s2222Attachment T b
  logKummer := (s2321OUnitsChainOfPrimeAlignment T b h).logKummer
  chain := s2321OUnitsChainOfPrimeAlignment T b h
  chain_eq := rfl
  logKummer_eq := rfl

@[simp] theorem s3130QCSourceData_qV
    (h : LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :
    (s3130QCSourceData T b h).qV = qVFamily T b := rfl

@[simp] theorem s3130QCSourceData_qNorm
    (h : LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :
    (s3130QCSourceData T b h).qNorm = qVFamilyQNorm T b := rfl

@[simp] theorem s3130QCSourceData_quotientMap
    (h : LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :
    (s3130QCSourceData T b h).quotientMap = s2219QuotientMap T b := rfl

@[simp] theorem s3130QCSourceData_chain
    (h : LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired T b) :
    (s3130QCSourceData T b h).chain = s2321OUnitsChainOfPrimeAlignment T b h := rfl

#check s3130QCSourceData
#check s3130QCSourceData_qV
#check s3130QCSourceData_chain

end LeanFormal.IUT.XiFPaper.S3130QCSourceActual

end