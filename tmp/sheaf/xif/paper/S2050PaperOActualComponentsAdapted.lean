import tmp.sheaf.xif.paper.S2031FDoublePlusFamilyActualAdapted
import tmp.sheaf.xif.paper.S2032R6GeneratorActual
import tmp.sheaf.xif.paper.S2034OperationKummerActual
import tmp.sheaf.xif.paper.S2035ActualOUnitsMuActual
import tmp.sheaf.xif.paper.S2037FDoublePlusPi1ActualAdapted
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S2031FDoublePlusFamilyActualAdapted
open LeanFormal.IUT.XiFPaper.S2032R6GeneratorActual
open LeanFormal.IUT.XiFPaper.S2034OperationKummerActual
open LeanFormal.IUT.XiFPaper.S2035ActualOUnitsMuActual
open LeanFormal.IUT.XiFPaper.S2037FDoublePlusPi1ActualAdapted
namespace LeanFormal.IUT.XiFPaper.S2050PaperOActualComponentsAdapted
/-- Actual components available. Not PaperOActual. -/
structure S2050ActualComponents (D : S1895PaperInput) (l : PrimeGeFive) where
  envCarrier : FDoublePlusPrimeStrip PaperV
  gauCarrier : FDoublePlusPrimeStrip PaperV
  oUnits : PaperV → Type
  oUnitsMu : PaperV → Type
  kummerIso : ∀ v : PaperV,
    TimesMuKummer.Isomorphism (actualOUnitsAction v) (actualStripUnitsAction v)
  evaluationSquare :
    SourceKummerEvaluationSquare LocG localOFieldStrip localOFieldStrip
      localOFieldStrip localOFieldStrip
  localQ : PaperV → Type
noncomputable def s2050ActualComponents (D : S1895PaperInput) (l : PrimeGeFive) :
    S2050ActualComponents D l where
  envCarrier := oneColumnEnvDoublePlus
  gauCarrier := oneColumnGauDoublePlus l
  oUnits := fun v => LocalOFieldUnitsAt v
  oUnitsMu := fun v => actualOUnitsMu v
  kummerIso := fun v => actualKummerIso v
  evaluationSquare := actualSquare
  localQ := fun v => LocalOFieldIntegralAt v
theorem s2050ActualComponents_nonempty (D : S1895PaperInput) (l : PrimeGeFive) :
    Nonempty (S2050ActualComponents D l) :=
  ⟨s2050ActualComponents D l⟩
/-- Exact missing (a): actual curve pi_1 family. -/
def S2050CurvePi1Missing (D : S1895PaperInput) : Prop := S2037FirstMissing D
/-- Exact missing (b): Fmod-indexed actual theta/Gaussian monoid family. -/
abbrev S2050ThetaAssignmentMissing (D : S1895PaperInput) : Type 1 :=
  FmodLocalThetaModel D
/-- Exact missing (c): Aut(G_v)-action on actual O^x. -/
abbrev S2050AutActionMissing (v : PaperV) : Type := S2035FirstMissing v
/-- Exact missing (e): attachment of the actual local Kummer/evaluation square
to the S1895 paper input. -/
abbrev S2050PaperAttachmentMissing
    (D : S1895OIdentificationsActual.S1895PaperInput) : Type 1 :=
  S1895AttachmentMissing D
#check S2050ActualComponents
#check s2050ActualComponents_nonempty
#check S2050CurvePi1Missing
#check S2050ThetaAssignmentMissing
#check S2050AutActionMissing
#check S2050PaperAttachmentMissing
end LeanFormal.IUT.XiFPaper.S2050PaperOActualComponentsAdapted
end
