import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHEComparisonActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {l : PrimeGeFive} {V : Type uv} [Fintype V]
variable (I : Input Label Choice)
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (R : ∀ v : V, J.SourceImageRealization v) (n : ThetaPilotCarrier l)

structure S1300SHEComparisonData : Type (max (max u v) uv) where
  hdd : S1215HDDLocalLattice (I := I)
  logShift : ∀ (m m' : Int) (j : SignedLabel l.value),
    Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)
  globalData : GlobalHullQPilotComparisonData (I := J) R n

noncomputable def S1300SHEComparisonData.of
    (D : S1300HDDHullDetSource I) : S1300SHEComparisonData I J R n where
  hdd := D.toS1215 (I := I)
  logShift := s1215LogShiftReadoutCompat_actual J
  globalData := globalHullQPilotComparisonData (I := J) R n

theorem S1300SHEComparisonData.comparison_of_condition
    (h : GlobalComparisonCondition (I := J) R n) :
    qPilotThetaHullComparison (I := J) R n :=
  qPilotThetaHullComparison_of_condition (I := J) R n h

#check S1300SHEComparisonData
#check S1300SHEComparisonData.of
#check S1300SHEComparisonData.comparison_of_condition
end LeanFormal.IUT.XiFPaper.S1300SHEComparisonActualAdapted
end
