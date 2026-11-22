import tmp.sheaf.xif.paper.S1300HDDHullDetActual
import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHECompositionActualAdapted
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
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (R : ∀ v : V, J.SourceImageRealization v) (n : ThetaPilotCarrier l)

structure S1300SHEComposition (I : Input Label Choice) : Type (max (max u v) uv) where
  hdd : S1215HDDLocalLattice (I := I)
  logShift : ∀ (m m' : Int) (j : SignedLabel l.value),
    Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)
  indeterminacySync : ∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
    (actualSHEOutput I).readingMap v o =
      (actualSHEOutput I).bundle.localization v unitSection
  comparisonData : GlobalHullQPilotComparisonData (I := J) R n

noncomputable def S1300SHEComposition.of
    (I : Input Label Choice) (D : S1300HDDHullDetSource I) :
    S1300SHEComposition (l := l) (V := V) J R n I where
  hdd := D.toS1215 (I := I)
  logShift := s1215LogShiftReadoutCompat_actual J
  indeterminacySync := s1215IndeterminacySync_actual I
  comparisonData := globalHullQPilotComparisonData (I := J) R n

theorem S1300SHEComposition.of_rank
    (I : Input Label Choice) (D : S1300HDDHullDetSource I) :
    (S1300SHEComposition.of (l := l) (V := V) J R n I D).hdd.rank = D.rank := rfl

#check S1300SHEComposition
#check S1300SHEComposition.of
#check S1300SHEComposition.of_rank
end LeanFormal.IUT.XiFPaper.S1300SHECompositionActualAdapted
end
