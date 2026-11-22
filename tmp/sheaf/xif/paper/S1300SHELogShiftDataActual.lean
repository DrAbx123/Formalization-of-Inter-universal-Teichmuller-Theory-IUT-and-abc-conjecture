import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1300SHELogShiftDataActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

structure S1300SHELogShiftData : Type where
  shift : ∀ (m m' : Int) (j : SignedLabel l.value),
    Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j)
  readout_theta : ∀ (m : Int) (j : SignedLabel l.value),
    Real.log (J.oneColumnScale m j) = Real.log (J.thetaValueAt m 0 j)

noncomputable def S1300SHELogShiftData.of : S1300SHELogShiftData J where
  shift := s1215LogShiftReadoutCompat_actual J
  readout_theta := fun m j => oneColumnLogReadout_theta J m j

#check S1300SHELogShiftData
#check S1300SHELogShiftData.of
end LeanFormal.IUT.XiFPaper.S1300SHELogShiftDataActual
end
