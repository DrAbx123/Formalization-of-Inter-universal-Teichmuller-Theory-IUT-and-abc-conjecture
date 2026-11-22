import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Actual log-shift of the one-column readout between two stages. -/
noncomputable def oneColumnLogShift (m m' : Int) (j : SignedLabel l.value) : Real :=
  oneColumnLogReadout J m j - oneColumnLogReadout J m' j

theorem oneColumnLogShift_eq_zero (m m' : Int) (j : SignedLabel l.value) :
    oneColumnLogShift J m m' j = 0 :=
  sub_eq_zero.mpr (oneColumnLogReadout_shift J m m' j)

theorem oneColumnLogShift_nonneg (m m' : Int) (j : SignedLabel l.value) :
    0 <= oneColumnLogShift J m m' j := by
  rw [oneColumnLogShift_eq_zero]

theorem oneColumnLogShift_add (m m' m'' : Int) (j : SignedLabel l.value) :
    oneColumnLogShift J m m' j + oneColumnLogShift J m' m'' j =
      oneColumnLogShift J m m'' j := by
  unfold oneColumnLogShift
  ring

theorem oneColumnLogShift_theta (m m' : Int) (j : SignedLabel l.value) :
    oneColumnLogShift J m m' j =
      Real.log (J.thetaValueAt m 0 j) - Real.log (J.thetaValueAt m' 0 j) := by
  unfold oneColumnLogShift
  rw [oneColumnLogReadout_theta, oneColumnLogReadout_theta]

#check oneColumnLogShift
#check oneColumnLogShift_eq_zero
#check oneColumnLogShift_nonneg
#check oneColumnLogShift_add
#check oneColumnLogShift_theta
end LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftActual