import tmp.sheaf.xif.paper.S3128Stage1SHELogShiftActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftActualDownstreamActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHELogShiftActualDownstream_zero
    (m m' : Int) (j : SignedLabel l.value) :
    oneColumnLogShift J m m' j = 0 :=
  oneColumnLogShift_eq_zero J m m' j

theorem S3128Stage1SHELogShiftActualDownstream_nonneg
    (m m' : Int) (j : SignedLabel l.value) :
    0 <= oneColumnLogShift J m m' j :=
  oneColumnLogShift_nonneg J m m' j

theorem S3128Stage1SHELogShiftActualDownstream_add
    (m m' m'' : Int) (j : SignedLabel l.value) :
    oneColumnLogShift J m m' j + oneColumnLogShift J m' m'' j =
      oneColumnLogShift J m m'' j :=
  oneColumnLogShift_add J m m' m'' j

theorem S3128Stage1SHELogShiftActualDownstream_theta
    (m m' : Int) (j : SignedLabel l.value) :
    oneColumnLogShift J m m' j =
      Real.log (J.thetaValueAt m 0 j) - Real.log (J.thetaValueAt m' 0 j) :=
  oneColumnLogShift_theta J m m' j

#check S3128Stage1SHELogShiftActualDownstream_zero
#check S3128Stage1SHELogShiftActualDownstream_nonneg
#check S3128Stage1SHELogShiftActualDownstream_add
#check S3128Stage1SHELogShiftActualDownstream_theta
end LeanFormal.IUT.XiFPaper.S3128Stage1SHELogShiftActualDownstreamActual