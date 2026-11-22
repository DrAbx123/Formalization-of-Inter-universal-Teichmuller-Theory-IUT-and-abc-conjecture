import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnScaleThetaConsumerActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1OneColumnScale_readout
    (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j =
      Real.log (J.oneColumnScale m j) := rfl

theorem S3128Stage1OneColumnScale_eq_theta
    (m : Int) (j : SignedLabel l.value) :
    Real.log (J.oneColumnScale m j) =
      Real.log (J.thetaValueAt m 0 j) := by
  rw [← S3128Stage1OneColumnScale_readout J m j]
  exact oneColumnLogReadout_theta J m j

#check S3128Stage1OneColumnScale_readout
#check S3128Stage1OneColumnScale_eq_theta
end LeanFormal.IUT.XiFPaper.S3128Stage1OneColumnScaleThetaConsumerActual