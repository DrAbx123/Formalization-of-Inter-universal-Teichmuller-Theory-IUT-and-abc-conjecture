import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual
universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

def S3128Stage1SHECompositionPremise : Prop :=
  (∀ (m m' : Int) (j : SignedLabel l.value),
      oneColumnLogReadout J m j = oneColumnLogReadout J m' j) ∧
    (∀ (m : Int) (j : SignedLabel l.value),
      oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j)) ∧
    HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}

theorem S3128Stage1SHECompositionPremise_holds :
    S3128Stage1SHECompositionPremise (J := J) := by
  refine ⟨?_, ?_, s1385FrozenSpec_actual⟩
  · intro m m' j
    exact oneColumnLogReadout_shift J m m' j
  · intro m j
    exact oneColumnLogReadout_theta J m j

theorem S3128Stage1SHE_readout_theta (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j) :=
  oneColumnLogReadout_theta J m j

#check S3128Stage1SHECompositionPremise
#check S3128Stage1SHECompositionPremise_holds
#check S3128Stage1SHE_readout_theta
end LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionActual