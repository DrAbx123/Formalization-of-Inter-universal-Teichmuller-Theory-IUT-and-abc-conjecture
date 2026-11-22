import tmp.sheaf.xif.paper.S1204SHEOneColumnReadoutActual
import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionConsumerActual
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHECompositionConsumer_readout_unit
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    C.sheLocalization.expression v o =
      (actualSHEOutput I).bundle.localization v unitSection := by
  rw [C.readout_reference_compat, C.indeterminacy_sync]

theorem S3128Stage1SHECompositionConsumer_logShift
    (m m' : Int) (j : SignedLabel l.value) :
    Real.log (J.oneColumnScale m j) = Real.log (J.oneColumnScale m' j) :=
  s1215LogShiftReadoutCompat_actual (J := J) m m' j

theorem S3128Stage1SHECompositionConsumer_theta
    (m : Int) (j : SignedLabel l.value) :
    oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j) :=
  oneColumnLogReadout_theta J m j

theorem S3128Stage1SHECompositionConsumer_frozenSpec :
    HullDeterminantLogVolumeFrozenSpec :=
  s1385FrozenSpec_actual

#check S3128Stage1SHECompositionConsumer_readout_unit
#check S3128Stage1SHECompositionConsumer_logShift
#check S3128Stage1SHECompositionConsumer_theta
#check S3128Stage1SHECompositionConsumer_frozenSpec
end LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionConsumerActual