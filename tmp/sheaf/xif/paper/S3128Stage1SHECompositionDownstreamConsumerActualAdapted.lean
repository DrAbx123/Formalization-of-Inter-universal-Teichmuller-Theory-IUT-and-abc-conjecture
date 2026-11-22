import tmp.sheaf.xif.paper.S3128Stage1SHECompositionConsumerActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionDownstreamConsumerActualAdapted
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHECompositionDownstream_chain
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    C.sheLocalization.expression v o =
        (actualSHEOutput I).bundle.localization v unitSection
      ∧ HullDeterminantLogVolumeFrozenSpec :=
  ⟨S3128Stage1SHECompositionConsumer_readout_unit C v o,
    S3128Stage1SHECompositionConsumer_frozenSpec⟩

theorem S3128Stage1SHECompositionDownstream_logTheta
    (m m' : Int) (j : SignedLabel l.value) :
    Real.log (J.oneColumnScale m j) =
        Real.log (J.oneColumnScale m' j)
      ∧ oneColumnLogReadout J m j = Real.log (J.thetaValueAt m 0 j) :=
  ⟨S3128Stage1SHECompositionConsumer_logShift (l := l) (J := J) m m' j,
    S3128Stage1SHECompositionConsumer_theta (J := J) m j⟩

#check S3128Stage1SHECompositionDownstream_chain
#check S3128Stage1SHECompositionDownstream_logTheta
end LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionDownstreamConsumerActualAdapted