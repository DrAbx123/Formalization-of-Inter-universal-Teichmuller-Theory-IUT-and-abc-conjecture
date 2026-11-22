import tmp.sheaf.xif.paper.S3128Stage1SHECompositionConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1SHEHDDSpecActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHEHDDSpecActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHESpecAndCompositionConsumerActualAdapted
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

theorem S3128Stage1SHESpecAndComposition
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    (∀ (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I),
        C.sheLocalization.expression v o =
          (actualSHEOutput I).bundle.localization v unitSection)
      ∧ (∀ (m m' : Int) (j : SignedLabel l.value),
          Real.log (J.oneColumnScale m j) =
            Real.log (J.oneColumnScale m' j)) :=
  ⟨fun v o => S3128Stage1SHECompositionConsumer_readout_unit C v o,
    fun m m' j =>
      S3128Stage1SHECompositionConsumer_logShift
        (l := l) (J := J) m m' j⟩

#check S3128Stage1SHESpecAndComposition
end LeanFormal.IUT.XiFPaper.S3128Stage1SHESpecAndCompositionConsumerActualAdapted