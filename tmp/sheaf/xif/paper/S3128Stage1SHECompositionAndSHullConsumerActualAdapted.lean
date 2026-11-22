import tmp.sheaf.xif.paper.S3128Stage1SHECompositionConsumerActual
import tmp.sheaf.xif.paper.S3128Stage1PaperSHullConsumerActual
import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual
import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1204SHEOneColumnReadoutActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionConsumerActual
open LeanFormal.IUT.XiFPaper.S3128Stage1PaperSHullConsumerActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionAndSHullConsumerActualAdapted
universe u v uv ua upi umon ui
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1SHECompositionAndSHull
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (D : PaperIndImageData T b) :
    (C.sheLocalization.expression
        (0 : NumberField.FinitePlace ℚ) (Classical.choice (inferInstance : Nonempty (Theorem311Output I))) =
      (actualSHEOutput I).bundle.localization
        (0 : NumberField.FinitePlace ℚ) unitSection)
      ∧ modelHull T b ⊆ paperSHull T b D :=
  ⟨S3128Stage1SHECompositionConsumer_readout_unit C
      (0 : NumberField.FinitePlace ℚ)
      (Classical.choice (inferInstance : Nonempty (Theorem311Output I))),
    S3128Stage1PaperSHull_modelHull_subset T b D⟩

#check S3128Stage1SHECompositionAndSHull
end LeanFormal.IUT.XiFPaper.S3128Stage1SHECompositionAndSHullConsumerActualAdapted