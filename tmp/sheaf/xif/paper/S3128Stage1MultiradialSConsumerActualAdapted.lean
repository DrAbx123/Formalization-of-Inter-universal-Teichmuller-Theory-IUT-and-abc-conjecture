import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1MultiradialSConsumerActualAdapted
universe u ua uv upi umon ui uR uVQ
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: the actual multiradial closure hull contains the model hull. -/
theorem S3128Stage1MultiradialSConsumer_subset
    (D : PaperIndImageData (l := l) T b) :
    modelHull T b ⊆ paperSHull (l := l) T b D :=
  modelHull_subset_paperSHull (l := l) T b D

/-- Consumer: strict Ind-image enlargement gives the proper containment. -/
theorem S3128Stage1MultiradialSConsumer_ssubset
    (D : PaperIndImageData (l := l) T b)
    (hstrict : PaperSStrictEnlargement (l := l) T b D) :
    modelHull T b ⊂ paperSHull (l := l) T b D :=
  modelHull_ssubset_paperSHull_of_strict (l := l) T b D hstrict

/-- Consumer: the three actual Ind-transfer obligations package as the required
multiradial transfer proposition. -/
theorem S3128Stage1MultiradialSConsumer_transfer
    (D : PaperIndImageData (l := l) T b)
    (h1 : D.ind1_transfer) (h2 : D.ind2_transfer)
    (h3 : D.ind3_transfer) :
    PaperIndImageTransferRequired (l := l) T b D :=
  ⟨h1, h2, h3⟩

#check S3128Stage1MultiradialSConsumer_subset
#check S3128Stage1MultiradialSConsumer_ssubset
#check S3128Stage1MultiradialSConsumer_transfer
end LeanFormal.IUT.XiFPaper.S3128Stage1MultiradialSConsumerActualAdapted