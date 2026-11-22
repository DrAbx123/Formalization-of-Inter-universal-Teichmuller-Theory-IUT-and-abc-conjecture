import tmp.sheaf.xif.paper.S1126MultiradialAuditActual
import tmp.sheaf.xif.paper.S917IndImageUnionActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1126MultiradialAuditActual
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1IndStrictEnlargementConsumerActual
universe u uX uLabel
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: S1126 Ind strict enlargement is exactly the S917 condition. -/
theorem S3128Stage1IndStrictEnlargement_iff
    (IndImages : Set (qVFamTensorBlock T b)) :
    S1126IndStrictEnlargement (l := l) T b IndImages ↔
      IndStrictEnlargement (l := l) T b IndImages := Iff.rfl

/-- Consumer: S1126 paper Ind-image transfer is exactly nonempty S916 data. -/
theorem S3128Stage1PaperIndImageTransfer_iff :
    S1126PaperIndImageTransfer (l := l) T b ↔
      Nonempty (PaperIndImageData (l := l) T b) := Iff.rfl

theorem S3128Stage1PaperSStrictEnlargement_iff
    (D : PaperIndImageData (l := l) T b) :
    S1126PaperSStrictEnlargement (l := l) T b D ↔
      PaperSStrictEnlargement (l := l) T b D := Iff.rfl

#check S3128Stage1IndStrictEnlargement_iff
#check S3128Stage1PaperIndImageTransfer_iff
#check S3128Stage1PaperSStrictEnlargement_iff
end LeanFormal.IUT.XiFPaper.S3128Stage1IndStrictEnlargementConsumerActual