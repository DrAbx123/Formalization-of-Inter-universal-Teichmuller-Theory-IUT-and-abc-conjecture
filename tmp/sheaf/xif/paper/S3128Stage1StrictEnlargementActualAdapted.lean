import tmp.sheaf.xif.paper.S1126MultiradialAuditActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1126MultiradialAuditActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1StrictEnlargementActualAdapted
universe u uX uLabel
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: S1126 paper strict enlargement is definitionally the S916 paper
strict enlargement. -/
theorem S3128Stage1StrictEnlargement_iff
    (D : PaperIndImageData (l := l) T b) :
    S1126PaperSStrictEnlargement (l := l) T b D ↔
      PaperSStrictEnlargement (l := l) T b D := Iff.rfl

/-- Consumer: S1126 strict enlargement gives the proper hull containment. -/
theorem S3128Stage1StrictEnlargement_ssubset
    (D : PaperIndImageData (l := l) T b)
    (h : S1126PaperSStrictEnlargement (l := l) T b D) :
    modelHull T b ⊂ paperSHull (l := l) T b D :=
  modelHull_ssubset_paperSHull_of_strict (l := l) T b D h

#check S3128Stage1StrictEnlargement_iff
#check S3128Stage1StrictEnlargement_ssubset
end LeanFormal.IUT.XiFPaper.S3128Stage1StrictEnlargementActualAdapted