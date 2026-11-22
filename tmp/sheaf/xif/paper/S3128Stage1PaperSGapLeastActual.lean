import tmp.sheaf.xif.paper.S909PaperSVsLeastHullActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S909PaperSVsLeastHullActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1PaperSGapLeastActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: an external paper S gap gives least lambda-O hull ⊂ paperS. -/
theorem S3128Stage1LeastLambdaO_ssubset_paperS
    (G : PaperSVsModelHullGap (l := l) T b) :
    paperLeastLambdaOHull (l := l) T b ⊂ G.paperS := by
  change modelHull T b ⊂ G.paperS
  exact ⟨G.model_subset_paperS, by
    rintro hsub
    rcases G.paperS_strict with ⟨x, hxS, hxnot⟩
    exact hxnot (hsub hxS)⟩

#check S3128Stage1LeastLambdaO_ssubset_paperS
end LeanFormal.IUT.XiFPaper.S3128Stage1PaperSGapLeastActual