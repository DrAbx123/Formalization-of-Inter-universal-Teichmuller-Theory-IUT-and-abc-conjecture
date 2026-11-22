import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1MultiradialIndImageActual
universe u ua uv upi umon ui uR uVQ
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Consumer: the supplied Ind image is contained in the paper closure hull S. -/
theorem S3128Stage1MultiradialIndImage_subset
    (D : PaperIndImageData (l := l) T b) :
    D.indImage ⊆ paperSHull (l := l) T b D := by
  intro x hx
  exact subset_closure (Or.inr hx)

/-- Consumer: pointwise, every theta possible-image or Ind-image point lies in S. -/
theorem S3128Stage1MultiradialUnion_member
    (D : PaperIndImageData (l := l) T b)
    {x : qVFamTensorBlock T b}
    (hx : x ∈ paperSImageUnion (l := l) T b D) :
    x ∈ paperSHull (l := l) T b D :=
  subset_closure hx

#check S3128Stage1MultiradialIndImage_subset
#check S3128Stage1MultiradialUnion_member
end LeanFormal.IUT.XiFPaper.S3128Stage1MultiradialIndImageActual