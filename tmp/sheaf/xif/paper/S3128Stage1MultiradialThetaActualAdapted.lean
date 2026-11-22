import tmp.sheaf.xif.paper.S916PaperMultiradialSActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1MultiradialThetaActualAdapted
universe u ua uv upi umon ui uR uVQ
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem S3128Stage1MultiradialTheta_subset_paperSHull
    (D : PaperIndImageData T b) :
    paperRootThetaImageNZ T b ⊆ paperSHull T b D := by
  intro x hx
  exact subset_closure (Or.inl hx)

theorem S3128Stage1MultiradialUnion_subset_paperSHull
    (D : PaperIndImageData T b) :
    paperSImageUnion T b D ⊆ paperSHull T b D :=
  subset_closure

#check S3128Stage1MultiradialTheta_subset_paperSHull
#check S3128Stage1MultiradialUnion_subset_paperSHull
end LeanFormal.IUT.XiFPaper.S3128Stage1MultiradialThetaActualAdapted