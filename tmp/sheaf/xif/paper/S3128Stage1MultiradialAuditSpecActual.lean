import tmp.sheaf.xif.paper.S1126MultiradialAuditActual
noncomputable section
open scoped BigOperators TensorProduct Topology
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S916PaperMultiradialSActual
open LeanFormal.IUT.XiFPaper.S917IndImageUnionActual
open LeanFormal.IUT.XiFPaper.S805NonzeroHullReplacementActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S1126MultiradialAuditActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1MultiradialAuditSpecActual
universe u uX uLabel

structure S3128Stage1MultiradialAuditSpec
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (b : Bad (nativePlaceSelection T)) : Prop where
  qPilot_subset_theta :
    qPilotPaperRegion T b ⊆ paperRootThetaImageNZ T b
  qPilot_subset_augmented :
    ∀ IndImages : Set (qVFamTensorBlock T b),
      qPilotPaperRegion T b ⊆ indAugmentedHull T b IndImages

theorem S3128Stage1MultiradialAuditSpec_ofSource
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (b : Bad (nativePlaceSelection T)) :
    S3128Stage1MultiradialAuditSpec T b :=
  { qPilot_subset_theta :=
      s1126QPilot_subset_thetaImage T b
    qPilot_subset_augmented := fun IndImages =>
      s1126QPilot_subset_augmentedHull T b IndImages }

#check S3128Stage1MultiradialAuditSpec
#check S3128Stage1MultiradialAuditSpec_ofSource
end LeanFormal.IUT.XiFPaper.S3128Stage1MultiradialAuditSpecActual