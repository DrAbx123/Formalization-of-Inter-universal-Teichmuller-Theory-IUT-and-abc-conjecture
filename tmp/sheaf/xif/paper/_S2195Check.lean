import tmp.sheaf.xif.paper.S2195Layer1InstanceActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2195Check

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S2195Layer1InstanceActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
  (b : Bad (nativePlaceSelection T))

example : S2135Layer1ConstructionRequired (l := l) T b :=
  s2195_layer1ConstructionRequired T b

example :
    S2135CompletionFinrankOne (l := l) T b ↔
      Module.finrank
        ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.adicCompletion ℚ)
        ((qVFamTensorPlace T b).maximalIdeal.adicCompletion T.arithmetic.F) = 1 :=
  s2195_finrank_instance_alignment T b

#check s2195_completionFinrankOne T b
#check s2195_completionEquivOfPlace T b
#check s2195_primeAlignedSplitPackage T b
#check s2195_exists_primeAlignedSplitPackage T b
#check s2195_nonempty_primeAlignedSplitPackage_iff T b

#print axioms s2195_layer1ConstructionRequired
#print axioms s2195_finrank_instance_alignment
#print axioms s2195_primeAlignedSplitPackage

end LeanFormal.IUT.XiFPaper.S2195Check
end
