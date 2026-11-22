import tmp.sheaf.xif.paper.NativeTateQSquaresBasicIntegrality
noncomputable section
namespace TestMax
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeTateQSquaresBasicIntegrality

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

example : Valued (localField (l:=l) T b) (WithZero (Multiplicative ℤ)) := inferInstance
example : Algebra (localRing (l:=l) T b) (localField (l:=l) T b) := inferInstance

end TestMax
end
