import tmp.sheaf.xif.paper.Mzk1P3MassIdentificationActual
import tmp.sheaf.xif.paper.Mzk1P2NativeBlockAlignmentActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3P2AlignmentActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeReadoutActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1P2NativeBlockAlignmentActual
open LeanFormal.IUT.XiFPaper.Mzk1P2DetWeightedNonnegActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]
theorem p2Alignment_nativeLogVolume (b : Bad (nativePlaceSelection T)) :
    (p2NativeBlockPacket T b).logVolume = nativeThetaReadout T b :=
  p2NativeBlockPacket_logVolume T b
theorem p2Alignment_detNonpos : p2WeightedDetLog T ≤ 0 :=
  p2WeightedDetLog_nonpos T
end LeanFormal.IUT.XiFPaper.Mzk1P3P2AlignmentActual
end