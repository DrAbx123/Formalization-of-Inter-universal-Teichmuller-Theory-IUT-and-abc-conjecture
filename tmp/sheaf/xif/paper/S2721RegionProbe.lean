import tmp.sheaf.xif.paper.S2586IQHullLogVolumeInstantiationActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2586IQHullLogVolumeInstantiationActual
open LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
namespace LeanFormal.IUT.XiFPaper.S2721RegionProbe

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]

#check (inferInstance : Measure.NullSingletonClass
  (Measure.addHaar : Measure (qVFamTensorBlock T b)))
#check (Measure.addHaar : Measure (qVFamTensorBlock T b)) {S2588PointMap (l := l) T b 0 0 0}

end LeanFormal.IUT.XiFPaper.S2721RegionProbe
end
