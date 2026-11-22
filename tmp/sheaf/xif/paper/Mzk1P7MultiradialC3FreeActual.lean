import tmp.sheaf.xif.paper.Mzk1P0NativeSourceCoreActual
import tmp.sheaf.xif.paper.Mzk1ThetaRootCarrierHaarActual
import tmp.sheaf.xif.paper.Mzk1P7MultiradialProductionActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialC3FreeActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P0NativeSourceCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaRootCarrierActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialProductionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- C3-free source package: P0 native root/tensor core and ThetaRootCarrier. -/
structure C3FreeKummerSource (b : Bad (nativePlaceSelection T)) where
  core : NativeSourceCore T b
  thetaCarrier : ThetaRootCarrier T

noncomputable def c3FreeKummerSource (b : Bad (nativePlaceSelection T)) :
    C3FreeKummerSource T b where
  core := actualNativeSourceCore T b
  thetaCarrier := fun _ => 0

theorem c3FreeKummerSource_qCoeff (b : Bad (nativePlaceSelection T)) :
    (c3FreeKummerSource T b).core.qCoeff =
      ((qVFamily T b).order : Real) := rfl

theorem c3FreeKummerSource_tensorBlock (b : Bad (nativePlaceSelection T)) :
    (c3FreeKummerSource T b).core.tensorBlock = qVFamTensorBlock T b := rfl

/-- Missing paper production fields; no inhabitant. -/
structure C3FreeProductionMissing where
  n : Nat
  oR_LGP : Type
  dPrimeProcessions : Type
  logKummerTransport : Type
  thetaMuLGP : Type
  iplSheApt : Type
  ind1Law : Prop
  ind2Law : Prop
  ind3Law : Prop

#print axioms c3FreeKummerSource_qCoeff
#print axioms c3FreeKummerSource_tensorBlock
end LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialC3FreeActual