import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.S664RootQUnitNormLeOneActual

/-! # Kummer norm-bound bridge: theta image norm and q-image pow norm -/

namespace LeanFormal.IUT.XiFPaper.Mzk1KummerNormBoundBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The label-1 theta image has norm at most one at every bad place. -/
theorem thetaOne_norm_le_one (b : Bad (nativePlaceSelection T)) :
    ‖thetaPilotImage T (oneThetaLabel l) b‖ ≤ 1 := by
  rw [thetaPilotImage_one_apply]
  exact rootNormedElement_norm_le_one (T := T) (b := b) (rootQUnitNormLeOne (T := T))

/-- The theta image is bounded by the actual root image radius. -/
theorem thetaOne_norm_le_radius (b : Bad (nativePlaceSelection T)) :
    ‖thetaPilotImage T (oneThetaLabel l) b‖ ≤ (rootImageRadius T b : Real) := by
  simpa [thetaPilotImage, rootExtensionProductThetaImage] using
    rootImageRadius_ge (T := T) (b := b) (oneThetaLabel l)

/-- The Kummer (2l-power) image of the theta image is bounded by the root radius. -/
theorem thetaOne_pow_norm_le_radius (b : Bad (nativePlaceSelection T)) :
    ‖thetaPilotImage T (oneThetaLabel l) b ^ (2 * l.value)‖ ≤
      (rootImageRadius T b : Real) := by
  rw [norm_pow]
  have h1 : ‖thetaPilotImage T (oneThetaLabel l) b‖ ≤ 1 :=
    thetaOne_norm_le_one T b
  have h2l : 1 ≤ 2 * l.value :=
    Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) l.prime.pos)
  have hdec : ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (2 * l.value) ≤
      ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (1 : Nat) :=
    pow_le_pow_of_le_one (norm_nonneg _) h1 h2l
  calc ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (2 * l.value)
      ≤ ‖thetaPilotImage T (oneThetaLabel l) b‖ ^ (1 : Nat) := hdec
    _ = ‖thetaPilotImage T (oneThetaLabel l) b‖ := pow_one _
    _ ≤ (rootImageRadius T b : Real) := thetaOne_norm_le_radius T b

end LeanFormal.IUT.XiFPaper.Mzk1KummerNormBoundBridgeActual
