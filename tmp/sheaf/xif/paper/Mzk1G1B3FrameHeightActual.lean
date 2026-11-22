/- B3 unit-layer deliverable for andrew's F8 (grace): the ω_Y(E) frame height equals the π^*O(1) frame height.
   This is the F8 second-equation input at the Cech/frame level (andrew consumes it to lift to pullbackO1Unit).
   Route F8 second equation; A5 unit identity omegaYEUnit = pullbackOmegaP1Unit (n >= 3). No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1F8SecondActual
import tmp.sheaf.xif.paper.Mzk1G1A5LineBundleIsoActual
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3FrameHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F8SecondActual

variable {k : Type*} [Field k] [NumberField k]

/-- **F8 第二式的 Čech/frame 层输入**：`ω_Y(E)` 与 `π^*O(1)` 的 frame height 相等。 -/
theorem b3_frameHeight_omegaE_eq (n : Nat) (hn : 3 ≤ n) (Φ : O0 n →+* k) :
    frameHeight n Φ (omegaYEUnit n) = frameHeight n Φ (pullbackO1Unit n) := by
  rw [frameHeight_omegaYEUnit n hn Φ, frameHeight_pullbackO1Unit n Φ]

/-- 同一陈述的 `pullbackOmegaP1Unit` 版本（A5 的命名）。 -/
theorem b3_frameHeight_omegaE_eq_pullbackOmega (n : Nat) (hn : 3 ≤ n) (Φ : O0 n →+* k) :
    frameHeight n Φ (omegaYEUnit n) = frameHeight n Φ (pullbackOmegaP1Unit n) := by
  rw [omegaYEUnit_eq_pullbackUnit n hn]

#print axioms b3_frameHeight_omegaE_eq
#print axioms b3_frameHeight_omegaE_eq_pullbackOmega

end LeanFormal.IUT.XiFPaper.Mzk1G1B3FrameHeightActual
