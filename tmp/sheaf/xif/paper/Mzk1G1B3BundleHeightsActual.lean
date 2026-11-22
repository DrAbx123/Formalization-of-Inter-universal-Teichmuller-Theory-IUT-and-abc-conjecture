/- B3 unit/frame layer supplement (grace): general transport lemmas for the Cech frame height
   used by andrew's F8 chain (b3_frameHeight_omegaE_eq already DONE 22:58:40). No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1G1B3FrameHeightActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B3BundleHeightsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F8SecondActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B3FrameHeightActual

variable {k : Type*} [Field k] [NumberField k]

/-- frameHeight 只依赖单元的值：相等的单元给出相等的 frame height。 -/
theorem frameHeight_congr (n : Nat) (Φ : O0 n →+* k) {u v : (O0 n)ˣ} (h : u = v) :
    frameHeight n Φ u = frameHeight n Φ v :=
  congrArg (frameHeight n Φ) h

/-- `π^*O(1)` 与 `π^*ω_{P¹}` 的 frame height 相等（A5 命名版）。 -/
theorem frameHeight_pullbackO1_eq_pullbackOmega (n : Nat) (hn : 3 ≤ n) (Φ : O0 n →+* k) :
    frameHeight n Φ (pullbackO1Unit n) = frameHeight n Φ (pullbackOmegaP1Unit n) := by
  rw [show pullbackOmegaP1Unit n = pullbackO1Unit n from rfl]

#print axioms frameHeight_congr
#print axioms frameHeight_pullbackO1_eq_pullbackOmega

end LeanFormal.IUT.XiFPaper.Mzk1G1B3BundleHeightsActual
