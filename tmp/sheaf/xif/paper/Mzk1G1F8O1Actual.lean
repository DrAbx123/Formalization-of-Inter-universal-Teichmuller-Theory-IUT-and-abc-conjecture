import tmp.sheaf.xif.paper.Mzk1G1F8SecondActual
import tmp.sheaf.xif.paper.Mzk1G1B3FrameHeightActual
import tmp.sheaf.xif.paper.Mzk1G1F8ChainActual
import Mathlib.Tactic
/-!
# F8 with the O(1) frame bridge

`b3_frameHeight_omegaE_eq` (grace, 22:58:40) identifies the `omega_Y(E)` and `pi^*O(1)`
frame heights, so F8's second equality now holds with the actual `omegaYEUnit` frame:
`frameHeight omegaYEUnit = n/(n-3) * frameHeight transitionUnit`.
This is the frame-level F8 second-equation input for the P8 assembly (`Mzk1G1P8ProducerAssemblyActual`).
-/
noncomputable section
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F8O1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1F8SecondActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B3FrameHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
variable {k : Type*} [Field k] [NumberField k]

/-- **F8 second equality with the actual `omega_Y(E)` frame.** -/
theorem f8_second_equality_omegaE_frame (n : Nat) (hn : 4 ≤ n) (Φ : O0 n →+* k) :
    frameHeight n Φ (omegaYEUnit n)
      = ((n : ℝ) / ((n : ℝ) - 3)) * frameHeight n Φ (transitionUnit n) := by
  rw [b3_frameHeight_omegaE_eq n (by omega) Φ, f8_second_equality_frame n hn Φ]

#print axioms f8_second_equality_omegaE_frame
end LeanFormal.IUT.XiFPaper.Mzk1G1F8O1Actual
end