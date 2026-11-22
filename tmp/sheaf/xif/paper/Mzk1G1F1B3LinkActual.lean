import tmp.sheaf.xif.paper.Mzk1G1F1ConsumeActual
import tmp.sheaf.xif.paper.Mzk1G1B3FrameHeightActual
import tmp.sheaf.xif.paper.Mzk1G1B3BundleHeightsActual
import Mathlib.Tactic
/-!
# F1 ↔ B3 unit/height link (documentation + aliases)

F1 (`Mzk1G1F1HeightTransportActual`) supplies the Cech-model data/`H0` frames
(`f1_transport_apply`, `f1_transport_mem_H0`); B3 (`Mzk1G1B3FrameHeightActual`,
`Mzk1G1B3BundleHeightsActual`) supplies the frame-height identifications for the actual
`omega_Y(E)`/`pullback O(1)` units.  The F8 second-equality consumer uses the latter
through `f8_second_equality_omegaE_frame` (`Mzk1G1F8O1Actual`).
-/
noncomputable section
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.F1B3LinkActual
open LeanFormal.IUT.XiFPaper.F1ConsumeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B3FrameHeightActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B3BundleHeightsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F8SecondActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaTransitionGlobalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1A5LineBundleIsoActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaLineBundleActual
variable {k : Type} [Field k] [NumberField k]

/-- B3 unit-level height identity, in the F1/F8 consumer namespace. -/
theorem frameHeight_eq_transport (n : Nat) (hn : 3 ≤ n) (Φ : O0 n →+* k) :
    frameHeight n Φ (omegaYEUnit n) = frameHeight n Φ (pullbackO1Unit n) :=
  b3_frameHeight_omegaE_eq n hn Φ

/-- F1 frame compatibility, re-exported for the height consumer. -/
theorem f1_frame_compat (n : Nat) (D : LeanFormal.IUT.XiFPaper.Mzk1G1F1HeightTransportActual.F1HeightTransportData n) :
    D.cover.ρ0 D.frame0 = (D.transitionUnit : D.cover.A01) * D.cover.ρ1 D.frame1 :=
  f1_transport_apply n D

#print axioms frameHeight_eq_transport
#print axioms f1_frame_compat
end LeanFormal.IUT.XiFPaper.F1B3LinkActual
end