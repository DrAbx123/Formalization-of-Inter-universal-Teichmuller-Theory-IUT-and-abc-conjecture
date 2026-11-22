import tmp.sheaf.xif.paper.Mzk1G1F1HeightTransportActual
import tmp.sheaf.xif.paper.Mzk1G1F8SecondActual
import tmp.sheaf.xif.paper.Mzk1G1B3FrameHeightActual
import Mathlib.Tactic
/-!
# F1 transport consumption

`Mzk1G1F1HeightTransportActual.F1HeightTransportData` packages a two-chart cover, the
transition unit and compatible H0 frames (route F1).  This file exposes the two consumer
forms: the explicit frame-compatibility equality and the H0 membership.
-/
noncomputable section
open AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.F1ConsumeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1F1HeightTransportActual

/-- The F1 frame compatibility, read off from the structure field (transport direction). -/
theorem f1_transport_apply (n : Nat) (D : F1HeightTransportData n) :
    D.cover.ρ0 D.frame0 = (D.transitionUnit : D.cover.A01) * D.cover.ρ1 D.frame1 :=
  D.frame_compat

/-- The F1 frames are H0 sections of the line bundle (donor `mem_H0_lineBundle_iff`). -/
theorem f1_transport_mem_H0 (n : Nat) (D : F1HeightTransportData n) :
    (D.frame0, D.frame1) ∈ (D.cover.lineBundle D.transitionUnit).H0 :=
  (f1_frame_mem_H0 n D).mpr D.frame_compat

/-- The interface is inhabited (trivial cover), the fallback used by the P8 assembly. -/
theorem f1_transport_nonempty (n : Nat) : Nonempty (F1HeightTransportData n) :=
  f1HeightTransportData_nonempty n

#print axioms f1_transport_apply
#print axioms f1_transport_mem_H0
#print axioms f1_transport_nonempty
end LeanFormal.IUT.XiFPaper.F1ConsumeActual
end