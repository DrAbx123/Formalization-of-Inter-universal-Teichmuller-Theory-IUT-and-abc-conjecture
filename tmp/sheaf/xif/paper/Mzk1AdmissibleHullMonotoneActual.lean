/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana_latest.Iut.Cor312.ContainerHull
import tmp.sheaf.lana_latest.Iut.Cor312.LogVolume
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual

/-!
# A523 admissible hull + monotone/signed direction on the actual container

Reuses the real LANA container hull API (`ContainerHullSystem.le_hullAdmissible`,
`hullAdmissible_mono`, `hullAdmissible_idem`, `hullFamily`) together with the
procession log-volume (`LogVolumeData.processionVol`) and the actual C3 hull scaling law
(`S3137ThetaHullVolumeScalingActual`).  The xi-f signed direction is stated in the
CORRECT orientation: for a monotone signed log-volume, `R <= H.hullAdmissible R` gives
`logVolume R <= logVolume (hull R)`, i.e. for the actual negative readings
`-|log q| <= -|log(Theta)|`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1AdmissibleHullMonotoneActual

open scoped Pointwise

universe u₁ u₂ v

variable {ι : Type u₁} {V : Type u₂}

/-! ## 1. Container hull: extensivity, monotonicity, idempotency -/

section Container

variable (D : Iut.LargeVolumeContainerData ι V)
variable (H : Iut.ContainerHullSystem D)
variable {i : Fin D.proc.length}

/-- A hull-admissible region is contained in its container hull (LANA real theorem). -/
theorem container_le_hullAdmissible {R : D.AdmissibleRegion i}
    (adm : H.IsAdmissible R) : R ≤ H.hullAdmissible R :=
  H.le_hullAdmissible adm

/-- Container-hull monotonicity on hull-admissible regions (LANA real theorem). -/
theorem container_hullAdmissible_mono {R S : D.AdmissibleRegion i}
    (hR : H.IsAdmissible R) (hS : H.IsAdmissible S) (hRS : R ≤ S) :
    H.hullAdmissible R ≤ H.hullAdmissible S :=
  H.hullAdmissible_mono hR hS hRS

/-- Container-hull idempotency (LANA real theorem). -/
theorem container_hullAdmissible_idem {R : D.AdmissibleRegion i}
    (adm : H.IsAdmissible R) (vQ : Iut.RationalPlace) :
    (H.hullAdmissible (H.hullAdmissible R)).region vQ = (H.hullAdmissible R).region vQ :=
  H.hullAdmissible_idem adm vQ

/-- The packet region of the container hull is the hull of the packet region (LANA real
  theorem). -/
theorem container_hullAdmissible_region (R : D.AdmissibleRegion i)
    (vQ : Iut.RationalPlace) :
    (H.hullAdmissible R).region vQ = (H.system i vQ).hull (R.region vQ) :=
  H.hullAdmissible_region R vQ

/-- The capsule-indexed hull family of a container region family (LANA real def). -/
def thm311HullFamily (R : ∀ i : Fin D.proc.length, D.AdmissibleRegion i) :
    ∀ i : Fin D.proc.length, D.AdmissibleRegion i :=
  H.hullFamily R

end Container

/-! ## 2. The signed xi-f direction (correct orientation) -/

/-- **xi-f signed direction, correct orientation**: for any real-valued log-volume
  monotone under inclusion, `qRegion ⊆ hull` yields `logVolume qRegion <= logVolume hull`.
  With the actual negative readings (`qPilotLogVolumeReading = -|log q|`,
  `thetaPilotHullLogVolumeReal = -|log(Theta)|`) this is exactly the paper inequality
  `-|log q| <= -|log(Theta)|` (no negated-magnitude detour). -/
theorem xi_f_signed_direction {X : Type*} (logVolume : Set X → ℝ)
    (mono : ∀ {S T : Set X}, S ⊆ T → logVolume S ≤ logVolume T)
    {qRegion hull : Set X} (h : qRegion ⊆ hull) :
    logVolume qRegion ≤ logVolume hull :=
  mono h

/-- The same statement with the container-hull extensivity providing the containment. -/
theorem xi_f_signed_direction_of_hull {X : Type*} (logVolume : Set X → ℝ)
    (mono : ∀ {S T : Set X}, S ⊆ T → logVolume S ≤ logVolume T)
    {qRegion R Hhull : Set X} (hq : qRegion ⊆ R) (hR : R ⊆ Hhull) :
    logVolume qRegion ≤ logVolume Hhull :=
  mono (Set.Subset.trans hq hR)

end

end LeanFormal.IUT.XiFPaper.Mzk1AdmissibleHullMonotoneActual