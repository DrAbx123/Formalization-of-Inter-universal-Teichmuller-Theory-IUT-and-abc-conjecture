/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.lana_latest.Iut.Cor312.HolomorphicHull
import tmp.sheaf.lana_latest.Iut.Cor312.Container
import tmp.sheaf.lana_latest.Iut.Cor312.LogVolume

/-!
# A522 hull/log-volume monotonicity layer (possibleRegion -> hull -> log-volume)

Membership chain of the xi-e containment (paper IUT III, Cor 3.12 Steps (xi-d)-(xi-f)):
* `MRRep.reg_subset_possibleRegion` (Thm 3.11 possible images; green Ref copy) gives
  `reg x ⊆ possibleRegion reg (mk x)`;
* the holomorphic hull of a region contains it (`HullSystem.subset_hull`, LANA real
  theorem) and is monotone (`HullSystem.hull_mono` / `closureOperator`);
* the container hull system of the Theta-pilot region contains the region
  (`ContainerHullSystem.le_hullAdmissible`);
* log-volume monotonicity: LANA's `LogVolumeData` records `packetVol` as an opaque
  field with normalization/combination laws only.  There is NO `packetVol_mono`,
  `globalVol_mono` or `processionVol_mono` lemma in the package: this is the remaining
  monotonicity GAP of the route.  It is flagged here as the explicit named field
  `packetVol_mono` of `LogVolumeMonotoneInput`; the `globalVol`/`processionVol`
  monotone consequences are then proved from it under the (also named, until the
  `finsum` monotone lemma is applied) `globalVol_mono` hypothesis.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeMonotoneActual

open scoped Pointwise

universe u₁ u₂ v

variable {ι : Type u₁} {V : Type u₂}

/-! ## 1. Hull monotonicity (reused real LANA theorems) -/

section Hull

variable (H : Iut.HullSystem)

/-- A region is contained in its holomorphic hull (LANA real theorem). -/
theorem hull_subset (U : Set H.packet.Total) (hU : U ∈ H.Admissible) :
    U ⊆ H.hull U :=
  H.subset_hull hU

/-- The holomorphic hull is the least hull region containing the region (LANA real
  theorem `hull_le`). -/
theorem hull_le_region (U : Set H.packet.Total) (hU : U ∈ H.Admissible)
    {R : Set H.packet.Total} (hR : R ∈ H.HullRegions) (hUR : U ⊆ R) :
    H.hull U ⊆ R :=
  H.hull_le hU hR hUR

/-- Hull monotonicity (LANA real theorem). -/
theorem hull_mono_region {U U' : Set H.packet.Total} (hU : U ∈ H.Admissible)
    (hU' : U' ∈ H.Admissible) (hUU' : U ⊆ U') :
    H.hull U ⊆ H.hull U' :=
  H.hull_mono hU hU' hUU'

/-- The hull of an admissible region is admissible (LANA real theorem). -/
theorem hull_admissible (U : Set H.packet.Total) (hU : U ∈ H.Admissible) :
    H.hull U ∈ H.Admissible :=
  H.hull_admissible hU

end Hull

/-! ## 2. The container hull and its monotonicity -/

section ContainerHull

variable (H : Iut.ContainerHullSystem (D := (default : Iut.LargeVolumeContainerData ι V)))

/-- An admissible region is contained in its container hull (LANA real theorem). -/
theorem container_le_hullAdmissible {R : (default : Iut.LargeVolumeContainerData ι V).AdmissibleRegion}
    (hR : H.IsAdmissible R) : R ≤ H.hullAdmissible R := by
  -- `ContainerHullSystem.le_hullAdmissible` (LANA real theorem).
  exact H.le_hullAdmissible hR

end ContainerHull

/-! ## 3. Log-volume monotonicity: the named gap and its consequences -/

section LogVolume

variable (D : Iut.LargeVolumeContainerData ι V)

/-- **Named monotonicity gap**: the packet log-volume is monotone under inclusion of
  packet regions.  LANA's `LogVolumeData` does not provide this lemma (it is an opaque
  field with normalization laws only); it must be proved from `componentVol` and the
  combination law `packetVol_product`. -/
def PacketVolMonotone (vol : Iut.LogVolumeData D) : Prop :=
  ∀ (i : Fin D.proc.length) (vQ : Iut.RationalPlace)
    {R S : Set (D.packet i vQ).Total}, R ⊆ S → vol.packetVol i vQ R ≤ vol.packetVol i vQ S

/-- **Named global monotonicity input**: the global log-volume is monotone.  It follows
  from `PacketVolMonotone` once the `finsum` monotone lemma is applied over the finite
  supports (`finite_support_packetVol`); that derivation is the remaining package
  monotonicity link. -/
def GlobalVolMonotone (vol : Iut.LogVolumeData D) : Prop :=
  ∀ {i : Fin D.proc.length} {R S : D.AdmissibleRegion i}, R ≤ S →
    vol.globalVol R ≤ vol.globalVol S

/-- **Procession log-volume is monotone** from the global monotonicity input (real
  proof: average of componentwise monotone global log-volumes). -/
theorem processionVol_mono (vol : Iut.LogVolumeData D)
    (h : GlobalVolMonotone D vol) {R S : ∀ i : Fin D.proc.length, D.AdmissibleRegion i}
    (hRS : ∀ i, R i ≤ S i) :
    vol.processionVol R ≤ vol.processionVol S := by
  unfold Iut.LogVolumeData.processionVol
  have hlen : (0 : ℝ) ≤ (D.proc.length : ℝ) := by positivity
  have hsum : (∑ i, vol.globalVol (R i)) ≤ ∑ i, vol.globalVol (S i) :=
    Finset.sum_le_sum fun i _ => h (hRS i)
  exact div_le_div_of_nonneg_right hsum hlen

/-- The Theta-pilot hull log-volume is the procession volume of the hull family;
  monotone in the pilot region via `processionVol_mono`. -/
theorem thetaHull_processionVol_mono (vol : Iut.LogVolumeData D)
    (h : GlobalVolMonotone D vol)
    {R S : Iut.RHSData D} (hRS : ∀ i, (R.thetaHull i) ≤ (S.thetaHull i) := by
      intro i; exact le_rfl) :
    vol.processionVol R.thetaHull ≤ vol.processionVol S.thetaHull :=
  processionVol_mono D vol h hRS

end LogVolume

end

end LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeMonotoneActual