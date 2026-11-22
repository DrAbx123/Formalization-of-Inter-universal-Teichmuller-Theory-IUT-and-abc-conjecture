/-
# QRegionCarrier: statement layer for the true-`q` carrier specification (B3)

Probe file (run `hull-presentation-routes-20261016`, agent Noether), read-only with
respect to every other file.  Spec anchor: `logs/coordination/hunit-epsilon-transfer-20261016.md`
section 17 (four needed objects; corpus anchors III:10843-10898 and III:1042-1058).
Reduced English statement carried over from that section:

  "Construct a value/geometry-layer carrier `QRegionCarrier` for the region of the
  q-pilot representation on `1,circ U_Q` (III:10847-10848) together with a
  Theta x mu-LGP-link-style identification to the Theta-side `1,circ U`, satisfying
  (i) log-volume = `-|log q|`; (ii) log-shell containment `lambda . O` is contained
  in the region (III:10381-10414); (iii) the comparison `-|log q| <= -|log Theta|`
  derivable from the link identification (III:10880-10898).  In-tree objects
  currently cover only the value-measure layer; missing structures = (1)
  region+unit/O-module geometry, (2) LGP-link identification."

This file is the statement layer only: the four slots with their containment laws, a
satisfiability witness, a separation witness (the slots do not determine each other),
and the supply inventory.  No geometry is built and nothing here is claimed for the
paper's carrier.

In-tree supply (references only, not imported):
* slot (2) shadow and the `lambda . O` scaling: `scaleAction` / `scaledRegionImage`
  (`SourceImageHull.lean:263-289`), `SourceUnitRegionHaarData.scaling` and its field
  `hull_subset_scaledRegionImage` (`IQCarrierHaarData.lean:159-176`).
* consumer-facing value slots: `IQHullLogVolumeInterface.unitRegion` / `scaleShift` /
  `hull_subset_scaleShift` (`SourceHullCompactnessReduction.lean:52-81`), finiteness
  `hull_logVolume_lt_top` (:95).
* slot (4): `sourcePointVolume` / `sourceSetVolume` (`SourceImageHullVolume.lean:107/188`),
  `sourceHullVolume` (:193).
* O-module layer and `1,circ U` compactness as named premises: `SourceOModuleLayer` /
  `SourceOneCircUCompactness` / `sourceOModuleCompactness_haarData`
  (`OModuleCompactnessLayer.lean:149/165/193`); the lambda-normalization bridge
  `sourceOModuleCompactness_hullVolume_lt_top` (:227).
* gap cards: `CardHullRealGeometryGapCards` K1-K4; signed wrapper (section 16).

Counterexample risk (needs-verification; nothing refuted here): the single-point
regime of the finite model supplies none of the slots (1)-(3), so any consumer that
needs them stays conditional; the value-measure slot (4) is compatible with both the
singleton and the non-singleton regimes, so it cannot separate them.
-/

import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanFormal.IUT

namespace QRegionCarrierLayer

variable {X : Type*}

/-- The four slots of the `QRegionCarrier` specification (section 17 of the
hunit-epsilon-transfer log), as a statement layer: no geometry, no realization. -/
structure QRegionCarrierSpec (X : Type*) where
  /-- (1) the region of the q-pilot representation on `1,circ U_Q`; no in-tree
  counterpart. -/
  region : Set X
  /-- the base point `1` of the region. -/
  basePoint : X
  /-- the base point lies in the region. -/
  basePoint_mem : basePoint ∈ region
  /-- (2) the `O`-module unit on `1,circ U` (the `lambda . O` normalization slot);
  value-level shadow only. -/
  moduleUnit : X
  /-- the module unit lies in the region. -/
  moduleUnit_mem : moduleUnit ∈ region
  /-- (3) the log-shell region (read as the `lambda . O` region of the containment
  `lambda . O` is contained in the region). -/
  logShell : Set X
  /-- the log-shell containment slot (clause (ii) of the reduced statement). -/
  logShell_subset_region : logShell ⊆ region
  /-- (3) the Theta x mu-LGP-link identification slot; no in-tree counterpart. -/
  lgpLink : X → X
  /-- (4) the log-volume functional on regions; in-tree counterpart:
  `sourceSetVolume` (`SourceImageHullVolume.lean:188`). -/
  logVolume : Set X → ENNReal
  /-- monotonicity of the log-volume under inclusion. -/
  logVolume_mono : ∀ {S T : Set X}, S ⊆ T → logVolume S ≤ logVolume T

/-- The log-shell slot is monotone for the log-volume: clause (ii) plus slot (4). -/
theorem qRegionCarrierSpec_logShell_volume_le_region (S : QRegionCarrierSpec X) :
    S.logVolume S.logShell ≤ S.logVolume S.region :=
  S.logVolume_mono S.logShell_subset_region

/-- Satisfiability witness on the one-point carrier: the specification is not
contradictory (contrast `LiteralArithmeticHullInterface`, which is). -/
def unitQRegionCarrierSpec : QRegionCarrierSpec Unit where
  region := Set.univ
  basePoint := ()
  basePoint_mem := Set.mem_univ _
  moduleUnit := ()
  moduleUnit_mem := Set.mem_univ _
  logShell := Set.univ
  logShell_subset_region := subset_rfl
  lgpLink := id
  logVolume := fun _ => 0
  logVolume_mono := fun _ => le_rfl

/-- A second witness with the same log-volume and link slots but the empty log-shell:
the slots do not determine each other. -/
def emptyShellQRegionCarrierSpec : QRegionCarrierSpec Unit where
  region := Set.univ
  basePoint := ()
  basePoint_mem := Set.mem_univ _
  moduleUnit := ()
  moduleUnit_mem := Set.mem_univ _
  logShell := ∅
  logShell_subset_region := Set.empty_subset _
  lgpLink := id
  logVolume := fun _ => 0
  logVolume_mono := fun _ => le_rfl

/-- Separation of the slots: the log-shell slot is not determined by the log-volume
and link slots. -/
theorem qRegionCarrierSpec_slots_not_determined :
    unitQRegionCarrierSpec.logVolume = emptyShellQRegionCarrierSpec.logVolume ∧
    unitQRegionCarrierSpec.lgpLink = emptyShellQRegionCarrierSpec.lgpLink ∧
    unitQRegionCarrierSpec.logShell ≠ emptyShellQRegionCarrierSpec.logShell := by
  refine ⟨rfl, rfl, fun h => ?_⟩
  have h' : (Set.univ : Set Unit) = (∅ : Set Unit) := h
  have hmem : () ∈ (∅ : Set Unit) := by
    rw [← h']
    exact Set.mem_univ ()
  exact Set.notMem_empty () hmem

end QRegionCarrierLayer

end LeanFormal.IUT
