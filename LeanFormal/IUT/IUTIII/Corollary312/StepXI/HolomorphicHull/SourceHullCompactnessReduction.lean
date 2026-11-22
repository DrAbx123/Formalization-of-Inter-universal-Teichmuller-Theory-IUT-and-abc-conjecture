import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.Audit.Status

/-!
  # The paper-level compactness interface of the Corollary 3.12 hull bound

  The value-monoid realization of the source holomorphic hull
  (`SourceImageHull.lean`, `SourceImageHullVolume.lean`) does not supply the bound that
  the proof of IUT III Corollary 3.12 obtains from the compactness of the
  `1,◦U_{j,vQ}` together with the definition of the log-volume: under the pointwise
  degree faithfulness of the source realization the value-realized hull log-degree is
  unbounded above (`sourceHolomorphicHull_logDegree_unbounded`), and the hull volume is
  `⊤` (`sourceHullVolume_eq_top_of_degreeFaithful`).

  This module isolates, as a data interface, exactly the paper-level ambient input that
  the paper's argument uses, without pretending that it is derived:

  * an ambient carrier (the role of `IQ(S±_{j+1}; n,◦D^vdash_{vQ})`);
  * the image union of the theta-pilot object and the hull containing it (the role of
    `n,◦U_{vQ}` and `φ(n,◦U_{vQ})`), i.e. the `P ⊆ φ(P)` property;
  * a log-volume functional on regions, monotone under inclusion;
  * a unit region (the role of the ring-of-integers/log-shell region `O`), whose
    normalized log-volume is finite (what the compactness of `1,◦U_{j,vQ}` and the
    definition of the log-volume provide in the paper);
  * the multiplicative translation `scaleShift` by a fixed scaling `λ`, with the
    property that the hull is contained in the `λ`-multiple of the unit region and that
    the log-volume of the `λ`-multiple is at most that of the unit region (the Haar
    translation invariance that makes `λ·O` normalize to the same log-volume as `O`).

  From that data, finiteness of the hull log-volume and propagation of any lower bound
  from the image union to the hull are proved.  The corresponding value-level reduction,
  where the `λ`-translation acts additively on log-degrees instead of preserving a Haar
  volume, is `sourceHullVolume_lt_top_of_scaledRegionImage`.

  A one-point witness shows the interface is satisfiable (it is not contradictory,
  unlike `LiteralArithmeticHullInterface`); the witness is a consistency check on the
  data interface only, not a model of the paper's carrier.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

universe u

/-- The paper-level ambient data used by the finiteness argument of IUT III
Corollary 3.12.  The intended carrier is the inductive-system carrier
`IQ(S±_{j+1}; n,◦D^vdash_{vQ})`; no field is a consequence of the hull operation, and
none is claimed to follow from `OriginalInput`. -/
structure IQHullLogVolumeInterface (X : Type u) where
  /-- The image union of the theta-pilot object inside the ambient carrier (the role
  of `n,◦U_{vQ}`). -/
  imageSet : Set X
  /-- The holomorphic hull of the image union (the role of `φ(n,◦U_{vQ})`). -/
  hull : Set X
  /-- `P ⊆ φ(P)`: the image union is contained in its hull (Remark 3.9.5, (ii)). -/
  imageSet_subset_hull : imageSet ⊆ hull
  /-- The log-volume functional on regions of the carrier (the role of the Haar
  log-volume, an `ENNReal`-valued measure of regions). -/
  logVolume : Set X → ENNReal
  /-- Log-volume is monotone under inclusion. -/
  logVolume_mono : ∀ {S T : Set X}, S ⊆ T → logVolume S ≤ logVolume T
  /-- The unit region of the carrier (the role of the ring-of-integers/log-shell
  region `O_{vQ}`, whose log-volume is normalized). -/
  unitRegion : Set X
  /-- The multiplicative translation by the scaling `λ` of the `λ·O` regions of
  Remark 3.9.5, (i). -/
  scaleShift : X → X
  /-- The input obtained in the paper from the compactness of the `1,◦U_{j,vQ}`: the
  hull is contained in the `λ`-multiple of the unit region. -/
  hull_subset_scaleShift : hull ⊆ scaleShift '' unitRegion
  /-- The normalization half of the definition of the log-volume: the unit region has
  finite normalized log-volume. -/
  unitRegion_logVolume_lt_top : logVolume unitRegion < ⊤
  /-- Haar translation invariance of the log-volume: the `λ`-multiple of the unit
  region carries at most the log-volume of the unit region, so `λ·O` is normalized by
  the same log-volume as `O`. -/
  scaleShift_unitRegion_logVolume_le :
    logVolume (scaleShift '' unitRegion) ≤ logVolume unitRegion

namespace IQHullLogVolumeInterface

variable {X : Type u} (W : IQHullLogVolumeInterface X)

/-- The normalized lower bound propagates from the image union to the hull. -/
theorem imageSet_logVolume_le_hull :
    W.logVolume W.imageSet ≤ W.logVolume W.hull :=
  W.logVolume_mono W.imageSet_subset_hull

/-- **Conditional finiteness of the hull log-volume** from the paper-level ambient
data: the hull lies in the `λ`-multiple of the unit region, whose normalized log-volume
is finite. -/
theorem hull_logVolume_lt_top : W.logVolume W.hull < ⊤ :=
  lt_of_le_of_lt
    (W.logVolume_mono W.hull_subset_scaleShift)
    (lt_of_le_of_lt W.scaleShift_unitRegion_logVolume_le
      W.unitRegion_logVolume_lt_top)

/-- The two conclusions of the paper's argument, from the same ambient data: any lower
bound on the image-union log-volume is also a lower bound on the hull log-volume, and
the hull log-volume is finite. -/
theorem lower_bound_and_finiteness {lowerBound : ENNReal}
    (h : lowerBound ≤ W.logVolume W.imageSet) :
    lowerBound ≤ W.logVolume W.hull ∧ W.logVolume W.hull < ⊤ :=
  ⟨le_trans h W.imageSet_logVolume_le_hull, W.hull_logVolume_lt_top⟩

/-- A one-point consistency witness for `IQHullLogVolumeInterface`: the interface is
satisfiable, so its hypotheses are not self-defeating.  This is a check on the data
interface only, not a model of the paper's carrier. -/
noncomputable def singletonRealWitness : IQHullLogVolumeInterface ℝ := by
  classical
  exact
    { imageSet := {0}
      hull := {0}
      imageSet_subset_hull := by intro x hx; exact hx
      logVolume := fun S => if S.Nonempty then 1 else 0
      logVolume_mono := by
        intro S T hST
        change (if S.Nonempty then 1 else 0) ≤ (if T.Nonempty then 1 else 0)
        by_cases h : S.Nonempty
        · have hT : T.Nonempty := by
            rcases h with ⟨x, hx⟩
            exact ⟨x, hST hx⟩
          simp [h, hT]
        · rw [if_neg h]
          exact zero_le
      unitRegion := {0}
      scaleShift := fun x => x
      hull_subset_scaleShift := by
        intro x hx
        exact ⟨x, hx, rfl⟩
      unitRegion_logVolume_lt_top := by
        change (if ({0} : Set ℝ).Nonempty then 1 else 0) < ⊤
        rw [if_pos (show ({0} : Set ℝ).Nonempty from ⟨0, rfl⟩)]
        exact ENNReal.one_lt_top
      scaleShift_unitRegion_logVolume_le := by simp }

end IQHullLogVolumeInterface

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the paper-level compactness interface of the Corollary 3.12 hull
log-volume bound. -/
def iqHullLogVolume : Obligation :=
  { id := "IUT-III.corollary-3.12-iq-hull-log-volume-interface"
    source :=
      "IUT III, Corollary 3.12 proof (compactness of the 1,circ U_{j,vQ} and the " ++
        "definition of the log-volume); Remark 3.9.5, (i), (ii)"
    status := VerificationStatus.interface
    note :=
      "The paper-level ambient data needed by the finiteness argument of " ++
        "Corollary 3.12 is named as the data interface IQHullLogVolumeInterface: an " ++
        "ambient hull carrier, the image-union containment P ⊆ φ(P), a monotone " ++
        "log-volume, a unit region with finite normalized log-volume, and Haar " ++
        "invariance under the lambda-translation, with the hull contained in the " ++
        "lambda-multiple of the unit region. Finiteness of the hull log-volume and " ++
        "propagation of the normalized lower bound from the image union to the hull " ++
        "are proved from that data, and a one-point witness shows the interface is " ++
        "satisfiable. NOT proved: that the interface is realized by the actual " ++
        "IQ(S±_{j+1}; n,circ D^vdash_{vQ}) carrier; under pointwise degree " ++
        "faithfulness the value-monoid realization is in fact unbounded " ++
        "(sourceHullVolume_eq_top_of_degreeFaithful), so this input is genuinely " ++
        "additional data."
    dependsOn :=
      [ "IUT-III.corollary-3.12-source-image-hull-volume" ] }

end LeanFormal.IUT.Audit
