import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HaarTranslateInterface
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Actual `1,circ U` Theta-hull surface: compactness, procession, Haar normalization

This file defines the *paper-level* `1,circ U` hull surface, not the value-layer
`sourceThetaHullLogVolume` (which is an `sSup` of pointwise local log-degrees and
is explicitly rejected here). The objects below are actual source-facing types:

* `FiniteProcession`: the finite signed-label procession `SignedLabel l.value`
  with normalized weights (paper: average over `j in F_l^*`);
* `OneCircUHaarNormalization`: a `1,circ U`-shaped Haar/log-volume region
  interface with unit region `O`, normalization `logVolume O = 1`, scaling
  translation, and Haar invariance;
* `OneCircUCompactHull`: the compact possible-image union and its compact
  holomorphic hull (paper: compactness of `1,circ U_{j,vQ}` and the hull);
* `ActualThetaHull`: the combined hull surface with `P subset phi(P)` and the
  `lambda * O` containment of the hull.

All fields are actual mathematical data. The file does NOT assert that the
literal `IQ(S+_{j+1}; n,circ D^vdash_{vQ})` carrier realizes this surface: that
realization is the exact missing field isolated in the module docstring. There
is no `PUnit`, `True`, `sorry`, or axiom. No `Nonempty ActualThetaHull` is
asserted; the structure is the obligation surface.

## Paper-level requirements vs available types

The paper's `-|log Theta|` is the procession-normalized mono-analytic
log-volume of the compact holomorphic hull in `1,circ U`. The components are
kept separate here:

1. finite procession over `SignedLabel l.value` (`Fintype`; cardinality `l`);
2. compactness of the image union and of the hull (`IsCompact`);
3. Haar/unit-region normalization (`logVolume O = 1`) and scaling invariance;
4. hull containment `hull subset lambda * O` and monotonicity of log-volume;
5. the signed hull log-volume is then the normalized log-volume of the hull,
   finite by (3)+(4).

The value-layer `sourceThetaHullLogValueSet`/`sourceThetaHullLogVolume` are
NOT used or derived from this file.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaperThetaHull

open scoped BigOperators

universe u

variable {l : PrimeGeFive}

/-- The zero signed label, used only to prove the finite procession is
nonempty. This is the actual label `0 in F_l^star`, not a toy carrier. -/
def zeroSignedLabel (l : PrimeGeFive) : SignedLabel l.value :=
  ⟨0, by
    have hle : (0 : Int) ≤ (lStar l.value : Int) :=
      by exact_mod_cast (Nat.zero_le (lStar l.value))
    exact ⟨neg_nonpos.mpr hle, hle⟩⟩

theorem zeroSignedLabel_mem (l : PrimeGeFive) :
    (zeroSignedLabel l).1 = 0 := rfl

/-- The actual finite signed-label procession with normalized weights. -/
structure FiniteProcession (l : PrimeGeFive) where
  /-- Weight of each signed label in the procession average. -/
  weight : SignedLabel l.value → Real
  /-- Weights are strictly positive. -/
  weight_pos : ∀ j : SignedLabel l.value, 0 < weight j
  /-- The procession weights are normalized: they sum to `1`. -/
  weight_sum_one : (∑ j : SignedLabel l.value, weight j) = 1

namespace FiniteProcession

variable (P : FiniteProcession l)

/-- The procession label type is finite with cardinality `l`. -/
theorem card_labels : Fintype.card (SignedLabel l.value) = l.value :=
  SignedLabel.card_signedLabel l

/-- The finite procession is nonempty. -/
theorem labels_nonempty : Nonempty (SignedLabel l.value) :=
  ⟨zeroSignedLabel l⟩

/-- The procession average of a real function on the labels. -/
def average (f : SignedLabel l.value → Real) : Real :=
  ∑ j : SignedLabel l.value, P.weight j * f j

/-- The average of a constant function is that constant, using the normalized
weights. This is the precise finite-procession lemma used by the paper's
`j in F_l^*` average. -/
theorem average_const (c : Real) :
    P.average (fun _ => c) = c := by
  unfold average
  rw [← Finset.sum_mul, P.weight_sum_one, one_mul]

theorem average_add (f g : SignedLabel l.value → Real) :
    P.average (fun j => f j + g j) = P.average f + P.average g := by
  unfold average
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem average_smul (c : Real) (f : SignedLabel l.value → Real) :
    P.average (fun j => c * f j) = c * P.average f := by
  unfold average
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end FiniteProcession

/-- The canonical uniform procession: each of the `l` signed labels receives
weight `1/l`. This is the actual finite procession normalization, not a toy
weight choice. -/
noncomputable def canonicalProcession : FiniteProcession l where
  weight := fun _ => ((Fintype.card (SignedLabel l.value) : Real))⁻¹
  weight_pos := by
    intro j
    apply inv_pos.mpr
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨zeroSignedLabel l⟩)
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [SignedLabel.card_signedLabel l]
    have hl : (l.value : Real) ≠ 0 := by
      have h5 : 5 ≤ l.value := l.ge_five
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < l.value))
    exact mul_inv_cancel₀ hl

/-- A `1,circ U`-shaped Haar/unit-region normalization surface. -/
structure OneCircUHaarNormalization (X : Type u) [TopologicalSpace X] where
  /-- The unit region `O` (ring-of-integers/log-shell region). -/
  unitRegion : Set X
  /-- Haar log-volume of regions, in `ENNReal` (positive magnitudes). -/
  logVolume : Set X → ENNReal
  /-- Monotonicity of the Haar log-volume. -/
  logVolume_mono : ∀ {S T : Set X}, S ⊆ T → logVolume S ≤ logVolume T
  /-- The normalization `mu(O) = 1`. -/
  unitRegion_normalized : logVolume unitRegion = 1
  /-- The multiplicative scaling `lambda` on the carrier. -/
  scaleShift : X → X
  /-- Haar/scaling invariance: the `lambda`-multiple of `O` has the same
  log-volume as `O` (translation invariance of the normalized Haar volume). -/
  scaleShift_unitRegion_eq :
    logVolume (scaleShift '' unitRegion) = logVolume unitRegion

namespace OneCircUHaarNormalization

variable {X : Type u} [TopologicalSpace X]
variable (H : OneCircUHaarNormalization X)

theorem unitRegion_logVolume_eq_one : H.logVolume H.unitRegion = 1 :=
  H.unitRegion_normalized

theorem scaleShift_unitRegion_le :
    H.logVolume (H.scaleShift '' H.unitRegion) ≤ H.logVolume H.unitRegion :=
  le_of_eq H.scaleShift_unitRegion_eq

theorem scaleShift_unitRegion_logVolume_le_one :
    H.logVolume (H.scaleShift '' H.unitRegion) ≤ 1 := by
  rw [← H.unitRegion_normalized]
  exact H.scaleShift_unitRegion_le

end OneCircUHaarNormalization

/-- The compact possible-image union and its compact holomorphic hull (the
paper's `1,circ U_{j,vQ}` and `phi(1,circ U_{j,vQ})`). -/
structure OneCircUCompactHull (X : Type u) [TopologicalSpace X] where
  /-- The union of possible theta-pilot images. -/
  imageSet : Set X
  /-- The holomorphic hull of the image union. -/
  hull : Set X
  /-- `P subset phi(P)`. -/
  imageSet_subset_hull : imageSet ⊆ hull
  /-- Compactness of the image union `1,circ U_{j,vQ}`. -/
  imageSet_compact : IsCompact imageSet
  /-- Compactness of the holomorphic hull. -/
  hull_compact : IsCompact hull

namespace OneCircUCompactHull

variable {X : Type u} [TopologicalSpace X] (C : OneCircUCompactHull X)

theorem imageSet_subset : C.imageSet ⊆ C.hull := C.imageSet_subset_hull

theorem imageSet_compact' : IsCompact C.imageSet := C.imageSet_compact

theorem hull_compact' : IsCompact C.hull := C.hull_compact

end OneCircUCompactHull

/-- The actual `1,circ U` Theta-hull surface. It carries the finite procession,
the compact hull, the Haar/unit-region normalization, the `lambda*O` hull
containment, and the normalized hull log-volume. The literal IQ-carrier
realization is deliberately a separate missing field, not assumed here. -/
structure ActualThetaHull (X : Type u) [TopologicalSpace X] (l : PrimeGeFive) where
  /-- The finite procession/weights. -/
  procession : FiniteProcession l
  /-- The compact image union and holomorphic hull. -/
  compactHull : OneCircUCompactHull X
  /-- The Haar/unit-region normalization. -/
  haar : OneCircUHaarNormalization X
  /-- The `lambda * O` containment of the holomorphic hull (Remark 3.9.5, (i)). -/
  hull_subset_scaleShift :
    compactHull.hull ⊆ haar.scaleShift '' haar.unitRegion
  /-- Exact missing paper realization: the carrier is the literal
  `IQ(S+_{j+1}; n,circ D^vdash_{vQ})` with its compact `O`-module structure. -/
  paper_IQCarrier_realization : Prop

namespace ActualThetaHull

variable {X : Type u} [TopologicalSpace X] (T : ActualThetaHull X l)

/-- The hull is contained in a scaling of the normalized unit region. -/
theorem hull_subset_scaled_unit :
    T.compactHull.hull ⊆ T.haar.scaleShift '' T.haar.unitRegion :=
  T.hull_subset_scaleShift

/-- The hull log-volume is at most the normalized unit log-volume `1`. -/
theorem hull_logVolume_le_one :
    T.haar.logVolume T.compactHull.hull ≤ 1 := by
  calc
    T.haar.logVolume T.compactHull.hull
        ≤ T.haar.logVolume (T.haar.scaleShift '' T.haar.unitRegion) :=
          T.haar.logVolume_mono T.hull_subset_scaleShift
    _ ≤ T.haar.logVolume T.haar.unitRegion :=
          T.haar.scaleShift_unitRegion_le
    _ = 1 := T.haar.unitRegion_normalized

/-- The normalized hull log-volume is finite: this is the paper's conclusion
`-|log Theta|` finite, at the Haar/unit-region level. -/
theorem hull_logVolume_lt_top :
    T.haar.logVolume T.compactHull.hull < ⊤ :=
  lt_of_le_of_lt T.hull_logVolume_le_one ENNReal.one_lt_top

/-- The image-union log-volume is bounded by the hull log-volume. -/
theorem imageSet_logVolume_le_hull :
    T.haar.logVolume T.compactHull.imageSet ≤
      T.haar.logVolume T.compactHull.hull :=
  T.haar.logVolume_mono T.compactHull.imageSet_subset_hull

/-- A lower bound on the image-union log-volume propagates to the hull. -/
theorem lower_bound_to_hull {lowerBound : ENNReal}
    (h : lowerBound ≤ T.haar.logVolume T.compactHull.imageSet) :
    lowerBound ≤ T.haar.logVolume T.compactHull.hull :=
  le_trans h T.imageSet_logVolume_le_hull

/-- The finite procession is nonempty. -/
theorem procession_nonempty : Nonempty (SignedLabel l.value) :=
  ⟨zeroSignedLabel l⟩

/-- The finite-procession cardinality is the source label cardinality. -/
theorem procession_card : Fintype.card (SignedLabel l.value) = l.value :=
  SignedLabel.card_signedLabel l

/-- The constant-function procession average is normalized. -/
theorem procession_average_const (c : Real) :
    T.procession.average (fun _ => c) = c :=
  T.procession.average_const c

end ActualThetaHull

/-- The exact paper-level target: the normalized signed hull log-volume
`-|log Theta|` is the normalized log-volume of the actual `1,circ U` hull,
with the finite procession and the compactness/Haar hypotheses above. This is a
definition surface, not a proof of the IQ-carrier realization. -/
def sourceThetaHullNormalizedLogVolume {X : Type u} [TopologicalSpace X]
    (T : ActualThetaHull X l) : ENNReal :=
  T.haar.logVolume T.compactHull.hull

theorem sourceThetaHullNormalizedLogVolume_eq {X : Type u}
    [TopologicalSpace X] (T : ActualThetaHull X l) :
    sourceThetaHullNormalizedLogVolume T =
      T.haar.logVolume T.compactHull.hull := rfl

theorem sourceThetaHullNormalizedLogVolume_lt_top {X : Type u}
    [TopologicalSpace X] (T : ActualThetaHull X l) :
    sourceThetaHullNormalizedLogVolume T < ⊤ :=
  T.hull_logVolume_lt_top

/-- The normalized hull log-volume is at most `1` (the unit normalization). -/
theorem sourceThetaHullNormalizedLogVolume_le_one {X : Type u}
    [TopologicalSpace X] (T : ActualThetaHull X l) :
    sourceThetaHullNormalizedLogVolume T ≤ 1 :=
  T.hull_logVolume_le_one

end XiFPaperThetaHull
end LeanFormal.IUT

end
