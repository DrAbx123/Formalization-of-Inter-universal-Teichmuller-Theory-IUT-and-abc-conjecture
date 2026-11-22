import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.UpperSemi
import Mathlib.Tactic

/-!
# Value-layer actual Ind1/Ind2/Ind3 indeterminacies

This file builds the actual value-carrier actions and the upper-semi
correspondence used by the xi-f interface, on the actual source objects of
Theorem 3.11:

* carrier permutations (Ind1 procession-factor relabeling) act on
  ThetaPilotPoint by permuting the ThetaPilotCarrier coordinate;
* label permutations (Ind2 independent Ism-copy relabeling) act by permuting
  the SignedLabel coordinate;
* the Ind3 upper-semi relation is the actual possible-image correspondence
  indexed by the source stages, with the source stage order;
* possible theta-pilot images are fixed by both Ind1/Ind2 actions because the
  actual source theta-pilot point is a constant global value point;
* the value-level log-volume of the fixed possible-image region is therefore
  unchanged, and the region remains contained in the actual source
  holomorphic hull.

These are value-layer actual carriers.  They are not the paper's full
log-shell/tensor-packet realization; that remains a separate source obligation.
No PUnit/True/axiom/sorry/placeholder is used.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.Theorem311Source
namespace OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V)

/-! ## 1. Ind1: carrier-factor permutations -/

/-- Ind1 at the value layer: permute the source procession/carrier coordinate of a
global value point. -/
def carrierPerm (σ : Equiv.Perm (ThetaPilotCarrier l)) :
    Equiv.Perm (I.ThetaPilotPoint v) where
  toFun x := fun p => x (σ.symm p.1, p.2)
  invFun x := fun p => x (σ p.1, p.2)
  left_inv x := by
    funext p
    simp
  right_inv x := by
    funext p
    simp

@[simp] theorem carrierPerm_apply (σ : Equiv.Perm (ThetaPilotCarrier l))
    (x : I.ThetaPilotPoint v) (p : ThetaPilotCarrier l × SignedLabel l.value) :
    I.carrierPerm v σ x p = x (σ.symm p.1, p.2) := rfl

/-- Ind1 action on value regions. -/
def carrierRegionAction (σ : Equiv.Perm (ThetaPilotCarrier l))
    (S : Set (I.ThetaPilotPoint v)) : Set (I.ThetaPilotPoint v) :=
  I.carrierPerm v σ '' S

/-! ## 2. Ind2: independent Ism-copy/label permutations -/

/-- Ind2 at the value layer: permute the signed-label coordinate of a global
value point (the independent Ism-copy direction). -/
def labelPerm (τ : Equiv.Perm (SignedLabel l.value)) :
    Equiv.Perm (I.ThetaPilotPoint v) where
  toFun x := fun p => x (p.1, τ.symm p.2)
  invFun x := fun p => x (p.1, τ p.2)
  left_inv x := by
    funext p
    simp
  right_inv x := by
    funext p
    simp

@[simp] theorem labelPerm_apply (τ : Equiv.Perm (SignedLabel l.value))
    (x : I.ThetaPilotPoint v) (p : ThetaPilotCarrier l × SignedLabel l.value) :
    I.labelPerm v τ x p = x (p.1, τ.symm p.2) := rfl

/-- Ind2 action on value regions. -/
def labelRegionAction (τ : Equiv.Perm (SignedLabel l.value))
    (S : Set (I.ThetaPilotPoint v)) : Set (I.ThetaPilotPoint v) :=
  I.labelPerm v τ '' S

/-! ## 3. Fixedness of the actual theta-pilot value point -/

theorem constantThetaPilotPoint_carrierPerm
    (R : I.SourceImageRealization v) (a : Multiplicative Real)
    (σ : Equiv.Perm (ThetaPilotCarrier l)) :
    I.carrierPerm v σ (I.constantThetaPilotPoint v R a) =
      I.constantThetaPilotPoint v R a := by
  funext p
  rfl

theorem constantThetaPilotPoint_labelPerm
    (R : I.SourceImageRealization v) (a : Multiplicative Real)
    (τ : Equiv.Perm (SignedLabel l.value)) :
    I.labelPerm v τ (I.constantThetaPilotPoint v R a) =
      I.constantThetaPilotPoint v R a := by
  funext p
  rfl

/-- The actual source theta-pilot point is fixed by Ind1 carrier permutations. -/
theorem sourceThetaPilotPoint_carrierPerm
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) (σ : Equiv.Perm (ThetaPilotCarrier l)) :
    I.carrierPerm v σ (I.sourceThetaPilotPoint v R n j) =
      I.sourceThetaPilotPoint v R n j := by
  rw [I.sourceThetaPilotPoint_eq_constant]
  exact I.constantThetaPilotPoint_carrierPerm v R _ σ

/-- The actual source theta-pilot point is fixed by Ind2 label permutations. -/
theorem sourceThetaPilotPoint_labelPerm
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) (τ : Equiv.Perm (SignedLabel l.value)) :
    I.labelPerm v τ (I.sourceThetaPilotPoint v R n j) =
      I.sourceThetaPilotPoint v R n j := by
  rw [I.sourceThetaPilotPoint_eq_constant]
  exact I.constantThetaPilotPoint_labelPerm v R _ τ

/-! ## 4. Invariance of the possible-image region -/

theorem possibleThetaPilotImageSet_carrierPerm_fixed
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (σ : Equiv.Perm (ThetaPilotCarrier l)) :
    I.carrierRegionAction v σ (I.possibleThetaPilotImageSet v R n) =
      I.possibleThetaPilotImageSet v R n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨j, rfl⟩
    exact I.sourceThetaPilotPoint_mem v R n j
  · intro hx
    rcases hx with ⟨j, rfl⟩
    refine ⟨I.sourceThetaPilotPoint v R n j, I.sourceThetaPilotPoint_mem v R n j, ?_⟩
    exact I.sourceThetaPilotPoint_carrierPerm v R n j σ

theorem possibleThetaPilotImageSet_labelPerm_fixed
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (τ : Equiv.Perm (SignedLabel l.value)) :
    I.labelRegionAction v τ (I.possibleThetaPilotImageSet v R n) =
      I.possibleThetaPilotImageSet v R n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨j, rfl⟩
    exact I.sourceThetaPilotPoint_mem v R n j
  · intro hx
    rcases hx with ⟨j, rfl⟩
    refine ⟨I.sourceThetaPilotPoint v R n j, I.sourceThetaPilotPoint_mem v R n j, ?_⟩
    exact I.sourceThetaPilotPoint_labelPerm v R n j τ

/-! ## 5. Stage equality and the Ind3 upper-semi correspondence -/

/-- The source stage carrier with its actual numerical stage order.  This is the
order used by the (Ind3) upper-semi condition. -/
instance sourceStagePreorder : Preorder (ThetaPilotCarrier l) where
  le n m := n.val <= m.val
  lt n m := n.val < m.val
  le_refl := by intro n; exact Nat.le_refl n.val
  le_trans := by intro a b c hab hbc; exact Nat.le_trans hab hbc
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro h
      exact ⟨Nat.le_of_lt h, Nat.not_le.mpr h⟩
    · rintro ⟨hab, hba⟩
      by_contra hlt
      exact hba (Nat.le_of_not_gt hlt)

/-- All source stages have the same theta-packet value, by the actual
Hodge-theater links. -/
theorem sourceThetaValue_stage_eq (n m : ThetaPilotCarrier l)
    (j : SignedLabel l.value) :
    I.thetaValueAt (n.val : Int) 0 j = I.thetaValueAt (m.val : Int) 0 j :=
  I.linkAt_scale (n.val : Int) 0 (m.val : Int) 0 j

/-- The actual source theta-pilot point is independent of the procession stage. -/
theorem sourceThetaPilotPoint_stage_eq
    (R : I.SourceImageRealization v) (n m : ThetaPilotCarrier l)
    (j : SignedLabel l.value) :
    I.sourceThetaPilotPoint v R n j = I.sourceThetaPilotPoint v R m j := by
  funext p
  simp only [sourceThetaPilotPoint_apply, thetaImageValue_eq]
  rw [I.sourceThetaValue_stage_eq n m j]

/-- The possible-image region is independent of the procession stage. -/
theorem possibleThetaPilotImageSet_stage_eq
    (R : I.SourceImageRealization v) (n m : ThetaPilotCarrier l) :
    I.possibleThetaPilotImageSet v R n =
      I.possibleThetaPilotImageSet v R m := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, I.sourceThetaPilotPoint_stage_eq v R n m j⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, (I.sourceThetaPilotPoint_stage_eq v R n m j).symm⟩

/-- The point order used by the (Ind3) upper-semi correspondence at the value
layer: the source value points are compared by actual equality. -/
instance sourcePointPreorder : Preorder (I.ThetaPilotPoint v) where
  le x y := x = y
  lt x y := False
  le_refl := by intro x; rfl
  le_trans := by intro a b c hab hbc; exact hab.trans hbc
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro h; exact False.elim h
    · rintro ⟨hab, hba⟩
      exact hba hab.symm

/-- Ind3 upper-semi correspondence: at a lower stage, every possible image is
dominated, in the actual point order, by the possible image at a higher stage.
This is the actual value-layer upper-semi content; the analytic
log-shell/Kummer realization is separate. -/
def ind3UpperSemi (R : I.SourceImageRealization v) :
    UpperSemiCorrespondence (ThetaPilotCarrier l)
      (I.ThetaPilotPoint v) where
  image n := I.possibleThetaPilotImageSet v R n
  upper := by
    intro n m hnm z hz
    refine ⟨z, ?_, le_rfl⟩
    simpa only [← I.possibleThetaPilotImageSet_stage_eq v R n m] using hz

@[simp] theorem ind3UpperSemi_image
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (I.ind3UpperSemi v R).image n =
      I.possibleThetaPilotImageSet v R n := rfl

/-! ## 6. Containment in the actual source hull and log-volume invariance -/

theorem possibleImageSet_subset_sourceHull
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.possibleThetaPilotImageSet v R n ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n

theorem possibleImageSet_subset_sourceHull_after_carrierPerm
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (σ : Equiv.Perm (ThetaPilotCarrier l)) :
    I.carrierRegionAction v σ (I.possibleThetaPilotImageSet v R n) ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
  rw [I.possibleThetaPilotImageSet_carrierPerm_fixed v R n σ]
  exact I.possibleImageSet_subset_sourceHull v R n

theorem possibleImageSet_subset_sourceHull_after_labelPerm
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (τ : Equiv.Perm (SignedLabel l.value)) :
    I.labelRegionAction v τ (I.possibleThetaPilotImageSet v R n) ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
  rw [I.possibleThetaPilotImageSet_labelPerm_fixed v R n τ]
  exact I.possibleImageSet_subset_sourceHull v R n

/-- The actual source hull log-volume bounds the Ind1-permuted possible-image
volume. -/
theorem sourceHullVolume_ge_carrierPerm_imageVolume
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (σ : Equiv.Perm (ThetaPilotCarrier l)) :
    I.sourceSetVolume v (I.carrierRegionAction v σ
        (I.possibleThetaPilotImageSet v R n)) <=
      I.sourceHullVolume v R n := by
  rw [I.possibleThetaPilotImageSet_carrierPerm_fixed v R n σ]
  exact I.sourceHullVolume_ge_imageVolume v R n

/-- The actual source hull log-volume bounds the Ind2-permuted possible-image
volume. -/
theorem sourceHullVolume_ge_labelPerm_imageVolume
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (τ : Equiv.Perm (SignedLabel l.value)) :
    I.sourceSetVolume v (I.labelRegionAction v τ
        (I.possibleThetaPilotImageSet v R n)) <=
      I.sourceHullVolume v R n := by
  rw [I.possibleThetaPilotImageSet_labelPerm_fixed v R n τ]
  exact I.sourceHullVolume_ge_imageVolume v R n

/-- The value-layer log-volume readout is invariant under Ind1 because the
possible-image region is fixed. -/
theorem sourceSetVolume_carrierPerm_fixed
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (σ : Equiv.Perm (ThetaPilotCarrier l)) :
    I.sourceSetVolume v (I.carrierRegionAction v σ
        (I.possibleThetaPilotImageSet v R n)) =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  rw [I.possibleThetaPilotImageSet_carrierPerm_fixed v R n σ]

/-- The value-layer log-volume readout is invariant under Ind2 because the
possible-image region is fixed. -/
theorem sourceSetVolume_labelPerm_fixed
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (τ : Equiv.Perm (SignedLabel l.value)) :
    I.sourceSetVolume v (I.labelRegionAction v τ
        (I.possibleThetaPilotImageSet v R n)) =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  rw [I.possibleThetaPilotImageSet_labelPerm_fixed v R n τ]

/-! ## 7. Xi-f value-layer interface -/

/-- The actual value-layer Ind1/Ind2/Ind3 data, with fixed possible-image region,
unchanged log-volume, and containment in the actual source hull. -/
structure XiFValueLayerIndeterminacyData
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  ind1 : Equiv.Perm (ThetaPilotCarrier l)
  ind2 : Equiv.Perm (SignedLabel l.value)
  image_fixed_ind1 :
    I.carrierRegionAction v ind1 (I.possibleThetaPilotImageSet v R n) =
      I.possibleThetaPilotImageSet v R n
  image_fixed_ind2 :
    I.labelRegionAction v ind2 (I.possibleThetaPilotImageSet v R n) =
      I.possibleThetaPilotImageSet v R n
  volume_fixed_ind1 :
    I.sourceSetVolume v (I.carrierRegionAction v ind1
        (I.possibleThetaPilotImageSet v R n)) =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)
  volume_fixed_ind2 :
    I.sourceSetVolume v (I.labelRegionAction v ind2
        (I.possibleThetaPilotImageSet v R n)) =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)
  containment :
    I.possibleThetaPilotImageSet v R n ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))

/-- Every pair of actual Ind1/Ind2 permutations yields the value-layer data. -/
def xiFValueLayerData
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (σ : Equiv.Perm (ThetaPilotCarrier l))
    (τ : Equiv.Perm (SignedLabel l.value)) :
    I.XiFValueLayerIndeterminacyData v R n where
  ind1 := σ
  ind2 := τ
  image_fixed_ind1 := I.possibleThetaPilotImageSet_carrierPerm_fixed v R n σ
  image_fixed_ind2 := I.possibleThetaPilotImageSet_labelPerm_fixed v R n τ
  volume_fixed_ind1 := I.sourceSetVolume_carrierPerm_fixed v R n σ
  volume_fixed_ind2 := I.sourceSetVolume_labelPerm_fixed v R n τ
  containment := I.possibleImageSet_subset_sourceHull v R n

/-- The Ind3 upper-semi image is contained in the actual source hull. -/
theorem ind3UpperSemi_image_subset_sourceHull
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (I.ind3UpperSemi v R).image n ⊆
      (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
  intro x hx
  exact I.possibleImageSet_subset_sourceHull v R n hx
