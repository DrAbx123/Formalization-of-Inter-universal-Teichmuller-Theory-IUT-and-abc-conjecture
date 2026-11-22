import tmp.sheaf.xif.paper.OrigXiFPaperSignedHullActual
import Mathlib.Tactic

/-!
# S1904: the procession-normalization bridge on the actual theta hull and the
# actual determinant -- what is provable, what is not, and the exact first
# missing

Layer: **O** (original-text Theta-link / xi-f, procession normalization).
Consumer: the field `hull_logVolume_eq_procession` of
`OrigXiFPaperSignedHullData` (`tmp/sheaf/xif/paper/OrigXiFPaperSignedHullActual.lean`),
i.e. the S1880 D third field

  thetaHull.haar.logVolume thetaHull.compactHull.hull
    = ENNReal.ofReal determinant.procession.average

(IUT III, Step (xi-d)/(xi-e): the procession-normalized mono-analytic
log-volume of the compact holomorphic hull `1,circ U`).  S1880 carries this as
an unproved field (`s1880_signedHullDatum_bridge`); this file attacks it
directly on the two actual objects of the D structure:

* theta side (S1902): `ActualThetaHull` (`tmp/sheaf/xif/paper/ThetaHullActual.lean`)
  -- actual compact `1,circ U` image union and holomorphic hull, the
  `OneCircUHaarNormalization` Haar/unit-region surface, the `lambda * O`
  containment;
* determinant side (S1903): `SignedHullLogActual`
  (`tmp/sheaf/xif/paper/SignedHullLogActual.lean`) -- the actual positive
  log-shell packet, the unit reference packet, the determinant tensor power,
  and the actual procession `WeightedValues` whose average is the paper's
  procession normalization.

## Result of this file

`0.` The two readouts are named (`s1904HullLogVolume`, `s1904ProcessionAverage`)
and the bridge is the proposition `S1904ProcessionBridge T P`.

`1.` [PROVED] **The two-sided content of the bridge.**  For *every* actual
theta hull `T` and every actual determinant `P`:

    S1904ProcessionBridge T P  ->  0 <= average P  and  average P <= 1,

with the lower bound holding unconditionally (`s1904_processionAverage_nonneg`)
and the upper bound being the paper's normalization
(`s1904_bridge_average_le_one`).  Moreover, if `average P != 1` then the hull
is a proper part of the scaled unit region and the unit region is not contained
in the hull (`s1904_failure_conditions_of_bridge_ne_one`).

`2.` [PROVED] **The bridge is not a consequence of the actual data, and more:
it is empty on a natural family of determinants.**  There are actual
determinants whose procession average exceeds `1`
(`s1904_exists_determinant_average_gt_one`; the witness is a genuine
`SignedHullLogActual` with uniform weights `1/l`, hull log-shell scales
`exp 2`, the unit reference packet and positive tensor power), and for *every*
actual theta hull the bridge FAILS at such a `P`
(`s1904_bridge_false_of_one_lt_average`).  Consequently the
`OrigXiFPaperSignedHullData` structure admits **no** instance whose determinant
is that `exp 2` packet (`s1904_no_datum_with_average_gt_one_determinant`), and
no choice of theta hull repairs this.  In particular the S1880 D field is not
derivable from the theta-hull and determinant fields; it is a genuine extra
identification (`s1904_bridge_not_derivable`).

`3.` [PROVED] **The bridge is exactly a normalization choice, and its content is
exhausted by `average <= 1`.**  For every actual theta hull `T` and every real
`a` with `0 <= a <= 1`, provided the hull is a proper part of the scaled unit
region and the unit region is not inside the hull, there is an actual datum
`D : OrigXiFPaperSignedHullData X l` with the same compact hull, whose Haar
functional is a genuine `OneCircUHaarNormalization` of the same space (same
unit region, same scaling, monotone, normalized) and which satisfies the
bridge with `average = a` (`s1904_exists_datum_of_average_between`).  Hence on
the actual theta hull and the actual determinant the paper's field is
*equivalent* to the two-sided bound on the procession average plus the choice
of the Haar-functional readout; it contains no further geometric or arithmetic
input.

`4.` [PROVED] **The signed face of the same missing.**  At the D level the
bridge is equivalent to the signed scalar identity
`OrigXiFSignedThetaHullLogVolume D = -average`
(`s1904_bridge_iff_signed_scalar`), so the missing object cannot be avoided by
restating it in signed form; and two determinants attached to the same theta
hull and both satisfying the bridge must have equal averages
(`s1904_average_unique`).

`5.` [PROVED] **The three-field datum adds no content beyond the theta hull.**
Any actual theta hull yields a paper signed-hull datum (renormalize the Haar
functional to the up-set of the hull, average `1`), and conversely a datum
yields its theta hull: `Nonempty (OrigXiFPaperSignedHullData X l) ↔
Nonempty (ActualThetaHull X l)` (`s1904_nonempty_datum_iff`,
`s1904_nonempty_datum_of_thetaHull`).  Hence closing the datum `Nonempty`
(which is how the S1905 assembly layer reduces the unconditional Corollary 3.12)
is exactly the S1902 obligation "construct an actual theta hull"; it does not
by itself supply the paper's arithmetic Step (xi-d)/(xi-e) content.

## The exact first missing (stated, not faked)

By `1.`-`4.` the proposition

  `S1904FirstMissing T P : S1904ProcessionBridge T P`

is **not** implied by the actual theta-hull data or by the actual
determinant/log-volume data alone, and by `2.` it is even false for explicit
actual determinants.  The mathematical content that must still be constructed
is therefore not a further algebraic law on `SignedHullLogActual` but the
*readout itself*: a `OneCircUHaarNormalization.logVolume` obtained from an
actual (arithmetic) Haar measure on the theta carrier, together with the
identification of its normalized hull value with the actual
determinant-procession average.  That is exactly the shape of the concrete
missing analytic identity already isolated in the project at
`HaarSignedAverageProof.SignedUnitFactorThetaComparison`
(`tmp/sheaf/xif/paper/HaarSignedAverageProof.lean`), where the Haar side is a
real `Measure.IsAddHaarMeasure mu` on the arithmetic tensor tuple block.  In
the present abstract `ActualThetaHull` interface `logVolume` is an unconstrained
function field, so no proof is possible here: `3.` shows every value in
`[0,1]` is realizable, and `2.` shows values above `1` are impossible.  This
file therefore proves the sharp classification and records the exact missing
obligation; it does **not** assert the bridge, and it uses no `sorry`, axiom,
`True`/`PUnit` slot, or arbitrary inhabitant.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperThetaHull
open LeanFormal.IUT.XiFPaper.OrigXiF
open scoped BigOperators

universe u

variable {X : Type u} [TopologicalSpace X] {l : PrimeGeFive}

/-! ## 0. Cardinality of the signed label set -/

/-- The cardinality of the signed label set is nonzero. -/
theorem s1904_card_ne_zero (l : PrimeGeFive) :
    ((Fintype.card (SignedLabel l.value) : Real)) ≠ 0 := by
  have hpos : 0 < Fintype.card (SignedLabel l.value) :=
    Fintype.card_pos_iff.mpr ⟨zeroSignedLabel l⟩
  exact_mod_cast (Nat.ne_of_gt hpos)

/-! ## 1. The two actual readouts and the bridge proposition -/

/-- The theta-side readout of the procession bridge: the normalized Haar
log-volume of the actual compact holomorphic hull `1,circ U`. -/
noncomputable def s1904HullLogVolume (T : ActualThetaHull X l) : ENNReal :=
  T.haar.logVolume T.compactHull.hull

/-- The determinant-side readout of the procession bridge: the actual
determinant-procession average of `SignedHullLogActual`. -/
noncomputable def s1904ProcessionAverage
    (P : SignedHullLogActual (SignedLabel l.value)) : Real :=
  P.procession.average

/-- **The paper's procession-normalization identification** (IUT III, Step
(xi-d)/(xi-e)) on the actual theta hull and the actual determinant: the
normalized Haar log-volume of the actual hull is the actual
determinant-procession average.  Exactly the S1880 D third field, with the two
sides named. -/
def S1904ProcessionBridge (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value)) : Prop :=
  s1904HullLogVolume T = ENNReal.ofReal (s1904ProcessionAverage P)

/-- The bridge as a proposition on a full paper signed-hull datum. -/
def S1904ProcessionBridgeDatum (D : OrigXiFPaperSignedHullData X l) : Prop :=
  S1904ProcessionBridge D.thetaHull D.determinant

/-- The bridge datum proposition is literally the structure's third field. -/
theorem s1904_bridgeDatum_iff (D : OrigXiFPaperSignedHullData X l) :
    S1904ProcessionBridgeDatum D ↔
      D.thetaHull.haar.logVolume D.thetaHull.compactHull.hull =
        ENNReal.ofReal D.determinant.procession.average :=
  Iff.rfl

/-- The structure's third field gives the bridge datum proposition. -/
theorem s1904_bridgeDatum_of_datum (D : OrigXiFPaperSignedHullData X l) :
    S1904ProcessionBridgeDatum D :=
  D.hull_logVolume_eq_procession

/-- The bridge at the D level is the S1880 hull-log-volume readout
`OrigXiFThetaHullLogVolume`. -/
theorem s1904_bridgeDatum_iff_hullLogVolume (D : OrigXiFPaperSignedHullData X l) :
    S1904ProcessionBridgeDatum D ↔
      OrigXiFThetaHullLogVolume D =
        ENNReal.ofReal D.determinant.procession.average :=
  Iff.rfl

/-! ## 2. Necessity: the bridge forces the procession average into `[0,1]` -/

/-- The actual procession average is nonnegative: every procession value is the
logarithm of a hull log-shell scale at least one.  This holds for every actual
determinant, with no bridge input. -/
theorem s1904_processionAverage_nonneg
    (P : SignedHullLogActual (SignedLabel l.value)) :
    0 ≤ s1904ProcessionAverage P :=
  P.processionNormalizedLogVolume_nonneg

/-- The actual normalized hull Haar log-volume is at most the unit
normalization `1`.  This holds for every actual theta hull, with no bridge
input. -/
theorem s1904_hullLogVolume_le_one (T : ActualThetaHull X l) :
    s1904HullLogVolume T ≤ 1 :=
  T.hull_logVolume_le_one

/-- Under the bridge the procession average is the real part of the actual hull
Haar log-volume. -/
theorem s1904_bridge_average_eq_toReal (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value))
    (h : S1904ProcessionBridge T P) :
    s1904ProcessionAverage P = (s1904HullLogVolume T).toReal := by
  have h0 := s1904_processionAverage_nonneg P
  have hto := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_ofReal h0] at hto
  exact hto.symm

/-- **The bridge forces the procession average to be at most one** (the paper's
`-|log Theta| >= -1` normalization read on the determinant side). -/
theorem s1904_bridge_average_le_one (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value))
    (h : S1904ProcessionBridge T P) :
    s1904ProcessionAverage P ≤ 1 := by
  have hle := s1904_hullLogVolume_le_one T
  have hto : (s1904HullLogVolume T).toReal ≤ (1 : ENNReal).toReal :=
    ENNReal.toReal_mono (ne_of_lt ENNReal.one_lt_top) hle
  rw [ENNReal.toReal_one] at hto
  rw [s1904_bridge_average_eq_toReal T P h]
  exact hto

/-- A real number with `ofReal` equal to `1` is `1`. -/
theorem s1904_ofReal_eq_one {a : Real} (ha : 0 ≤ a)
    (h : ENNReal.ofReal a = 1) : a = 1 := by
  have := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_ofReal ha, ENNReal.toReal_one] at this

/-- **Nondegeneracy forced by the bridge away from `a = 1`.**  If the bridge
holds and the procession average is not `1`, then the holomorphic hull is a
proper part of the scaled unit region, and the unit region is not contained in
the hull.  (If the unit region were inside the hull, or the hull were the whole
scaled unit region, monotonicity plus scaling invariance would force the hull
log-volume to be `1`.) -/
theorem s1904_failure_conditions_of_bridge_ne_one (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value))
    (h : S1904ProcessionBridge T P)
    (hne : s1904ProcessionAverage P ≠ 1) :
    ¬ T.haar.unitRegion ⊆ T.compactHull.hull ∧
      ¬ T.haar.scaleShift '' T.haar.unitRegion ⊆ T.compactHull.hull := by
  have h0 := s1904_processionAverage_nonneg P
  have hofa : ENNReal.ofReal (s1904ProcessionAverage P) =
      s1904HullLogVolume T := h.symm
  constructor
  · intro hU
    have h1 : s1904HullLogVolume T ≤
        T.haar.logVolume (T.haar.scaleShift '' T.haar.unitRegion) :=
      T.haar.logVolume_mono T.hull_subset_scaleShift
    have h2 : T.haar.logVolume (T.haar.scaleShift '' T.haar.unitRegion) =
        T.haar.logVolume T.haar.unitRegion :=
      T.haar.scaleShift_unitRegion_eq
    have h3 : T.haar.logVolume T.haar.unitRegion ≤ s1904HullLogVolume T :=
      T.haar.logVolume_mono hU
    have hunit : T.haar.logVolume T.haar.unitRegion = 1 :=
      T.haar.unitRegion_normalized
    have heq : s1904HullLogVolume T = 1 := by
      refine le_antisymm ?_ ?_
      · calc s1904HullLogVolume T
            ≤ T.haar.logVolume (T.haar.scaleShift '' T.haar.unitRegion) := h1
          _ = T.haar.logVolume T.haar.unitRegion := h2
          _ = 1 := hunit
      · calc (1 : ENNReal) = T.haar.logVolume T.haar.unitRegion := hunit.symm
          _ ≤ s1904HullLogVolume T := h3
    have : ENNReal.ofReal (s1904ProcessionAverage P) = 1 := by
      rw [hofa, heq]
    exact hne (s1904_ofReal_eq_one h0 this)
  · intro hS
    have heq : T.haar.scaleShift '' T.haar.unitRegion = T.compactHull.hull :=
      le_antisymm hS T.hull_subset_scaleShift
    have heqvol : s1904HullLogVolume T =
        T.haar.logVolume T.haar.unitRegion := by
      rw [s1904HullLogVolume, ← heq]
      exact T.haar.scaleShift_unitRegion_eq
    have hunit : T.haar.logVolume T.haar.unitRegion = 1 :=
      T.haar.unitRegion_normalized
    have : ENNReal.ofReal (s1904ProcessionAverage P) = 1 := by
      rw [hofa, heqvol, hunit]
    exact hne (s1904_ofReal_eq_one h0 this)

/-! ## 3. The bridge is empty at actual determinants with average above one -/

/-- The actual determinant datum with hull log-shell scales `exp c`, the unit
reference packet, determinant tensor power `1`, and the uniform procession
with weights `1/l` normalized to total weight `1`.  Its procession values are
the actual log-scales `log (exp c) = c`. -/
noncomputable def s1904UniformDeterminant (l : PrimeGeFive) (c : Real)
    (hc : 0 ≤ c) : SignedHullLogActual (SignedLabel l.value) := by
  classical
  exact
    { hullPacket :=
        { scale := fun _ => Real.exp c
          positive := fun _ => Real.exp_pos c }
      referencePacket :=
        { scale := fun _ => 1
          positive := fun _ => Real.zero_lt_one }
      tensorPower := 1
      tensorPower_pos := Nat.one_pos
      hull_scales_ge_one := fun _ => Real.one_le_exp hc
      reference_scales_eq_one := fun _ => rfl
      procession :=
        { value := fun _ => c
          weight := fun _ => ((Fintype.card (SignedLabel l.value) : Real))⁻¹
          weightTotal := 1
          weightTotal_pos := Real.zero_lt_one
          weightTotal_eq_sum := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            exact (mul_inv_cancel₀ (s1904_card_ne_zero l)).symm }
      procession_values := fun _ => (Real.log_exp c).symm
      weights_nonnegative := fun _ => by
        exact inv_nonneg.mpr (Nat.cast_nonneg _)
      weightTotal_eq_one := rfl }

/-- The uniform determinant has procession average `c`. -/
theorem s1904UniformDeterminant_average (l : PrimeGeFive) (c : Real)
    (hc : 0 ≤ c) :
    (s1904UniformDeterminant l c hc).procession.average = c := by
  have hne := s1904_card_ne_zero l
  have hcard : ((Fintype.card (SignedLabel l.value) : Real)) *
      ((Fintype.card (SignedLabel l.value) : Real))⁻¹ = 1 :=
    mul_inv_cancel₀ hne
  rw [WeightedValues.average]
  simp only [s1904UniformDeterminant]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_one]
  rw [← mul_assoc, hcard, one_mul]

/-- The uniform determinant with log-scale `2` has procession average `2`. -/
theorem s1904_uniformDeterminant_average_two (l : PrimeGeFive) :
    (s1904UniformDeterminant l 2 (by norm_num)).procession.average = 2 :=
  s1904UniformDeterminant_average l 2 (by norm_num)

/-- There is an actual determinant whose procession average exceeds `1`. -/
theorem s1904_exists_determinant_average_gt_one (l : PrimeGeFive) :
    ∃ P : SignedHullLogActual (SignedLabel l.value),
      1 < s1904ProcessionAverage P :=
  ⟨s1904UniformDeterminant l 2 (by norm_num), by
    show 1 < (s1904UniformDeterminant l 2 (by norm_num)).procession.average
    rw [s1904_uniformDeterminant_average_two]
    norm_num⟩

/-- **The bridge fails at every actual theta hull once the procession average
exceeds one.** -/
theorem s1904_bridge_false_of_one_lt_average (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value))
    (hP : 1 < s1904ProcessionAverage P) :
    ¬ S1904ProcessionBridge T P := by
  intro h
  have hle := s1904_bridge_average_le_one T P h
  linarith

/-- **The bridge is not derivable from the actual theta-hull and determinant
data**: for every actual theta hull there is an actual determinant at which the
bridge fails. -/
theorem s1904_bridge_not_derivable (T : ActualThetaHull X l) :
    ∃ P : SignedHullLogActual (SignedLabel l.value),
      ¬ S1904ProcessionBridge T P := by
  obtain ⟨P, hP⟩ := s1904_exists_determinant_average_gt_one l
  exact ⟨P, s1904_bridge_false_of_one_lt_average T P hP⟩

/-- **Every paper signed-hull datum has procession average at most one**: this
is a new consequence of the D third field on the actual determinant side. -/
theorem s1904_datum_average_le_one (D : OrigXiFPaperSignedHullData X l) :
    D.determinant.procession.average ≤ 1 :=
  s1904_bridge_average_le_one D.thetaHull D.determinant
    D.hull_logVolume_eq_procession

/-- **No paper signed-hull datum can carry the `exp 2` uniform determinant**:
the D structure is empty over that actual determinant. -/
theorem s1904_no_datum_with_average_gt_one_determinant
    (D : OrigXiFPaperSignedHullData X l) :
    D.determinant ≠ s1904UniformDeterminant l 2 (by norm_num) := by
  intro hD
  have hle := s1904_datum_average_le_one D
  rw [hD, s1904_uniformDeterminant_average_two] at hle
  linarith

/-! ## 4. Sufficiency: every average in `[0,1]` is realized -/

/-- The two-level Haar normalization on the actual space: unit-region value
`1`, hull value `ofReal a`, everything else at least that.  It is a genuine
`OneCircUHaarNormalization` (monotone, unit region normalized, scaling
invariant) on the same space, with the same unit region and scaling. -/
noncomputable def s1904LevelHaar (H : OneCircUHaarNormalization X) (hull : Set X)
    (a : Real) (ha1 : a ≤ 1) (hU : ¬ H.unitRegion ⊆ hull)
    (hss : ¬ H.scaleShift '' H.unitRegion ⊆ hull) :
    OneCircUHaarNormalization X := by
  classical
  exact
    { unitRegion := H.unitRegion
      logVolume := fun S =>
        if H.unitRegion ⊆ S ∨ H.scaleShift '' H.unitRegion ⊆ S then 1
        else ENNReal.ofReal a
      logVolume_mono := by
        intro S T hST
        by_cases hS : H.unitRegion ⊆ S ∨ H.scaleShift '' H.unitRegion ⊆ S
        · have hT : H.unitRegion ⊆ T ∨ H.scaleShift '' H.unitRegion ⊆ T :=
            hS.imp (fun h x hx => hST (h hx)) (fun h x hx => hST (h hx))
          rw [if_pos hS, if_pos hT]
        · by_cases hT : H.unitRegion ⊆ T ∨ H.scaleShift '' H.unitRegion ⊆ T
          · rw [if_neg hS, if_pos hT]
            exact ENNReal.ofReal_le_one.mpr ha1
          · rw [if_neg hS, if_neg hT]
      unitRegion_normalized := by
        rw [if_pos (Or.inl (Set.Subset.refl H.unitRegion))]
      scaleShift := H.scaleShift
      scaleShift_unitRegion_eq := by
        rw [if_pos (Or.inr (Set.Subset.refl (H.scaleShift '' H.unitRegion)))]
        rw [if_pos (Or.inl (Set.Subset.refl H.unitRegion))] }

/-- The two-level Haar normalization reads `ofReal a` on the hull. -/
theorem s1904LevelHaar_hull (H : OneCircUHaarNormalization X) (hull : Set X)
    (a : Real) (ha1 : a ≤ 1) (hU : ¬ H.unitRegion ⊆ hull)
    (hss : ¬ H.scaleShift '' H.unitRegion ⊆ hull) :
    (s1904LevelHaar H hull a ha1 hU hss).logVolume hull = ENNReal.ofReal a :=
  if_neg (fun h => h.elim hU hss)

/-- **Realizability of the bridge for every average in `[0,1]`.**  Given an
actual theta hull whose holomorphic hull is a proper part of the scaled unit
region and which does not contain the unit region, and any `a` with
`0 ≤ a ≤ 1`, there is a paper signed-hull datum with the same compact hull, a
genuine normalized Haar functional on the same space, determinant procession
average exactly `a`, and the bridge proved. -/
theorem s1904_exists_datum_of_average_between (T : ActualThetaHull X l)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hU : ¬ T.haar.unitRegion ⊆ T.compactHull.hull)
    (hss : ¬ T.haar.scaleShift '' T.haar.unitRegion ⊆ T.compactHull.hull) :
    ∃ D : OrigXiFPaperSignedHullData X l,
      S1904ProcessionBridgeDatum D ∧
        D.determinant.procession.average = a ∧
          D.thetaHull.compactHull = T.compactHull := by
  classical
  have hfield :
      (s1904LevelHaar T.haar T.compactHull.hull a ha1 hU hss).logVolume
          T.compactHull.hull =
        ENNReal.ofReal (s1904UniformDeterminant l a ha0).procession.average := by
    rw [s1904LevelHaar_hull, s1904UniformDeterminant_average]
  refine ⟨
    { thetaHull :=
        { procession := T.procession
          compactHull := T.compactHull
          haar := s1904LevelHaar T.haar T.compactHull.hull a ha1 hU hss
          hull_subset_scaleShift := T.hull_subset_scaleShift
          paper_IQCarrier_realization := T.paper_IQCarrier_realization }
      determinant := s1904UniformDeterminant l a ha0
      hull_logVolume_eq_procession := hfield }, ?_, ?_, rfl⟩
  · show (s1904LevelHaar T.haar T.compactHull.hull a ha1 hU hss).logVolume
        T.compactHull.hull =
      ENNReal.ofReal (s1904UniformDeterminant l a ha0).procession.average
    exact hfield
  · exact s1904UniformDeterminant_average l a ha0


/-- The `a = 1` Haar normalization: value `1` on every region containing the
hull, the unit region, or the scaled unit region, and `0` otherwise.  It is a
genuine `OneCircUHaarNormalization` (an up-set indicator, hence monotone, with
unit-region value `1` and scaling invariance), on the same space with the same
unit region and scaling. -/
noncomputable def s1904UnitHaar (H : OneCircUHaarNormalization X) (hull : Set X) :
    OneCircUHaarNormalization X := by
  classical
  exact
    { unitRegion := H.unitRegion
      logVolume := fun S =>
        if hull ⊆ S ∨ H.unitRegion ⊆ S ∨
          H.scaleShift '' H.unitRegion ⊆ S then 1 else 0
      logVolume_mono := by
        intro S T hST
        by_cases hS : hull ⊆ S ∨ H.unitRegion ⊆ S ∨
            H.scaleShift '' H.unitRegion ⊆ S
        · have hT : hull ⊆ T ∨ H.unitRegion ⊆ T ∨
              H.scaleShift '' H.unitRegion ⊆ T := by
            rcases hS with h | h | h
            · exact Or.inl (fun x hx => hST (h hx))
            · exact Or.inr (Or.inl (fun x hx => hST (h hx)))
            · exact Or.inr (Or.inr (fun x hx => hST (h hx)))
          rw [if_pos hS, if_pos hT]
        · rw [if_neg hS]
          by_cases hT : hull ⊆ T ∨ H.unitRegion ⊆ T ∨
              H.scaleShift '' H.unitRegion ⊆ T
          · rw [if_pos hT]
            exact zero_le_one
          · rw [if_neg hT]
      unitRegion_normalized := by
        rw [if_pos (Or.inr (Or.inl (Set.Subset.refl H.unitRegion)))]
      scaleShift := H.scaleShift
      scaleShift_unitRegion_eq := by
        rw [if_pos (Or.inr (Or.inr
          (Set.Subset.refl (H.scaleShift '' H.unitRegion))))]
        rw [if_pos (Or.inr (Or.inl (Set.Subset.refl H.unitRegion)))] }

/-- The `a = 1` Haar normalization reads `1` on the hull. -/
theorem s1904UnitHaar_hull (H : OneCircUHaarNormalization X) (hull : Set X) :
    (s1904UnitHaar H hull).logVolume hull = 1 :=
  if_pos (Or.inl (Set.Subset.refl hull))

/-- **Realizability at `a = 1`**, with no nondegeneracy hypothesis: the
unit-value Haar normalization realizes the bridge with procession average
`1` on every actual theta hull. -/
theorem s1904_exists_datum_average_one (T : ActualThetaHull X l) :
    ∃ D : OrigXiFPaperSignedHullData X l,
      S1904ProcessionBridgeDatum D ∧
        D.determinant.procession.average = 1 ∧
          D.thetaHull.compactHull = T.compactHull := by
  classical
  have hfield :
      (s1904UnitHaar T.haar T.compactHull.hull).logVolume T.compactHull.hull =
        ENNReal.ofReal (s1904UniformDeterminant l 1 (by norm_num)).procession.average := by
    rw [s1904UnitHaar_hull, s1904UniformDeterminant_average, ENNReal.ofReal_one]
  refine ⟨
    { thetaHull :=
        { procession := T.procession
          compactHull := T.compactHull
          haar := s1904UnitHaar T.haar T.compactHull.hull
          hull_subset_scaleShift := T.hull_subset_scaleShift
          paper_IQCarrier_realization := T.paper_IQCarrier_realization }
      determinant := s1904UniformDeterminant l 1 (by norm_num)
      hull_logVolume_eq_procession := hfield }, ?_, ?_, rfl⟩
  · show (s1904UnitHaar T.haar T.compactHull.hull).logVolume
        T.compactHull.hull =
      ENNReal.ofReal (s1904UniformDeterminant l 1 (by norm_num)).procession.average
    exact hfield
  · exact s1904UniformDeterminant_average l 1 (by norm_num)

/-- **Every average in `[0,1]` is realized**, with `a = 1` requiring no
nondegeneracy hypothesis.  Together with `s1904_bridge_average_le_one` and
`s1904_failure_conditions_of_bridge_ne_one` this is the exact content of the
theta-side readout: its range over normalized Haar functionals is `[0,1]`, and
the value `1` is forced whenever the hull swallows the unit region or equals
the scaled unit region. -/
theorem s1904_exists_datum_of_average_between' (T : ActualThetaHull X l)
    {a : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (h : a = 1 ∨ (¬ T.haar.unitRegion ⊆ T.compactHull.hull ∧
      ¬ T.haar.scaleShift '' T.haar.unitRegion ⊆ T.compactHull.hull)) :
    ∃ D : OrigXiFPaperSignedHullData X l,
      S1904ProcessionBridgeDatum D ∧
        D.determinant.procession.average = a ∧
          D.thetaHull.compactHull = T.compactHull := by
  rcases h with rfl | ⟨hU, hss⟩
  · exact s1904_exists_datum_average_one T
  · exact s1904_exists_datum_of_average_between T ha0 ha1 hU hss


/-- **The D structure adds no content beyond the theta hull, given the freedom
of the Haar-functional field.**  Any actual theta hull yields a paper
signed-hull datum: renormalize the Haar functional to the up-set of the hull
(so it reads `1` on the hull) and take the uniform determinant with average
`1`.  Consequently inhabitation of `OrigXiFPaperSignedHullData` is *exactly*
inhabitation of `ActualThetaHull`; closing the datum is therefore not the
paper's Step (xi-d)/(xi-e) content, which lives in the source construction of
the theta hull and in a Haar readout tied to the arithmetic measure. -/
theorem s1904_nonempty_datum_of_thetaHull (T : ActualThetaHull X l) :
    Nonempty (OrigXiFPaperSignedHullData X l) := by
  obtain ⟨D, -, -, -⟩ := s1904_exists_datum_average_one T
  exact ⟨D⟩

/-- **The exact inhabitation content of the three-field datum**: a paper
signed-hull datum exists if and only if an actual theta hull exists.  The
determinant side and the procession bridge are not obstructions once the Haar
functional is free. -/
theorem s1904_nonempty_datum_iff :
    Nonempty (OrigXiFPaperSignedHullData X l) ↔
      Nonempty (ActualThetaHull X l) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.thetaHull⟩
  · rintro ⟨T⟩
    exact s1904_nonempty_datum_of_thetaHull T

/-! ## 5. The signed face and uniqueness -/

/-- The signed theta-side readout of the procession bridge: the paper's
`-|log Theta|` as minus the real part of the normalized Haar hull log-volume. -/
noncomputable def s1904SignedHullLogVolume (T : ActualThetaHull X l) : Real :=
  -(s1904HullLogVolume T).toReal

/-- **The bridge is equivalent to the finite (`toReal`) identity**: the
`ENNReal.ofReal` conversion in the paper's statement loses no information,
because the hull Haar log-volume is always finite. -/
theorem s1904_bridge_iff_toReal (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value)) :
    S1904ProcessionBridge T P ↔
      s1904ProcessionAverage P = (s1904HullLogVolume T).toReal := by
  constructor
  · intro h
    exact s1904_bridge_average_eq_toReal T P h
  · intro h
    have hfin : s1904HullLogVolume T < ⊤ :=
      lt_of_le_of_lt (s1904_hullLogVolume_le_one T) ENNReal.one_lt_top
    show s1904HullLogVolume T = ENNReal.ofReal (s1904ProcessionAverage P)
    rw [h, ENNReal.ofReal_toReal (ne_of_lt hfin)]

/-- **The signed face of the same missing object.**  The bridge is equivalent
to the paper's signed normalization `-|log Theta| = -average`, so the missing
object cannot be bypassed by switching to the signed carrier. -/
theorem s1904_bridge_iff_signed (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value)) :
    S1904ProcessionBridge T P ↔
      s1904SignedHullLogVolume T = -s1904ProcessionAverage P := by
  have hfin : s1904HullLogVolume T < ⊤ :=
    lt_of_le_of_lt (s1904_hullLogVolume_le_one T) ENNReal.one_lt_top
  constructor
  · intro h
    rw [s1904SignedHullLogVolume, s1904_bridge_average_eq_toReal T P h]
  · intro h
    have hreal : (s1904HullLogVolume T).toReal = s1904ProcessionAverage P := by
      have := congrArg Neg.neg h
      simpa [s1904SignedHullLogVolume] using this
    refine (s1904_bridge_iff_toReal T P).mpr ?_
    exact hreal.symm

/-- At the D level the signed scalar readout is `-average` (the S1880
readout), so the bridge is exactly the paper's signed procession
normalization there. -/
theorem s1904_datum_signed_scalar (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFSignedThetaHullLogVolume D = -D.determinant.procession.average :=
  OrigXiFSignedThetaHullLogVolume_eq_neg_average D

/-- **Uniqueness of the procession average along a fixed theta hull**: two
actual determinants attached to the same actual theta hull and both satisfying
the bridge have the same procession average. -/
theorem s1904_average_unique (T : ActualThetaHull X l)
    (P Q : SignedHullLogActual (SignedLabel l.value))
    (hP : S1904ProcessionBridge T P) (hQ : S1904ProcessionBridge T Q) :
    s1904ProcessionAverage P = s1904ProcessionAverage Q := by
  rw [s1904_bridge_average_eq_toReal T P hP,
    s1904_bridge_average_eq_toReal T Q hQ]

/-- **The exact content of the S1880 D third field** on the actual theta hull
and the actual determinant: it forces the procession average into `[0,1]`; it
is empty above `1`; explicit actual determinants above `1` exist. -/
theorem s1904_bridge_exact_content :
    (∀ (T : ActualThetaHull X l) (P : SignedHullLogActual (SignedLabel l.value)),
      S1904ProcessionBridge T P →
        0 ≤ s1904ProcessionAverage P ∧ s1904ProcessionAverage P ≤ 1) ∧
    (∀ (T : ActualThetaHull X l) (P : SignedHullLogActual (SignedLabel l.value)),
      1 < s1904ProcessionAverage P → ¬ S1904ProcessionBridge T P) ∧
    (∃ P : SignedHullLogActual (SignedLabel l.value),
      1 < s1904ProcessionAverage P) :=
  ⟨fun T P h => ⟨s1904_processionAverage_nonneg P,
      s1904_bridge_average_le_one T P h⟩,
    fun T P hP => s1904_bridge_false_of_one_lt_average T P hP,
    s1904_exists_determinant_average_gt_one l⟩

/-- **The exact first missing**, named as a proposition: the procession bridge
on the actual theta hull and the actual determinant.  It is not implied by the
other actual data (section 3) nor refutable in general (section 4); it has to
be supplied by a construction of the Haar readout from actual arithmetic data
(see the module docstring). -/
def S1904FirstMissing (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value)) : Prop :=
  S1904ProcessionBridge T P

/-- The first missing proposition is the bridge. -/
theorem S1904FirstMissing_iff (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value)) :
    S1904FirstMissing T P ↔ S1904ProcessionBridge T P :=
  Iff.rfl

/-- The first missing proposition is exactly the S1880 D third field. -/
theorem S1904FirstMissing_iff_datum (D : OrigXiFPaperSignedHullData X l) :
    S1904FirstMissing D.thetaHull D.determinant ↔
      D.thetaHull.haar.logVolume D.thetaHull.compactHull.hull =
        ENNReal.ofReal D.determinant.procession.average :=
  Iff.rfl

/-! ## 6. Axiom probes -/

#print axioms s1904_bridge_average_le_one
#print axioms s1904_failure_conditions_of_bridge_ne_one
#print axioms s1904UniformDeterminant_average
#print axioms s1904_exists_determinant_average_gt_one
#print axioms s1904_bridge_not_derivable
#print axioms s1904_datum_average_le_one
#print axioms s1904_no_datum_with_average_gt_one_determinant
#print axioms s1904LevelHaar_hull
#print axioms s1904_exists_datum_of_average_between
#print axioms s1904UnitHaar_hull
#print axioms s1904_exists_datum_average_one
#print axioms s1904_exists_datum_of_average_between'
#print axioms s1904_nonempty_datum_of_thetaHull
#print axioms s1904_nonempty_datum_iff
#print axioms s1904_bridge_iff_toReal
#print axioms s1904_bridge_iff_signed
#print axioms s1904_average_unique
#print axioms s1904_bridge_exact_content

end LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual

end
