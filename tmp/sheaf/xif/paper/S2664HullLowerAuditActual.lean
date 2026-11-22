/-
  # S2664: audit of lower bounds for the source holomorphic-hull log-degree

  Target (`HullDegreeLowerBound`, S2614):

    exists C : Real, forall x, x in hull -> C <= I.sourceLocalLogDegree v x.

  ## Findings

  * **No current actual hypothesis implies the target for the source hull.**
    - `SourceCompactBound`, `SourceOModuleLayer`,
      `ValueHullCompactnessInput`, `SourceOneCircUCompactness`
      and `sourceHullVolume_lt_top_of_hullBound` all bound the log-degree
      *above* (`... <= C`).  The unit-region containment
      `hull <= lambda * O` plus an upper bound on `O` yields only an
      upper bound on the hull, via additivity of `sourceLocalLogDegree`
      (`sourceHullVolume_lt_top_of_scaledRegionImage`).
    - Under pointwise degree faithfulness `hdeg`, the target is refuted
      outright by S2663 (`not_exists_hull_logDegree_lower_bound`): the
      constant scaling with exponent `-(k+1)` lies in
      `sourceScalingUnits` and drives the hull degree to `-infinity`.
    - Without `hdeg`, the concrete source model of
      `SourceUnitRegionHaarDataActual.lean` gives a
      `SourceOneCircUCompactness` datum while both the actual hull and the
      bridge unit region are unbounded below (Section 5).  The
      `SourceOModuleLayer` structure records only an upper bound, so the
      interface admits a lower-unbounded unit region.
    - The O-module/arithmetic-tuple canonical-hull bridge
      (`SourceArithmeticThetaPilotBridge`) likewise has only
      `unit_bound : degree <= C`; it cannot supply a lower bound.

  * **Actual positive results.**
    - The finite image union `possibleThetaPilotImageSet` has a lower
      bound (finite minimum over the signed labels): Section 2.
    - A scaled region `lambda * O` has a lower bound if `lambda` and
      `O` do (Section 3); this is the exact missing-premise shape for the
      O-module compactness datum.
    - `HullDegreeLowerBound hull` is *equivalent* to finiteness of the
      signed hull volume (Section 4).  Replacing the pointwise lower bound by a
      finite signed hull volume is therefore not a weakening; and an unsigned
      hull volume (positive part) is a different, upper-side notion (the
      concrete model has unsigned hull volume 0 and infinite signed hull
      volume).
    - `SignedGap2SourceData` is inhabited with hull = the finite image
      union and scaledUnit = hull (Section 6).  Thus the data structure itself
      is satisfiable; what is missing is the geometric identification of the
      hull/scaledUnit with the paper's source hull and scaled region, not a
      construction of the structure.

  No existing source file is modified.
-/
import tmp.sheaf.xif.paper.S2614CompactnessScalingActual
import tmp.sheaf.xif.paper.S2611SignedGap2SourceActual
import tmp.sheaf.xif.paper.S2663HullLowerUnboundedActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2605SignedSourceVolumeActual
open LeanFormal.IUT.XiFPaper.S2611SignedGap2SourceActual
open LeanFormal.IUT.XiFPaper.S2614CompactnessScalingActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2664HullLowerAuditActual

universe ua uv upi umon ui

/-! ## 1. Monotonicity of the lower-bound predicate -/

section Generic

variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- A lower bound propagates from a superset to a subset. -/
theorem hullDegreeLowerBound_mono (v : V) {S T : Set (I.ThetaPilotPoint v)}
    (hST : S ⊆ T) (hT : HullDegreeLowerBound (I := I) T) :
    HullDegreeLowerBound (I := I) S := by
  obtain ⟨C, hC⟩ := hT
  exact ⟨C, fun x hx => hC x (hST hx)⟩

/-- Log-degree of powers.  This is the local form used for the concrete model;
it does not use degree faithfulness. -/
theorem sourceLocalLogDegree_pow_audit (v : V) (x : I.ThetaPilotPoint v) (k : Nat) :
    I.sourceLocalLogDegree v (x ^ k) =
      (k : Real) * I.sourceLocalLogDegree v x := by
  induction k with
  | zero => simp [I.sourceLocalLogDegree_one]
  | succ k ih =>
      rw [pow_succ, I.sourceLocalLogDegree_mul, ih]
      push_cast
      ring

/-! ## 2. The actual lower-bound source: the finite image union -/

/-- **Unconditional lower bound on the finite theta-pilot image union.**  The
image union is the image of the finite label set `SignedLabel l.value`, so a
minimum of the real log-degree exists.  No degree faithfulness, compactness, or
upper-bound hypothesis is used. -/
theorem hullDegreeLowerBound_possibleThetaPilotImageSet (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    HullDegreeLowerBound (I := I) (I.possibleThetaPilotImageSet v R n) := by
  classical
  have hfin : (I.possibleThetaPilotImageSet v R n).Finite := by
    have hEq : I.possibleThetaPilotImageSet v R n =
        I.sourceThetaPilotPoint v R n '' (Set.univ : Set (SignedLabel l.value)) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨j, Set.mem_univ j, rfl⟩
      · rintro ⟨j, _hj, rfl⟩
        exact ⟨j, rfl⟩
    rw [hEq]
    exact Set.finite_univ.image _
  obtain ⟨x, hx, hmin⟩ :=
    Set.exists_min_image (I.possibleThetaPilotImageSet v R n)
      (fun x => I.sourceLocalLogDegree v x) hfin
      (I.possibleThetaPilotImageSet_nonempty v R n)
  exact ⟨I.sourceLocalLogDegree v x, fun y hy => hmin y hy⟩

/-! ## 3. The exact missing-premise shape for the O-module/scaled-region data -/

/-- A lower bound on a scaled region `lambda * O` follows from lower bounds on
the scaling and on the unit region.  This is the lower-side counterpart of
`sourceHullVolume_lt_top_of_scaledRegionImage`. -/
theorem hullDegreeLowerBound_scaledRegionImage
    {v : V} {lam : I.ThetaPilotPoint v} {O : Set (I.ThetaPilotPoint v)}
    {Cl Co : Real} (hlam : Cl <= I.sourceLocalLogDegree v lam)
    (hO : forall y, y ∈ O -> Co <= I.sourceLocalLogDegree v y) :
    HullDegreeLowerBound (I := I) (scaledRegionImage lam O) := by
  refine ⟨Cl + Co, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  rw [I.sourceLocalLogDegree_mul]
  linarith [hlam, hO y hy]

/-- **Conditional hull lower bound from the O-module compactness datum.**  If the
scaling and the unit region of a `SourceOneCircUCompactness` datum are bounded
below, then the actual source hull is bounded below by additivity and the
containment `hull <= lambda * O`.

The two lower-bound hypotheses are exactly what the current structure does not
provide: `SourceOModuleLayer.unitRegion_logDegree_le` is an upper bound and
`SourceUnitRegionHaarData.scaling_logDegree_nonpos` bounds the scaling above. -/
theorem hullDegreeLowerBound_sourceHolomorphicHull_of_compactness
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (C : I.SourceOneCircUCompactness v R n)
    {Cl Co : Real} (hlam : Cl <= I.sourceLocalLogDegree v C.scaling)
    (hO : forall y, y ∈ C.layer.unitRegion ->
      Co <= I.sourceLocalLogDegree v y) :
    HullDegreeLowerBound (I := I)
      ((I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) := by
  obtain ⟨B, hB⟩ := hullDegreeLowerBound_scaledRegionImage (I := I)
    (v := v) (lam := C.scaling) (O := C.layer.unitRegion) hlam hO
  exact ⟨B, fun x hx => hB x (C.hull_subset_scaledRegionImage hx)⟩

/-- The precise replacement hypothesis for the hull lower bound: a scaling
`lambda` and a unit region `O` with `hull <= lambda * O`, both bounded
below.  This is the paper-shaped `lambda . O` input with the missing lower side
made explicit. -/
def ScaledRegionLowerBoundSource (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Prop :=
  exists (lam : I.ThetaPilotPoint v) (O : Set (I.ThetaPilotPoint v))
      (Cl Co : Real),
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
        scaledRegionImage lam O ∧
      Cl <= I.sourceLocalLogDegree v lam ∧
      (forall y, y ∈ O -> Co <= I.sourceLocalLogDegree v y)

/-- The replacement hypothesis implies the hull lower bound. -/
theorem hullDegreeLowerBound_of_scaledRegionLowerBoundSource
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (h : ScaledRegionLowerBoundSource I v R n) :
    HullDegreeLowerBound (I := I)
      ((I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) := by
  obtain ⟨lam, O, Cl, Co, hHull, hlam, hO⟩ := h
  obtain ⟨B, hB⟩ := hullDegreeLowerBound_scaledRegionImage (I := I)
    (v := v) (lam := lam) (O := O) hlam hO
  exact ⟨B, fun x hx => hB x (hHull hx)⟩

/-! ## 4. Finite signed hull volume is exactly the pointwise lower bound -/

/-- A finite signed hull volume gives a pointwise lower bound. -/
theorem hullDegreeLowerBound_of_signedHullVolume_lt_top
    (v : V) {hull : Set (I.ThetaPilotPoint v)}
    (h : sourceSetVolumeSigned I v hull < ⊤) :
    HullDegreeLowerBound (I := I) hull := by
  refine ⟨-(sourceSetVolumeSigned I v hull).toReal, ?_⟩
  intro x hx
  have hxle : sourcePointVolumeSigned I v x <= sourceSetVolumeSigned I v hull :=
    le_iSup_of_le x (le_iSup_of_le hx le_rfl)
  have hEq : sourceSetVolumeSigned I v hull =
      ENNReal.ofReal (sourceSetVolumeSigned I v hull).toReal :=
    (ENNReal.ofReal_toReal h.ne).symm
  rw [hEq] at hxle
  have hle : -I.sourceLocalLogDegree v x <=
      (sourceSetVolumeSigned I v hull).toReal :=
    (ENNReal.ofReal_le_ofReal_iff (ENNReal.toReal_nonneg)).mp hxle
  linarith

/-- A pointwise lower bound gives a finite signed hull volume (the in-tree
`signedHullFinite_of_logDegree_ge`). -/
theorem signedHullVolume_lt_top_of_hullDegreeLowerBound
    (v : V) {hull : Set (I.ThetaPilotPoint v)}
    (h : HullDegreeLowerBound (I := I) hull) :
    sourceSetVolumeSigned I v hull < ⊤ :=
  signedHullFinite_of_logDegree_ge I (by simpa [HullDegreeLowerBound] using h)

/-- **Exact equivalence.**  The `hull_logDegree_ge` field of
`SignedGap2SourceData` is not a technical convenience: it is exactly
finiteness of the signed hull volume.  A finite *unsigned* hull volume is a
different, upper-side statement. -/
theorem hullDegreeLowerBound_iff_signedHullVolume_lt_top
    (v : V) (hull : Set (I.ThetaPilotPoint v)) :
    HullDegreeLowerBound (I := I) hull ↔
      sourceSetVolumeSigned I v hull < ⊤ :=
  ⟨fun h => signedHullVolume_lt_top_of_hullDegreeLowerBound I v h,
    fun h => hullDegreeLowerBound_of_signedHullVolume_lt_top I v h⟩

/-- The proposed replacement `d(scaling) >= 0 for all scaling units` is false
in the degree-faithful regime: the constant scaling of exponent `-1` is a
scaling unit of log-degree `-card`.  It also would not give a hull lower
bound by itself, since the hull is closed under powers of its image points. -/
theorem not_forall_sourceScalingUnits_logDegree_nonneg_of_degreeFaithful
    (v : V) (R : I.SourceImageRealization v)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ (forall s, s ∈ I.sourceScalingUnits v ->
      0 <= I.sourceLocalLogDegree v s) := by
  intro hnonneg
  have hmem : I.constantThetaPilotPoint v R (Multiplicative.ofAdd (-1 : Real)) ∈
      I.sourceScalingUnits v :=
    I.constantThetaPilotPoint_mem_sourceScalingUnits v R (a := -1) (by norm_num) hdeg
  have hdegneg : I.sourceLocalLogDegree v
      (I.constantThetaPilotPoint v R (Multiplicative.ofAdd (-1 : Real))) =
      -((Fintype.card (SourceVolumeIndex l) : Real)) := by
    rw [I.sourceLocalLogDegree_constant v R (-1) hdeg]
    ring
  have h := hnonneg _ hmem
  rw [hdegneg] at h
  have hcard : (0 : Real) < (Fintype.card (SourceVolumeIndex l) : Real) := by
    exact_mod_cast sourceVolumeIndex_card_pos l
  linarith

end Generic

/-! ## 4b. The S2663 refutation in the degree-faithful regime

S2663 is stated for `V : Type` (universe 0); this section records the
`HullDegreeLowerBound` restatement at that universe. -/

section DegreeFaithful

variable {l : PrimeGeFive} {V : Type}
variable (I : Theorem311Source.OriginalInput.{ua, 0, upi, umon, ui} l V)

/-- The exact S2663 refutation, restated at the `HullDegreeLowerBound` target:
under pointwise degree faithfulness the source holomorphic hull has no lower
bound. -/
theorem not_hullDegreeLowerBound_sourceHolomorphicHull_of_degreeFaithful
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : forall b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ HullDegreeLowerBound (I := I)
      ((I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))) := by
  simpa [HullDegreeLowerBound] using
    LeanFormal.IUT.XiFPaper.S2663HullLowerUnboundedActual.not_exists_hull_logDegree_lower_bound
      I v R n hdeg

end DegreeFaithful

/-! ## 5. Concrete countermodel without degree faithfulness

`SourceUnitRegionHaarDataActual.lean` constructs a genuine `OriginalInput`
(`sourceHaarActualOriginalInput`) whose value monoid is the nonpositive reals:
every log-degree is `<= 0`, so the *upper* bound of the O-module compactness
layer holds with bound `0`.  The strict point `sourceHaarActualStrictPoint`
lies in the actual hull and has log-degree `-card`; its powers are hull points
with log-degree `-k * card`, hence the hull (and `Set.univ`) is
unbounded below.

This shows that the current `SourceOneCircUCompactness` / `SourceOModuleLayer`
interface is consistent with a lower-unbounded unit region: it cannot imply
`HullDegreeLowerBound`. -/

section Concrete

variable {l : PrimeGeFive}

/-- The actual source hull of the concrete model, as a set. -/
abbrev sourceHaarActualHull (S : SourceDefinition31Data.{ua} l)
    (n : ThetaPilotCarrier l) :
    Set ((sourceHaarActualOriginalInput S).ThetaPilotPoint ()) :=
  ↑((sourceHaarActualOriginalInput S).sourceHolomorphicHull ()
    (sourceHaarActualImageRealization S) n)

/-- The compactness datum of the concrete model, with unit region `Set.univ`
and upper bound `0`. -/
def sourceHaarActualOneCircUCompactness (S : SourceDefinition31Data.{ua} l)
    (n : ThetaPilotCarrier l) :
    (sourceHaarActualOriginalInput S).SourceOneCircUCompactness ()
      (sourceHaarActualImageRealization S) n where
  oneCircU := Set.univ
  image_subset_oneCircU := by
    intro x _hx
    exact Set.mem_univ x
  layer :=
    { unitRegion := Set.univ
      degreeBound := 0
      unitRegion_logDegree_le := by
        intro y _hy
        exact sourceHaarActual_sourceLocalLogDegree_nonpos S n y }
  scaling := 1
  hull_subset_scaledRegionImage := by
    intro x _hx
    exact ⟨x, Set.mem_univ x, (one_mul x).symm⟩

/-- The bridge unit region of the concrete compactness datum is all of the
carrier. -/
theorem sourceHaarActualOneCircUCompactness_bridgeUnitRegion
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l) :
    (sourceOModuleCompactness_haarData (I := sourceHaarActualOriginalInput S)
      () (sourceHaarActualImageRealization S) n
      (sourceHaarActualOneCircUCompactness S n)).unitRegion = Set.univ := by
  have hscaling : (sourceHaarActualOneCircUCompactness S n).scaling = 1 := rfl
  have hunit : (sourceHaarActualOneCircUCompactness S n).layer.unitRegion = Set.univ :=
    rfl
  rw [sourceOModuleCompactness_haarData_unitRegion, hscaling, hunit]
  ext x
  simp [scaledRegionImage]

/-- If a set contains all powers of the strict point, it has no lower bound in
the concrete model. -/
theorem sourceHaarActual_not_lowerBounded_of_pow_mem
    (S : SourceDefinition31Data.{ua} l)
    {A : Set ((sourceHaarActualOriginalInput S).ThetaPilotPoint ())}
    (hA : forall k : Nat, (sourceHaarActualStrictPoint S) ^ k ∈ A) :
    ¬ HullDegreeLowerBound (I := sourceHaarActualOriginalInput S) A := by
  rintro ⟨C, hC⟩
  have hcard : (0 : Real) < (Fintype.card (SourceVolumeIndex l) : Real) := by
    exact_mod_cast sourceVolumeIndex_card_pos l
  obtain ⟨k, hk⟩ :=
    exists_nat_gt ((-C) / (Fintype.card (SourceVolumeIndex l) : Real))
  have hk' : -C < (k : Real) * (Fintype.card (SourceVolumeIndex l) : Real) := by
    have hm := mul_lt_mul_of_pos_right hk hcard
    have hcancel : ((-C) / (Fintype.card (SourceVolumeIndex l) : Real)) *
        (Fintype.card (SourceVolumeIndex l) : Real) = -C :=
      div_mul_cancel₀ (-C) (ne_of_gt hcard)
    rwa [hcancel] at hm
  have hdeg : (sourceHaarActualOriginalInput S).sourceLocalLogDegree ()
      ((sourceHaarActualStrictPoint S) ^ k) =
      -((k : Real) * (Fintype.card (SourceVolumeIndex l) : Real)) := by
    rw [sourceLocalLogDegree_pow_audit, sourceHaarActualStrictPoint_logDegree]
    ring
  have hlt : (sourceHaarActualOriginalInput S).sourceLocalLogDegree ()
      ((sourceHaarActualStrictPoint S) ^ k) < C := by
    rw [hdeg]
    linarith
  exact not_lt_of_ge (hC _ (hA k)) hlt

/-- The actual source holomorphic hull of the concrete model has no lower
bound.  No degree-faithfulness hypothesis is used. -/
theorem sourceHaarActual_hull_not_lowerBounded
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l) :
    ¬ HullDegreeLowerBound (I := sourceHaarActualOriginalInput S)
      (sourceHaarActualHull S n) := by
  apply sourceHaarActual_not_lowerBounded_of_pow_mem S (A := sourceHaarActualHull S n)
  intro k
  have hbase : sourceHaarActualStrictPoint S ∈ (sourceHaarActualData S n).unitRegion :=
    sourceHaarActualStrictPoint_mem_unitRegion S n
  rw [sourceHaarActualData_unitRegion] at hbase
  exact Submonoid.pow_mem _ hbase k

/-- In the concrete model the strict point is itself a scaling unit of negative
log-degree, so the proposed `d(scaling) >= 0` restriction fails without any
degree-faithfulness hypothesis. -/
theorem sourceHaarActual_strictPoint_mem_sourceScalingUnits
    (S : SourceDefinition31Data.{ua} l) :
    sourceHaarActualStrictPoint S ∈
      (sourceHaarActualOriginalInput S).sourceScalingUnits () := by
  intro p hp
  have hto := congrArg Multiplicative.toAdd hp
  change (sourceHaarActualMinusOne : sourceHaarActualNonpositiveAddSubmonoid) = 0 at hto
  have hreal : (-1 : Real) = 0 :=
    congrArg (fun q : sourceHaarActualNonpositiveAddSubmonoid => (q : Real)) hto
  norm_num at hreal

/-- The concrete model's scaling units are not all of nonnegative log-degree. -/
theorem sourceHaarActual_scaling_nonneg_false
    (S : SourceDefinition31Data.{ua} l) :
    ¬ (forall s, s ∈ (sourceHaarActualOriginalInput S).sourceScalingUnits () ->
      0 <= (sourceHaarActualOriginalInput S).sourceLocalLogDegree () s) := by
  intro hnonneg
  have hmem := sourceHaarActual_strictPoint_mem_sourceScalingUnits S
  have hdegneg := sourceHaarActualStrictPoint_logDegree S
  have h := hnonneg _ hmem
  rw [hdegneg] at h
  have hcard : (0 : Real) < (Fintype.card (SourceVolumeIndex l) : Real) := by
    exact_mod_cast sourceVolumeIndex_card_pos l
  linarith

/-- The full carrier `Set.univ` has no lower bound in the concrete model. -/
theorem sourceHaarActual_univ_not_lowerBounded
    (S : SourceDefinition31Data.{ua} l) :
    ¬ HullDegreeLowerBound (I := sourceHaarActualOriginalInput S)
      (Set.univ : Set ((sourceHaarActualOriginalInput S).ThetaPilotPoint ())) :=
  sourceHaarActual_not_lowerBounded_of_pow_mem S (A := Set.univ)
    (fun k => Set.mem_univ _)

/-- The bridge unit region of the concrete compactness datum has no lower
bound. -/
theorem sourceHaarActual_bridgeUnitRegion_not_lowerBounded
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l) :
    ¬ HullDegreeLowerBound (I := sourceHaarActualOriginalInput S)
      (sourceOModuleCompactness_haarData (I := sourceHaarActualOriginalInput S)
        () (sourceHaarActualImageRealization S) n
        (sourceHaarActualOneCircUCompactness S n)).unitRegion := by
  rw [sourceHaarActualOneCircUCompactness_bridgeUnitRegion S n]
  exact sourceHaarActual_univ_not_lowerBounded S

/-- **Headline counterexample.**  There is a `SourceOneCircUCompactness`
datum in the concrete model while the actual source holomorphic hull is not
bounded below.  Hence the O-module compactness interface alone (upper bound +
`hull <= lambda * O` + unit-region containment) cannot imply
`HullDegreeLowerBound`. -/
theorem exists_sourceOneCircUCompactness_not_hullDegreeLowerBound
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l) :
    exists C : (sourceHaarActualOriginalInput S).SourceOneCircUCompactness ()
        (sourceHaarActualImageRealization S) n,
      ¬ HullDegreeLowerBound (I := sourceHaarActualOriginalInput S)
        (sourceHaarActualHull S n) :=
  ⟨sourceHaarActualOneCircUCompactness S n, sourceHaarActual_hull_not_lowerBounded S n⟩

/-- The unsigned (positive-part) hull volume of the concrete model is `0`:
all log-degrees are nonpositive. -/
theorem sourceHaarActual_unsignedHullVolume_eq_zero
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l) :
    (sourceHaarActualOriginalInput S).sourceHullVolume ()
      (sourceHaarActualImageRealization S) n = 0 := by
  unfold sourceHullVolume sourceSetVolume sourcePointVolume
  refine le_antisymm ?_ zero_le
  refine iSup_le fun x => iSup_le fun _hx => ?_
  exact le_of_eq (ENNReal.ofReal_eq_zero.mpr
    (sourceHaarActual_sourceLocalLogDegree_nonpos S n x))

/-- The signed hull volume of the concrete model is not finite: unsigned
finiteness does not give signed finiteness. -/
theorem sourceHaarActual_signedHullVolume_not_lt_top
    (S : SourceDefinition31Data.{ua} l) (n : ThetaPilotCarrier l) :
    ¬ sourceSetVolumeSigned (sourceHaarActualOriginalInput S) ()
      (sourceHaarActualHull S n) < ⊤ := by
  intro h
  exact sourceHaarActual_hull_not_lowerBounded S n
    (hullDegreeLowerBound_of_signedHullVolume_lt_top
      (sourceHaarActualOriginalInput S) () h)

end Concrete

/-! ## 6. Signed gap-2 data with the finite image union as hull

The original `SignedGap2SourceData.hull_logDegree_ge` is satisfiable when the
hull is the finite image union, by Section 2.  The remaining two fields are
satisfied by the degenerate choices `scaledUnit = hull` and
`point = 1`.  This is an actual inhabitant of the interface, not a
construction of the paper's geometric hull. -/

section SignedGap2

variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- **An actual `SignedGap2SourceData` inhabitant.**  The hull is the finite
theta-pilot image union (so `hull_logDegree_ge` is the unconditional
finite-minimum theorem), the scaled unit is the same set, and the point is the
monoid unit.  The structure is therefore not empty; the gap is the geometric
identification of these fields with the paper's hull and scaled region. -/
theorem signedGap2SourceData_imageUnion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    SignedGap2SourceData (I := I) (v := v)
      (hull := I.possibleThetaPilotImageSet v R n)
      (scaledUnit := fun _ _ _ => I.possibleThetaPilotImageSet v R n)
      (point := fun _ _ _ => (1 : I.ThetaPilotPoint v))
      (eps := 0) (D0 := 0) (D1 := 0) := by
  refine
    { hull_logDegree_ge := ?_
      scaledUnit_le_hull := ?_
      point_logDegree_le := ?_ }
  · simpa [HullDegreeLowerBound] using
      hullDegreeLowerBound_possibleThetaPilotImageSet I v R n
  · intro a b c _habc
    simp
  · intro a b c _habc
    simpa [I.sourceLocalLogDegree_one v] using
      (arithmeticWeight_nonneg (abcRationalPoint a c))

end SignedGap2

/-! ## 7. Axiom probes -/

#print axioms hullDegreeLowerBound_possibleThetaPilotImageSet
#print axioms hullDegreeLowerBound_scaledRegionImage
#print axioms hullDegreeLowerBound_sourceHolomorphicHull_of_compactness
#print axioms hullDegreeLowerBound_iff_signedHullVolume_lt_top
#print axioms not_hullDegreeLowerBound_sourceHolomorphicHull_of_degreeFaithful
#print axioms sourceHaarActual_hull_not_lowerBounded
#print axioms exists_sourceOneCircUCompactness_not_hullDegreeLowerBound
#print axioms not_forall_sourceScalingUnits_logDegree_nonneg_of_degreeFaithful
#print axioms sourceHaarActual_strictPoint_mem_sourceScalingUnits
#print axioms sourceHaarActual_scaling_nonneg_false
#print axioms sourceHaarActual_unsignedHullVolume_eq_zero
#print axioms sourceHaarActual_signedHullVolume_not_lt_top
#print axioms sourceHaarActual_bridgeUnitRegion_not_lowerBounded
#print axioms signedGap2SourceData_imageUnion

end LeanFormal.IUT.XiFPaper.S2664HullLowerAuditActual
