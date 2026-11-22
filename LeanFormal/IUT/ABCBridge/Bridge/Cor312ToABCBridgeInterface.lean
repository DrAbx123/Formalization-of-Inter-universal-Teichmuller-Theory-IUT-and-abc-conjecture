import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Bridge.ThetaBoundToHeightWeight
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

/-!
  # Conditional bridge from IUT III Corollary 3.12 to the ABC height form

  This module freezes, at exact fidelity, the formal implication that the pending
  obligation `cor312ToABCBridge` of `ABCBridge/Bridge/IUTToABC.lean` stands for:
  from

  (a) the paper-level hull/finiteness interface of IUT III Corollary 3.12 (the
      `IQHullLogVolumeInterface` of
      `Corollary312/StepXI/HolomorphicHull/SourceHullCompactnessReduction.lean`,
      whose finiteness theorem `hull_logVolume_lt_top` is proved there) together
      with the θ-pilot volume data of the comparison, and
  (b) the actual rational-point dictionary (`RationalPointDictionary.lean`,
      `RationalPrimeSupport.lean`),

  derive the ABC-style height bound in exactly the form of the right-hand side of
  `abcConjecture_iff_abcArithmeticWeightHeightBound` (`IUTToABC.lean`):

  `∀ ε > 0, ∃ A, ∀ a b c, IsABCTriple a b c →
     Height.logHeight₁ (abcRationalPoint a c) ≤
       (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A`.

  ## Role of the two accepted inputs

  * The hull side enters as `IQHullLogVolumeInterface` (`Cor312ToABCBridgeInterface.hullData`):
    its hull log-volume is finite by the already-proved `hull_logVolume_lt_top`, so
    the real number `(logVolume hull).toReal` is a faithful θ-pilot bound
    (`hullLogVolume_ofReal_toReal`).  In the paper this bound is the content of
    Corollary 3.12 (finiteness of `−|log(Θ)|`); the value-monoid realization here is
    the one of Herschel's files, and it is *not* claimed to be the literal
    `IQ(S±_{j+1}; n,◦D^vdash_{vQ})` carrier — see the audit note of
    `SourceHullCompactnessReduction.lean`.
  * The equivalence `abcConjecture_iff_abcArithmeticWeightHeightBound` and the
    dictionary identities `abcRationalPoint_logHeight₁`,
    `radical_log_eq_arithmeticWeight` are the accepted arithmetic facts used below.

  ## What is proved and what is only named

  Everything below is proved: the per-`ε` factor absorption (in
  `ThetaBoundToHeightWeight.lean`), the assembly of the height bound from the named
  comparison data, the conditional derivation of `ABCConjecture` (via the accepted
  equivalence), the multiplicative `rpow` form (via
  `logLeIffLeExpMulRpow`), the unboundedness of the height of ABC rational points,
  and the strength calibration `Nonempty Cor312ToABCBridgeInterface ↔ ABCConjecture`.

  The comparison region is no longer an abstract field: for the carrier's unit
  region and paper scaling (`IQHullLogVolumeInterface.unitRegion`, `.scaleShift`;
  Remark 3.9.5) and the named point datum `logShellPoint a b c` (the image of
  `x = a/c` in the carrier), the region is the concrete Set-level construction
  `normalizedComparisonRegion`:

  `W.scaleShift '' (W.unitRegion ∪ {logShellPoint a b c})`.

  The point datum is forced to vary with the triple: a triple-independent region
  has fixed log-volume while heights are unbounded
  (`no_constantRegion_heightComparison`).

  Exactly two still-unproved paper links remain; each is an explicit named field
  (gap) of `Cor312EpsilonArithmeticComparison`, nothing unproved is hidden behind a
  placeholder declaration, and no unproved field is used as a foundation:

  * `height_le_normalizedRegionVolume` (gap): the `ε`-normalized comparison of the
    logarithmic height with the log-volume of the comparison region of `x = a/c`
    (IUT IV arithmetic line-bundle comparison; not formalized here);
  * `regionVolume_le_normalizedWeight` (gap): the `ε`-normalized log-volume
    computation of that region, with the θ-pilot contribution bounded by the
    ambient hull log-volume and a residual constant (IUT IV main estimate,
    conditional on the Corollary 3.12 finiteness; not formalized here).

  Finiteness of the region log-volume is *derived* rather than assumed: it follows
  from the height comparison as
  `Cor312EpsilonArithmeticComparison.comparisonRegion_logVolume_lt_top`.

  ## Why no hull containment of the comparison region is imposed

  Heights of ABC rational points are unbounded
  (`abcRationalPoint_logHeight_unbounded`), whereas the hull has finite log-volume
  (`hull_logVolume_lt_top`).  Hence no interface of the shape "region inside the
  finite hull and height ≤ region volume" can exist: this is proved as
  `no_heightDictionary_into_finiteHull`.  In the paper the Corollary 3.12
  finiteness enters the *additive constant* of the comparison, not the containment
  of the point's region; the interface below is shaped accordingly.

  ## Strength

  `cor312ToABCBridgeInterface_nonempty_iff_abcConjecture` shows that the interface
  package has exactly the strength of `ABCConjecture`: from any inhabitant the
  height bound (and hence `ABCConjecture`) follows, and conversely `ABCConjecture`
  yields an inhabitant.  Consequently this module does **not** prove Corollary
  3.12, does not prove the IUT IV estimate, and does not prove ABC; it proves only
  the conditional reduction and its calibrated equivalence.  The comparison region
  is realized concretely on the paper-level carrier interface, but the carrier
  itself remains the named data interface `IQHullLogVolumeInterface` (not claimed
  to be the literal paper inductive system), and the two analytic comparisons of
  IUT IV remain the two named gaps.
-/

namespace LeanFormal.IUT

noncomputable section

universe u

/-! ## 1. Arithmetic bookkeeping for the constants -/

/-- The arithmetic weight of a rational number is nonnegative: it is a sum of
`Real.log p` over prime factors `p ≥ 2`. -/
theorem arithmeticWeight_nonneg (x : Rat) : 0 ≤ arithmeticWeight x := by
  unfold arithmeticWeight
  refine Finset.sum_nonneg fun p hp => Real.log_nonneg ?_
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
    · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
  · exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le

/-- The θ-pilot bound `(logVolume hull).toReal` is faithful: the hull log-volume of
a paper-level hull interface is exactly the `ENNReal.ofReal` of that real number.
This is the concrete use of the Corollary 3.12 finiteness theorem
`IQHullLogVolumeInterface.hull_logVolume_lt_top`. -/
theorem hullLogVolume_ofReal_toReal {X : Type u} (W : IQHullLogVolumeInterface X) :
    ENNReal.ofReal (W.logVolume W.hull).toReal = W.logVolume W.hull :=
  ENNReal.ofReal_toReal (ne_of_lt W.hull_logVolume_lt_top)

/-! ## 2. Unboundedness of the heights and the no-containment obstruction -/

/-- The logarithmic heights of the rational points attached to ABC triples are
unbounded above: the triples `(1, n, n + 1)` are primitive additive triples and
their heights are `Real.log (n + 1)`. -/
theorem abcRationalPoint_logHeight_unbounded (C : Real) :
    ∃ a b c : Nat, IsABCTriple a b c ∧
      C < Height.logHeight₁ (abcRationalPoint a c) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp C)
  have hnpos : 0 < n := by
    exact_mod_cast (lt_trans (Real.exp_pos C) hn : (0 : Real) < (n : Real))
  have htriple : IsABCTriple 1 n (n + 1) :=
    ⟨Nat.one_pos, hnpos, Nat.add_comm 1 n, Nat.coprime_one_left n⟩
  refine ⟨1, n, n + 1, htriple, ?_⟩
  rw [abcRationalPoint_logHeight₁ htriple]
  exact (Real.lt_log_iff_exp_lt (by exact_mod_cast Nat.succ_pos n)).mpr
    (by push_cast; linarith)

/-- **No-containment obstruction.**  There is no height dictionary of the shape
"the comparison region of `x = a/c` lies in the θ-pilot hull and the height is
bounded by the region log-volume": the hull has finite log-volume
(`IQHullLogVolumeInterface.hull_logVolume_lt_top`), so such a dictionary would
bound all heights by the fixed constant `(logVolume hull).toReal`, contradicting
`abcRationalPoint_logHeight_unbounded`.  This is why the per-`ε` comparison
structure below routes the Corollary 3.12 bound through the additive constant
instead of through containment. -/
theorem no_heightDictionary_into_finiteHull {X : Type u} (W : IQHullLogVolumeInterface X)
    (hfin : W.logVolume W.hull < ⊤)
    (region : Nat → Nat → Nat → Set X)
    (hsub : ∀ a b c : Nat, IsABCTriple a b c → region a b c ⊆ W.hull) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        ENNReal.ofReal (Height.logHeight₁ (abcRationalPoint a c)) ≤
          W.logVolume (region a b c)) := by
  intro h
  have hbound : ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤ (W.logVolume W.hull).toReal := by
    intro a b c habc
    have h1 := h a b c habc
    have h2 := W.logVolume_mono (hsub a b c habc)
    have h3 : ENNReal.ofReal (Height.logHeight₁ (abcRationalPoint a c)) ≤
        ENNReal.ofReal (W.logVolume W.hull).toReal := by
      rw [ENNReal.ofReal_toReal (ne_of_lt hfin)]
      exact le_trans h1 h2
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h3
  obtain ⟨a, b, c, habc, hgt⟩ :=
    abcRationalPoint_logHeight_unbounded (W.logVolume W.hull).toReal
  exact not_lt_of_ge (hbound a b c habc) hgt

/-- **No-constant-region obstruction.**  No triple-independent comparison region can
support the height comparison: the heights of the ABC points are unbounded
(`abcRationalPoint_logHeight_unbounded`), while `(1 + ε) · (logVolume R).toReal` is a
fixed constant.  This is why the concrete comparison region
`normalizedComparisonRegion` retains the named point datum `logShellPoint`: the
region must vary with the triple. -/
theorem no_constantRegion_heightComparison {X : Type u} (W : IQHullLogVolumeInterface X)
    (R : Set X) (epsilon : Real) :
    ¬ (∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) ≤
          (1 + epsilon) * (W.logVolume R).toReal) := by
  intro h
  obtain ⟨a, b, c, habc, hgt⟩ :=
    abcRationalPoint_logHeight_unbounded ((1 + epsilon) * (W.logVolume R).toReal)
  exact not_lt_of_ge (h a b c habc) hgt

/-! ## 3. The per-`ε` arithmetic comparison data -/

/-- The concrete Set-level comparison region of the per-`ε` comparison, built from
the paper-level carrier data (`IQHullLogVolumeInterface.unitRegion`,
`IQHullLogVolumeInterface.scaleShift`; Remark 3.9.5) together with the named point
datum `logShellPoint a b c`: paper: the `ε`-thickened comparison region of the point,
realized as the `λ`-multiple of the log-shell together with the point. -/
def normalizedComparisonRegion {X : Type u} (W : IQHullLogVolumeInterface X)
    (logShellPoint : Nat → Nat → Nat → X) (a b c : Nat) : Set X :=
  W.scaleShift '' (W.unitRegion ∪ {logShellPoint a b c})

/-- The per-`ε` data of the arithmetic comparison step that converts the IUT III
Corollary 3.12 θ-pilot log-volume finiteness into the ABC height bound.

The comparison region of `x = a/c` is the concrete Set-level construction
`normalizedComparisonRegion W logShellPoint a b c` — the `λ`-multiple of the
log-shell `O` together with the image point of the triple — so the only datum left
to the inhabitant is the named paper point `logShellPoint`.  The point cannot be
dropped: a triple-independent region has fixed log-volume while heights are
unbounded (`no_constantRegion_heightComparison`).

The two remaining fields are the two still-unformalized paper links (gaps): the
`ε`-normalized comparison of the height with the region log-volume and the
`ε`-normalized computation of that log-volume.  The identifications
`Height.logHeight₁ (abcRationalPoint a c) = log c` and
`arithmeticWeight (abcRationalPoint a c) = log(radical (a * b * c))` are the
accepted dictionary facts of `RationalPointDictionary.lean` and
`RationalPrimeSupport.lean`.  Finiteness of the region log-volume is not assumed:
it is derived from the height comparison as
`Cor312EpsilonArithmeticComparison.comparisonRegion_logVolume_lt_top`. -/
structure Cor312EpsilonArithmeticComparison {X : Type u} (W : IQHullLogVolumeInterface X)
    (epsilon : Real) where
  /-- **Named paper datum (data, not a gap).**  The point of the ambient carrier
  attached to the rational point `x = a/c` (paper: the element of the carrier whose
  log-volume/local degree is compared with the height).  No claim about it is
  assumed beyond the two gap fields below. -/
  logShellPoint : Nat → Nat → Nat → X
  /-- **Gap 1: height comparison (paper link, not formalized).**  The logarithmic
  height of `x = a/c` is bounded by `(1 + ε)` times the log-volume of its concrete
  comparison region `scaleShift '' (unitRegion ∪ {logShellPoint a b c})` — the
  `ε`-normalized comparison of the height with the log-volume of the arithmetic
  line bundle (IUT IV §2). -/
  height_le_normalizedRegionVolume : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) *
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal
  /-- **Gap 2: log-volume computation (paper link, not formalized).**  The
  `ε`-normalized region log-volume is bounded by `(1 + ε)` times the arithmetic
  weight of `x = a/c`, plus the θ-pilot bound `(logVolume hull).toReal` (faithful as
  a real number by `hullLogVolume_ofReal_toReal`, and finite by the Corollary 3.12
  finiteness theorem) plus a residual per-`ε` constant `D` independent of the
  triple.  This is the shape of the main log-volume estimate of IUT IV §2 in which
  the Corollary 3.12 boundedness of `−|log(Θ)|` and the finite-prime data are
  absorbed. -/
  regionVolume_le_normalizedWeight : ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D

/-- The concrete comparison region as an accessor on the comparison data: the
`λ`-multiple of the log-shell together with the named point.  (The name is kept so
that statements written against the former field read unchanged.) -/
def Cor312EpsilonArithmeticComparison.comparisonRegion {X : Type u}
    {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon) (a b c : Nat) : Set X :=
  normalizedComparisonRegion W C.logShellPoint a b c

/-- **Derived region finiteness** (formerly a field of the structure).  On every ABC
triple the comparison-region log-volume is finite: if it were `⊤`, gap 1 would read
`log c ≤ (1 + ε) · 0 = 0`, contradicting `0 < log c` on the (positive) ABC triple.
No containment of the region in the hull is used or available — see
`no_heightDictionary_into_finiteHull` — so this is the only route to finiteness at
this interface level. -/
theorem Cor312EpsilonArithmeticComparison.comparisonRegion_logVolume_lt_top
    {X : Type u} {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon) :
    ∀ a b c : Nat, IsABCTriple a b c → W.logVolume (C.comparisonRegion a b c) < ⊤ := by
  intro a b c habc
  have hregion : C.comparisonRegion a b c =
      normalizedComparisonRegion W C.logShellPoint a b c := rfl
  rw [hregion, lt_top_iff_ne_top]
  intro htop
  have hle := C.height_le_normalizedRegionVolume a b c habc
  rw [htop, ENNReal.toReal_top, mul_zero] at hle
  have hc : 1 < c := by
    obtain ⟨ha, hb, hsum, _⟩ := habc
    omega
  have hpos : 0 < Height.logHeight₁ (abcRationalPoint a c) := by
    rw [abcRationalPoint_logHeight₁ habc]
    exact Real.log_pos (by exact_mod_cast hc)
  exact absurd hle (not_le.mpr hpos)

/-- Under the derived region finiteness `comparisonRegion_logVolume_lt_top`, the
region log-volume is the `ENNReal.ofReal` of its `toReal` value: the `.toReal`
presentation of the comparison fields is faithful to the `ENNReal` hull
interface. -/
theorem cor312ComparisonRegionVolume_ofReal_toReal {X : Type u}
    {W : IQHullLogVolumeInterface X} {epsilon : Real}
    (C : Cor312EpsilonArithmeticComparison W epsilon) {a b c : Nat}
    (habc : IsABCTriple a b c) :
    ENNReal.ofReal (W.logVolume (C.comparisonRegion a b c)).toReal =
      W.logVolume (C.comparisonRegion a b c) :=
  ENNReal.ofReal_toReal (ne_of_lt (C.comparisonRegion_logVolume_lt_top a b c habc))

/-! ## 3b. Versioned additive comparison data (re-freeze 2026-10-16, contract v2)

The height field `height_le_normalizedRegionVolume` of
`Cor312EpsilonArithmeticComparison` was only instantiable through the uniform
valuation bound of `ABCHeightArithmeticWeightComparison.lean`, which is refuted
(probe `H1UniformValuationBoundCounterexampleProbe.lean`,
`no_oneAdd_valuation_bound`; witness family `(1, 2^k − 1, 2^k)`).  The versioned
structure below keeps the same named point datum, the same concrete region
`normalizedComparisonRegion`, and the same log-volume-computation field, and moves
only the height comparison to the IUT IV Theorem A shape
`height ≤ (1 + ε) · regionVolume + A` with an explicit additive constant `A`
(the approved global additive re-freeze; contract `ABCHeightWeightAdditiveBoundV2`
of `ABCHeightArithmeticWeightComparison.lean`, matching
`cor312ToABCBridge_heightBound`/`abcConjecture_iff_abcArithmeticWeightHeightBound`).
The multiplicative structure is retained unchanged: both versions coexist and no
old declaration is deleted or re-stated. -/

/-- **Version-2 (additive) per-`ε` comparison data.**  Same point datum and region
as `Cor312EpsilonArithmeticComparison`; the height comparison carries the explicit
additive constant `A` (IUT IV Theorem A, bounded-discrepancy form), while the
log-volume computation keeps its (unchanged) shape. -/
structure Cor312EpsilonArithmeticComparisonAdditive {X : Type u}
    (W : IQHullLogVolumeInterface X) (epsilon A : Real) where
  /-- The named paper datum: the image point of `x = a/c` in the carrier (same
  role as in `Cor312EpsilonArithmeticComparison`). -/
  logShellPoint : Nat → Nat → Nat → X
  /-- **Additive height comparison (version-2 shape).**  `logHeight₁ x` is bounded
  by `(1 + ε)` times the comparison-region log-volume plus the constant `A`. -/
  height_le_normalizedRegionVolume_add : ∀ a b c : Nat, IsABCTriple a b c →
    Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) *
        (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal + A
  /-- **Log-volume computation (unchanged shape).**  Identical to the
  corresponding field of `Cor312EpsilonArithmeticComparison`. -/
  regionVolume_le_normalizedWeight : ∃ D : Real, ∀ a b c : Nat, IsABCTriple a b c →
    (W.logVolume (normalizedComparisonRegion W logShellPoint a b c)).toReal ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (W.logVolume W.hull).toReal + D
/-- **Consumption of the additive comparison family: contract v2 out.**  A
carrier implementation `W` whose version-2 additive comparison data
`Cor312EpsilonArithmeticComparisonAdditive W epsilon (Aeps epsilon)` is supplied
for every `epsilon > 0`, each instance carrying its own named point datum and
comparison region, yields the
approved global additive contract `ABCHeightWeightAdditiveBoundV2`
(`ABCHeightArithmeticWeightComparison.lean`), i.e. the exact IUT IV Theorem A
shape `∀ ε > 0, ∃ A, ∀ abc, logHeight ≤ (1 + ε) · weight + A`.  The proof
reuses the proved factor absorption
`heightWeightBound_of_normalizedVolumeComparison` by shifting the per-`epsilon`
additive constant into the recorded volume; no arithmetic content beyond the
two structure fields is used. -/
theorem abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditive {X : Type u}
    (W : IQHullLogVolumeInterface X)
    (Aeps : Real → Real)
    (hcomp : ∀ epsilon : Real, 0 < epsilon →
      Cor312EpsilonArithmeticComparisonAdditive W epsilon (Aeps epsilon)) :
    ABCHeightWeightAdditiveBoundV2 := by
  refine heightWeightBound_of_normalizedVolumeComparison
    (P := IsABCTriple)
    (height := fun a b c => Height.logHeight₁ (abcRationalPoint a c))
    (weight := fun a b c => arithmeticWeight (abcRationalPoint a c))
    (volume := fun delta hdelta a b c =>
      (W.logVolume
          (normalizedComparisonRegion W (hcomp delta hdelta).logShellPoint a b c)).toReal +
        Aeps delta / (1 + delta))
    (thetaBound := (W.logVolume W.hull).toReal)
    (hweight_nonneg := fun a b c _ => arithmeticWeight_nonneg _)
    (hcomparison := fun delta hdelta => ?_)
  constructor
  · intro a b c habc
    have hdelta_ne : (1 + delta : Real) ≠ 0 := ne_of_gt (by linarith)
    calc Height.logHeight₁ (abcRationalPoint a c)
        ≤ (1 + delta) *
            (W.logVolume
                (normalizedComparisonRegion W (hcomp delta hdelta).logShellPoint
                  a b c)).toReal +
            Aeps delta :=
          (hcomp delta hdelta).height_le_normalizedRegionVolume_add a b c habc
      _ = (1 + delta) *
            ((W.logVolume
                (normalizedComparisonRegion W (hcomp delta hdelta).logShellPoint
                  a b c)).toReal +
              Aeps delta / (1 + delta)) := by
          rw [mul_add, mul_div_cancel₀ _ hdelta_ne]
  · obtain ⟨D, hD⟩ := (hcomp delta hdelta).regionVolume_le_normalizedWeight
    refine ⟨D + Aeps delta / (1 + delta), fun a b c habc => ?_⟩
    calc (W.logVolume
            (normalizedComparisonRegion W (hcomp delta hdelta).logShellPoint
              a b c)).toReal + Aeps delta / (1 + delta)
        ≤ ((1 + delta) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal + D) + Aeps delta / (1 + delta) :=
          add_le_add (hD a b c habc) (le_refl (Aeps delta / (1 + delta)))
      _ = (1 + delta) * arithmeticWeight (abcRationalPoint a c) +
            (W.logVolume W.hull).toReal +
            (D + Aeps delta / (1 + delta)) := by
          ring

/-! ## 4. The bridge interface package -/

/-- The complete conditional input of the Corollary 3.12 → ABC bridge: an ambient
carrier with its paper-level hull/log-volume interface `hullData` (the role of
`IQ(S±_{j+1}; n,◦D^vdash_{vQ})` with its Haar log-volume, as named by
`SourceHullCompactnessReduction.lean`), together with the per-`ε` arithmetic
comparison data (concrete comparison region on the carrier with two named gaps).
The interface is inhabited if and only if `ABCConjecture` holds
(`cor312ToABCBridgeInterface_nonempty_iff_abcConjecture`), so it exposes exactly
the unproved arithmetic content and nothing more. -/
structure Cor312ToABCBridgeInterface where
  /-- The ambient carrier of the paper-level hull interface. -/
  carrier : Type u
  /-- The hull/finiteness interface of IUT III Corollary 3.12. -/
  hullData : IQHullLogVolumeInterface carrier
  /-- The per-`ε` arithmetic comparison data. -/
  epsilonComparison : ∀ epsilon : Real, 0 < epsilon →
    Cor312EpsilonArithmeticComparison hullData epsilon

/-! ## 5. The conditional bridge theorem and its consequences -/

/-- **The conditional Cor 3.12 → ABC bridge.**  From the bridge interface, derive
the ABC-style height-bound statement in exactly the form of the right-hand side of
`abcConjecture_iff_abcArithmeticWeightHeightBound`: for every `ε > 0` there is a
constant `A` depending only on `ε` (and on the interface data) with
`Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + ε) * arithmeticWeight (abcRationalPoint a c) + A`
on all ABC triples.

The proof consumes the `δ`-normalized comparison fields at `δ = min 1 (ε / 3)` and
re-absorbs the two `(1 + δ)` losses through
`heightWeightBound_of_normalizedVolumeComparison`.  No unconditional closure is
claimed: the comparison fields are the unproved paper links. -/
theorem cor312ToABCBridge_heightBound (D : Cor312ToABCBridgeInterface) :
    ∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) ≤
        (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A := by
  refine heightWeightBound_of_normalizedVolumeComparison
    (P := IsABCTriple)
    (height := fun a b c => Height.logHeight₁ (abcRationalPoint a c))
    (weight := fun a b c => arithmeticWeight (abcRationalPoint a c))
    (volume := fun delta hdelta a b c =>
      (D.hullData.logVolume ((D.epsilonComparison delta hdelta).comparisonRegion a b c)).toReal)
    (thetaBound := (D.hullData.logVolume D.hullData.hull).toReal)
    (hweight_nonneg := fun a b c _ => arithmeticWeight_nonneg _)
    (hcomparison := fun delta hdelta =>
      ⟨(D.epsilonComparison delta hdelta).height_le_normalizedRegionVolume,
        (D.epsilonComparison delta hdelta).regionVolume_le_normalizedWeight⟩)

/-- Under the bridge interface, `ABCConjecture` holds, by the accepted equivalence
`abcConjecture_iff_abcArithmeticWeightHeightBound` and
`cor312ToABCBridge_heightBound`.  This is a conditional closure through the named
unproved comparison fields; it does not prove them. -/
theorem cor312ToABCBridge_abcConjecture (D : Cor312ToABCBridgeInterface) :
    ABCConjecture :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.mpr
    (cor312ToABCBridge_heightBound D)

/-- Under the bridge interface, the logarithmic form `ABCLogConjecture` holds, by
the accepted equivalence `abcConjecture_iff_abcLogConjecture`. -/
theorem cor312ToABCBridge_abcLogConjecture (D : Cor312ToABCBridgeInterface) :
    ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp (cor312ToABCBridge_abcConjecture D)

/-- Under the bridge interface, the standard radical-power form holds: for every
`ε > 0` there is `K > 0` with `c ≤ K * radical (a * b * c) ^ (1 + ε)` on ABC
triples, obtained from the height bound through the accepted per-`ε` equivalence
`logLeIffLeExpMulRpow`. -/
theorem cor312ToABCBridge_rpowBound (D : Cor312ToABCBridgeInterface) :
    ∀ epsilon : Real, 0 < epsilon → ∃ K : Real, 0 < K ∧
      ∀ a b c : Nat, IsABCTriple a b c →
        (c : Real) ≤ K * (radical (a * b * c) : Real) ^ (1 + epsilon) := by
  intro epsilon hepsilon
  obtain ⟨A, hA⟩ := cor312ToABCBridge_heightBound D epsilon hepsilon
  refine ⟨Real.exp A, Real.exp_pos A, ?_⟩
  intro a b c habc
  have hc : (0 : Real) < (c : Real) := abcTriple_c_pos habc
  have hr : (0 : Real) < (radical (a * b * c) : Real) := radical_cast_pos a b c
  have hlog : Real.log (c : Real) ≤
      (1 + epsilon) * Real.log (radical (a * b * c) : Real) + A := by
    have h := hA a b c habc
    rw [abcRationalPoint_logHeight₁ habc, ← radical_log_eq_arithmeticWeight habc] at h
    exact h
  exact (logLeIffLeExpMulRpow hc hr).mp hlog

/-! ## 6. Strength calibration: the interface is equivalent to `ABCConjecture`

The consistency witness below uses the real line with the supremum log-volume
`realLineLogVolume S = ⨆ x ∈ S, ofReal x`; it is a check on the *strength* of the
interface package only, not a model of the paper's carrier.  It shows that the
interface is satisfiable exactly when ABC holds, i.e. it contains exactly the
unproved arithmetic content. -/

/-- The sup-of-`ofReal` log-volume functional on the real line, used only for the
strength-calibration witness. -/
noncomputable def realLineLogVolume (S : Set Real) : ENNReal :=
  ⨆ x ∈ S, ENNReal.ofReal x

theorem realLineLogVolume_mono {S T : Set Real} (hST : S ⊆ T) :
    realLineLogVolume S ≤ realLineLogVolume T :=
  iSup_le fun x => iSup_le fun hx => le_iSup_of_le x (le_iSup_of_le (hST hx) le_rfl)

theorem realLineLogVolume_singleton (y : Real) :
    realLineLogVolume ({y} : Set Real) = ENNReal.ofReal y := by
  refine le_antisymm (iSup_le fun x => iSup_le fun hx => ?_)
    (le_iSup_of_le y (le_iSup_of_le rfl le_rfl))
  obtain rfl : x = y := Set.mem_singleton_iff.mp hx
  exact le_rfl

theorem realLineLogVolume_empty : realLineLogVolume (∅ : Set Real) = 0 :=
  le_antisymm (iSup_le fun _ => iSup_le fun hx => False.elim hx) bot_le

/-- The sup-of-`ofReal` log-volume of the two-point set `{0, r}` with `0 ≤ r` is
`ofReal r`: the value at the nonnegative point dominates.  Used to compute the
comparison region of the calibration witness below. -/
theorem realLineLogVolume_pair_zero {r : Real} (hr : 0 ≤ r) :
    realLineLogVolume ({0, r} : Set Real) = ENNReal.ofReal r := by
  refine le_antisymm (iSup_le fun x => iSup_le fun hx => ?_)
    (le_iSup_of_le r (le_iSup_of_le (by simp) le_rfl))
  rcases (show x = 0 ∨ x = r from by simpa using hx) with rfl | rfl
  · rw [ENNReal.ofReal_zero]
    exact zero_le
  · exact le_rfl

/-- A paper-level hull interface on the real line for the calibration witness:
empty image union and hull, the unit region `{0}`, identity scaling, and the
sup-of-`ofReal` log-volume.  This satisfies the hull/finiteness interface but is
deliberately not a model of the paper's carrier. -/
noncomputable def realLineHullData : IQHullLogVolumeInterface Real where
  imageSet := ∅
  hull := ∅
  imageSet_subset_hull := Set.empty_subset _
  logVolume := realLineLogVolume
  logVolume_mono := fun hST => realLineLogVolume_mono hST
  unitRegion := {0}
  scaleShift := id
  hull_subset_scaleShift := Set.empty_subset _
  unitRegion_logVolume_lt_top := by
    rw [realLineLogVolume_singleton]
    exact ENNReal.ofReal_lt_top
  scaleShift_unitRegion_logVolume_le :=
    le_of_eq (congrArg realLineLogVolume (Set.image_id ({0} : Set Real)))

/-- `ABCConjecture` inhabits the bridge interface: the calibration direction
showing the interface is not stronger than ABC. -/
theorem cor312ToABCBridgeInterface_nonempty_of_abcConjecture (h : ABCConjecture) :
    Nonempty Cor312ToABCBridgeInterface.{0} := by
  refine ⟨{ carrier := Real
            hullData := realLineHullData
            epsilonComparison := ?_ }⟩
  intro epsilon hepsilon
  refine
    { logShellPoint := fun a b c => Real.log (c : Real)
      height_le_normalizedRegionVolume := ?_
      regionVolume_le_normalizedWeight := ?_ }
  · intro a b c habc
    have hc1 : (1 : Real) ≤ (c : Real) := by
      have h1 : 1 ≤ c := by
        obtain ⟨ha, hb, hsum, _⟩ := habc
        omega
      exact_mod_cast h1
    have hlogc : 0 ≤ Real.log (c : Real) := Real.log_nonneg hc1
    have hvol : realLineLogVolume (realLineHullData.scaleShift ''
        (realLineHullData.unitRegion ∪ {Real.log (c : Real)})) =
        ENNReal.ofReal (Real.log (c : Real)) := by
      change realLineLogVolume (id '' (({0} : Set Real) ∪ {Real.log (c : Real)})) =
        ENNReal.ofReal (Real.log (c : Real))
      rw [Set.image_id, Set.singleton_union]
      exact realLineLogVolume_pair_zero hlogc
    change Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) * (realLineLogVolume (realLineHullData.scaleShift ''
        (realLineHullData.unitRegion ∪ {Real.log (c : Real)}))).toReal
    rw [hvol, ENNReal.toReal_ofReal hlogc,
      abcRationalPoint_logHeight₁ habc]
    nlinarith [hepsilon.le, hlogc]
  · obtain ⟨A, hA⟩ :=
      (abcConjecture_iff_abcArithmeticWeightHeightBound.mp h) epsilon hepsilon
    refine ⟨max A 0, ?_⟩
    intro a b c habc
    have hc1 : (1 : Real) ≤ (c : Real) := by
      have h1 : 1 ≤ c := by
        obtain ⟨ha, hb, hsum, _⟩ := habc
        omega
      exact_mod_cast h1
    have hlogc : 0 ≤ Real.log (c : Real) := Real.log_nonneg hc1
    have hvol : realLineLogVolume (realLineHullData.scaleShift ''
        (realLineHullData.unitRegion ∪ {Real.log (c : Real)})) =
        ENNReal.ofReal (Real.log (c : Real)) := by
      change realLineLogVolume (id '' (({0} : Set Real) ∪ {Real.log (c : Real)})) =
        ENNReal.ofReal (Real.log (c : Real))
      rw [Set.image_id, Set.singleton_union]
      exact realLineLogVolume_pair_zero hlogc
    change (realLineLogVolume (realLineHullData.scaleShift ''
        (realLineHullData.unitRegion ∪ {Real.log (c : Real)}))).toReal ≤
      (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) +
        (realLineLogVolume (∅ : Set Real)).toReal + max A 0
    rw [hvol, ENNReal.toReal_ofReal hlogc,
      realLineLogVolume_empty, ENNReal.toReal_zero]
    have hA' := hA a b c habc
    rw [abcRationalPoint_logHeight₁ habc] at hA'
    linarith [le_max_left A 0]

/-- From an inhabitant of the bridge interface, `ABCConjecture` follows (the
calibration direction showing the interface is not weaker than ABC). -/
theorem cor312ToABCBridgeInterface_abcConjecture_of_nonempty
    (h : Nonempty Cor312ToABCBridgeInterface) : ABCConjecture :=
  abcConjecture_iff_abcArithmeticWeightHeightBound.mpr
    (cor312ToABCBridge_heightBound h.some)

/-- **Strength calibration.**  The bridge interface package is inhabited if and
only if `ABCConjecture` holds.  Hence the interface contains exactly the unproved
arithmetic content: the module proves the conditional reduction, not ABC. -/
theorem cor312ToABCBridgeInterface_nonempty_iff_abcConjecture :
    Nonempty Cor312ToABCBridgeInterface.{0} ↔ ABCConjecture :=
  ⟨cor312ToABCBridgeInterface_abcConjecture_of_nonempty,
   cor312ToABCBridgeInterface_nonempty_of_abcConjecture⟩

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the conditional Corollary 3.12 → ABC bridge interface of
`ABCBridge/Bridge/Cor312ToABCBridgeInterface.lean`.  The record documents the
proved conditional reduction and the explicit unproved paper links; it does not
assert that Corollary 3.12, the IUT IV estimate, or ABC has been proved. -/
def cor312ToABCBridgeInterfaceObligation : Obligation :=
  { id := "IUT-III.cor312-to-ABC-conditional-interface"
    source :=
      "IUT III Corollary 3.12 (finiteness of the θ-pilot / log-volume hull); " ++
        "IUT IV §2 arithmetic line-bundle comparison; the pending marker " ++
        "`cor312ToABCBridge` of ABCBridge/Bridge/IUTToABC.lean"
    status := VerificationStatus.interface
    note :=
      "The conditional bridge from the paper-level Corollary 3.12 hull interface " ++
        "(IQHullLogVolumeInterface; hull log-volume finite by the proved " ++
        "hull_logVolume_lt_top) and the actual rational-point dictionary to the " ++
        "height form of abcConjecture_iff_abcArithmeticWeightHeightBound is " ++
        "frozen: the assembly, the conditional ABCConjecture derivation, the " ++
        "rpow form, the strength calibration `Nonempty interface <-> " ++
        "ABCConjecture`, and the derivation of the region-log-volume finiteness " ++
        "from the height comparison are proved; the comparison region is the " ++
        "concrete construction scaleShift '' (unitRegion union {logShellPoint " ++
        "a b c}) on the carrier, with the named point datum logShellPoint. NOT " ++
        "proved: the two per-epsilon comparison gaps (height <= (1+eps) * " ++
        "region log-volume; region log-volume <= (1+eps) * weight + hull bound " ++
        "+ D), the realization of the carrier by the literal paper inductive " ++
        "system, and any unconditional closure. The lemmas " ++
        "no_heightDictionary_into_finiteHull and " ++
        "no_constantRegion_heightComparison record that the Corollary 3.12 " ++
        "bound cannot enter through region containment or through a " ++
        "triple-independent region (heights are unbounded), only through the " ++
        "additive constant carried by a triple-dependent region."
    dependsOn :=
      [ "IUT-III.cor312-to-ABC",
        "IUT-III.corollary-3.12-iq-hull-log-volume-interface" ] }

end LeanFormal.IUT.Audit
