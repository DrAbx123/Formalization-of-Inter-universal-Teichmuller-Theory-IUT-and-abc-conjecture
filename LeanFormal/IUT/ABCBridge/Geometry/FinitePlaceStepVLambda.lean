import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVJInvariant
import LeanFormal.IUT.Foundations.Geometry.TateJInvariantNorm

set_option linter.unusedSectionVars false
/-!
# The Step (v) theta-pilot exponent attached to a local j-invariant

IUT IV Theorem 1.10 Step (v) (`IV.txt` L1640-L1662, L1715-L1740) takes
`λ = ord(q̲_{v_j}^{j²})` with `q̲ = q_v^{1/2l}` (IUT I, Example 3.2(iv)), so
`λ = j²·(-ord_v j_E)/(2l)` at a place of multiplicative reduction.  The
quantitative Step (v) bound depends only on this order (`FinitePlaceStepVAssembly`,
`FinitePlaceStepVJInvariant`), not on an actual Tate parameter.

This module records that exponent from the actual local j-invariant alone:

* `inverseJInvariantOrder J h`: the actual `v`-adic (DVR) order of `J⁻¹`, where
  `J` is the local image of `j_E` with `‖J‖ > 1`;
* `stepVLambda p label J l`: the normalized signed Step (v) exponent
  `j²·(-ord J)/(2l)`, in the value group `(1/e)ℤ` of the local field;
* `stepVRootOrder`, `stepVLambdaOrder` and `StepVRootOrderCard`: the integer
  form `j²·(ord J⁻¹/(2l))` and the arithmetic card `2l ∣ ord(J⁻¹)`, together
  with the exact-division and value-group lemmas
  (`e·stepVLambda = stepVLambdaOrder`); the extension form of the card is the
  cited `order_dvd_extension_iff_ramification` (`2l·e_K ∣ v_K(a)·e_L`).  No
  coprimality of the root order with `l` is assumed or needed; the card is
  exactly `2l ∣ e·ord(q)` because `e·ord(q) = ord(J⁻¹)`.
* `exists_stepV_normOrder_representative_of_stepVLambda`: the norm-order
  representative `ϖ` with `ord ϖ = stepVLambda`, obtained by citing
  `LocalRootNormRepresentative.exists_stepV_j_normOrder_representative`
  (not reproved);
* `arithmeticTuple_stepV_hull_le_paperBound_of_stepVLambda`: the actual-tuple
  Step (v) hull-volume bound of `FinitePlaceStepVJInvariant` with the exponent
  written explicitly as `stepVLambda`;
* `qSideSignedValueCondition`: the residual q-side source condition
  `qSigned = -|log q|` of the actual q-pilot, named so that any conditional
  reduction must consume it explicitly.

Boundary (honest):

* Only the theta side (volume upper bound) is treated.  The inequality is a
  signed real statement (`arithmeticTupleNormalizedLogVolume`); no `ENNReal`
  truncation is used.
* No actual Tate parameter, Tate uniformization, or Weierstrass isomorphism
  `E ≅ E_q` is constructed.  The q-side source identification of the actual
  q-pilot (`qSigned = -|log q|`, IUT III Theorem 3.11 (ii), workstream N5) is
  recorded below as the named condition `qSideSignedValueCondition` and is
  NOT proved in this file.
* Remaining N8 q-side gap list:
  1. actual q-pilot and its source identification with `-|log j_E|`
     (`qSideSignedValueCondition`; N5, IUT III Theorem 3.11 (ii));
  2. Kummer/Theta-pilot containment of the image of the theta-pilot in
     `q̲^{j²}·O` (the same source identification, not a standard fact);
  3. the procession-normalized averaging of the per-label Step (v) bound
     over `j` (IV L1745-L1783), which is not the per-label bound proved here
     (see guidance §12.23: consumer semantics must choose average vs max);
  4. the final real inequality with the paper constants (guidance §12.19
     proposed item 1), which is pure real analysis but not proved here.
* The norm-level fact `‖j‖·‖q‖ = 1` for a *given* Tate q-series is available
  in `LeanFormal.IUT.Foundations.Geometry.TateJInvariantNorm`
  (`TateCurvePadic.tateJInvariant_norm_mul_q_norm`); it does not produce a `q`
  for a given local j-invariant and is cited only at that norm level.
-/


namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm LeanFormal.IUT.LocalFieldIntegralUnits
open MeasureTheory

noncomputable section

universe u v w

/-! ## 1. The Step (v) exponent and its integer form -/

/-- The actual DVR order of `J⁻¹`, where `J` is the local image of the elliptic
curve's `j`-invariant with `‖J‖ > 1`.  This is `(v(J⁻¹)).toNat` in the actual
discrete valuation ring `Integers K` of the local field. -/
def inverseJInvariantOrder {K : Type*} [NormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Integers K)]
    (jValue : K) (largeNorm : 1 < ‖jValue‖) : ℕ :=
  (IsDiscreteValuationRing.addVal (Integers K)
    (LocalRootNormRepresentative.inverseJInteger jValue largeNorm)).toNat

/-- The normalized signed Step (v) exponent attached to the local j-invariant
`J` and the label `j`: `λ = j²·(-ord J)/(2l)`, i.e. `j²·ord(q)/(2l)` for the
q-pilot order `ord(q) = -ord(J)`.  This is an element of the normalized value
group `(1/e)ℤ`; its integer form is `stepVLambdaOrder`. -/
def stepVLambda (p : ℕ) {K : Type*} [Norm K] (label : ℕ) (jValue : K) (l : ℕ) : ℝ :=
  (label : ℝ) ^ 2 * (-localNormOrder p jValue) / (2 * l : ℕ)

/-- The integer Step (v) root order `ord(J⁻¹)/(2l)`, when it exists; it is the
DVR order of the `2l`-th norm-root representative of `J⁻¹`. -/
def stepVRootOrder {K : Type*} [NormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Integers K)]
    (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ) : ℤ :=
  (inverseJInvariantOrder jValue largeNorm : ℤ) / ((2 * l : ℕ) : ℤ)

/-- The integer Step (v) exponent `j²·(ord J⁻¹/(2l))`.  It is the DVR order of
the `j²`-th power of the `2l`-th norm-root representative; when the card
`StepVRootOrderCard` holds it is the exact integer quotient (no truncation). -/
def stepVLambdaOrder {K : Type*} [NormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Integers K)]
    (label : ℕ) (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ) : ℤ :=
  (label : ℤ) ^ 2 * stepVRootOrder jValue largeNorm l

/-- The Step (v) root-divisibility card: `2l ∣ ord(J⁻¹)`, equivalently
`2l ∣ e·ord(q)`.  No coprimality of the root order with `l` is assumed. -/
def StepVRootOrderCard {K : Type*} [NormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Integers K)]
    (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ) : Prop :=
  (2 * l) ∣ inverseJInvariantOrder jValue largeNorm

/-- The exact-division statement for the root order: multiplying the integer
root order `ord(J⁻¹)/(2l)` by `2l` recovers `ord(J⁻¹)` exactly if and only if
the divisibility card holds.  (For a positive divisor, truncated division
recovers the dividend exactly only when the division is exact.) -/
theorem stepVRootOrder_mul_eq_iff {K : Type*} [NormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Integers K)]
    (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ) :
    ((2 * l : ℕ) : ℤ) * stepVRootOrder jValue largeNorm l =
        (inverseJInvariantOrder jValue largeNorm : ℤ) ↔
      StepVRootOrderCard jValue largeNorm l := by
  unfold stepVRootOrder StepVRootOrderCard
  constructor
  · intro h
    exact Int.natCast_dvd_natCast.mp
      (dvd_iff_exists_eq_mul_right.mpr ⟨_, h.symm⟩)
  · intro h
    exact Int.mul_ediv_cancel' (Int.natCast_dvd_natCast.mpr h)

/-- The integer Step (v) exponent exists exactly when `2l` divides `ord(J⁻¹)`
cyclic: the root order is `ord(J⁻¹)/(2l)`. -/
theorem exists_stepVRootOrder_iff {K : Type*} [NormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Integers K)]
    (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ) :
    (∃ root : ℤ, ((2 * l : ℕ) : ℤ) * root =
        (inverseJInvariantOrder jValue largeNorm : ℤ)) ↔
      StepVRootOrderCard jValue largeNorm l := by
  unfold StepVRootOrderCard
  constructor
  · rintro ⟨root, hroot⟩
    exact Int.natCast_dvd_natCast.mp
      (dvd_iff_exists_eq_mul_right.mpr ⟨root, hroot.symm⟩)
  · intro hdvd
    exact ⟨_, Int.mul_ediv_cancel' (Int.natCast_dvd_natCast.mpr hdvd)⟩

/-- Under the divisibility card, the integer Step (v) exponent `stepVLambdaOrder`
multiplies by `2l` to `j²·ord(J⁻¹)` exactly. -/
theorem stepVLambdaOrder_mul_eq_of_card {K : Type*} [NormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Integers K)]
    (label : ℕ) (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ)
    (hcard : StepVRootOrderCard jValue largeNorm l) :
    ((2 * l : ℕ) : ℤ) * stepVLambdaOrder label jValue largeNorm l =
      (label : ℤ) ^ 2 * (inverseJInvariantOrder jValue largeNorm : ℤ) := by
  have hroot : ((2 * l : ℕ) : ℤ) * stepVRootOrder jValue largeNorm l =
      (inverseJInvariantOrder jValue largeNorm : ℤ) :=
    (stepVRootOrder_mul_eq_iff jValue largeNorm l).mpr hcard
  unfold stepVLambdaOrder
  calc
    ((2 * l : ℕ) : ℤ) * ((label : ℤ) ^ 2 * stepVRootOrder jValue largeNorm l)
        = (label : ℤ) ^ 2 *
            (((2 * l : ℕ) : ℤ) * stepVRootOrder jValue largeNorm l) := by ring
    _ = (label : ℤ) ^ 2 * (inverseJInvariantOrder jValue largeNorm : ℤ) := by rw [hroot]

/-- The integer Step (v) exponent exists as soon as the card holds. -/
theorem exists_stepVLambdaOrder_of_card {K : Type*} [NormedField K] [IsUltrametricDist K]
    [IsDiscreteValuationRing (Integers K)]
    (label : ℕ) (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ)
    (hcard : StepVRootOrderCard jValue largeNorm l) :
    ∃ lambda : ℤ, ((2 * l : ℕ) : ℤ) * lambda =
      (label : ℤ) ^ 2 * (inverseJInvariantOrder jValue largeNorm : ℤ) :=
  ⟨_, stepVLambdaOrder_mul_eq_of_card label jValue largeNorm l hcard⟩

/-! ## 2. The normalized value-group form of the exponent -/

/-- The normalized order of an inverse is the negative normalized order. -/
theorem localNormOrder_inv {F : Type*} [NormedField F] (p : ℕ) (x : F) :
    localNormOrder p x⁻¹ = -localNormOrder p x := by
  unfold localNormOrder
  rw [norm_inv, Real.log_inv]
  ring

/-- If the norms of `jValue` and `q` multiply to one (the norm-level Tate
relation `‖j‖·‖q‖ = 1`), then their normalized orders are opposite. -/
theorem localNormOrder_eq_neg_of_norm_mul_eq_one {F : Type*} [Norm F] (p : ℕ)
    (jValue q : F) (hprod : ‖jValue‖ * ‖q‖ = 1) :
    localNormOrder p q = -localNormOrder p jValue := by
  have hq : ‖q‖ = ‖jValue‖⁻¹ := eq_inv_of_mul_eq_one_right hprod
  unfold localNormOrder
  rw [hq, Real.log_inv]
  ring

/-- The normalized order `stepVLambda` written through the q-pilot order:
if a local parameter `q` satisfies the norm-level Tate relation
`‖J‖·‖q‖ = 1` (equivalently `ord q = -ord J`), then
`λ = j²·ord(q)/(2l)`.  The existence of such a `q` for the actual j-invariant
is not claimed; that is the q-side source condition (N5). -/
theorem stepVLambda_eq_qOrder_of_norm_mul_eq_one {F : Type*} [Norm F] (p : ℕ)
    (label : ℕ) (jValue q : F) (l : ℕ) (hprod : ‖jValue‖ * ‖q‖ = 1) :
    stepVLambda p label jValue l =
      (label : ℝ) ^ 2 * localNormOrder p q / (2 * l : ℕ) := by
  unfold stepVLambda
  rw [localNormOrder_eq_neg_of_norm_mul_eq_one p jValue q hprod]

/-- The signed q-side exponent is the negative of the Step (v) exponent: for a
`q` with `ord q = -ord J` (norm-level Tate relation),
`-λ = -j²·ord(q)/(2l)`.  This is the signed form of the `-λ` term of the
Step (v) bound; `ord q` is positive when `‖q‖ < 1`. -/
theorem neg_stepVLambda_eq_qOrder {F : Type*} [Norm F] (p : ℕ)
    (label : ℕ) (jValue q : F) (l : ℕ) (hprod : ‖jValue‖ * ‖q‖ = 1) :
    -stepVLambda p label jValue l =
      -((label : ℝ) ^ 2 * localNormOrder p q / (2 * l : ℕ)) := by
  rw [stepVLambda_eq_qOrder_of_norm_mul_eq_one p label jValue q l hprod]

section LocalFieldValueGroup

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
  [IsDiscreteValuationRing (Integers K)]

/-- The actual `inverseJInteger` is nonzero (it coerces to `J⁻¹`). -/
theorem inverseJInteger_ne_zero (jValue : K) (largeNorm : 1 < ‖jValue‖) :
    LocalRootNormRepresentative.inverseJInteger jValue largeNorm ≠ 0 := by
  have hj : jValue ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at largeNorm
    norm_num at largeNorm
  intro hzero
  have hfield : (jValue⁻¹ : K) = 0 := by
    have hcoe := congrArg (fun x : Integers K => (x : K)) hzero
    exact hcoe
  exact (inv_ne_zero hj) hfield

/-- The normalized order of the inverse `j`-invariant is its actual DVR order
divided by the ramification exponent: `ord(J⁻¹) = v(J⁻¹)/e`. -/
theorem localNormOrder_inverseJInteger (jValue : K) (largeNorm : 1 < ‖jValue‖) :
    localNormOrder p
        ((LocalRootNormRepresentative.inverseJInteger jValue largeNorm : Integers K) : K) =
      (inverseJInvariantOrder jValue largeNorm : ℝ) /
        (logShellRamificationExponent (K := K) (p := p) : ℝ) := by
  have hnonzero := inverseJInteger_ne_zero jValue largeNorm
  have hp_pos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hlogp : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one hp_pos (by
      exact_mod_cast (Fact.out : p.Prime).ne_one)
  have hram : (logShellRamificationExponent (K := K) (p := p) : ℝ) ≠ 0 := by
    exact_mod_cast (LocalFieldLogarithm.logShellRamificationExponent_pos
      (K := K) (p := p)).ne'
  unfold localNormOrder inverseJInvariantOrder
  rw [LocalRootNormRepresentative.norm_integer_eq_prime_rpow_neg_order
    (p := p) _ hnonzero, Real.log_rpow hp_pos]
  field_simp

/-- The negative normalized order of `J` is `ord(J⁻¹) = v(J⁻¹)/e`, expressed
entirely through the actual DVR order and the ramification exponent. -/
theorem neg_localNormOrder_eq_inverseJInvariantOrder_div
    (jValue : K) (largeNorm : 1 < ‖jValue‖) :
    -localNormOrder p jValue =
      (inverseJInvariantOrder jValue largeNorm : ℝ) /
        (logShellRamificationExponent (K := K) (p := p) : ℝ) := by
  rw [← localNormOrder_inv p jValue]
  change localNormOrder p
      ((LocalRootNormRepresentative.inverseJInteger jValue largeNorm : Integers K) : K) = _
  exact localNormOrder_inverseJInteger jValue largeNorm

/-- The normalized Step (v) exponent written through the actual DVR order of
`J⁻¹`: `λ = j²·(v(J⁻¹)/e)/(2l)`, i.e. an element of the normalized value group
`(1/e)ℤ`. -/
theorem stepVLambda_eq_order_div_ramification (label : ℕ)
    (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ) :
    stepVLambda p label jValue l =
      (label : ℝ) ^ 2 *
        ((inverseJInvariantOrder jValue largeNorm : ℝ) /
          (logShellRamificationExponent (K := K) (p := p) : ℝ)) / (2 * l : ℕ) := by
  unfold stepVLambda
  rw [neg_localNormOrder_eq_inverseJInvariantOrder_div jValue largeNorm]

/-- The integer Step (v) exponent cast to the reals is `j²·ord(J⁻¹)/(2l)`.
Under the card the division is exact, so the cast is the quotient. -/
theorem stepVLambdaOrder_cast_eq_div (label : ℕ)
    (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ) (hl : 0 < 2 * l)
    (hcard : StepVRootOrderCard jValue largeNorm l) :
    (stepVLambdaOrder label jValue largeNorm l : ℝ) =
      (label : ℝ) ^ 2 * (inverseJInvariantOrder jValue largeNorm : ℝ) /
        (2 * l : ℕ) := by
  have hspec := stepVLambdaOrder_mul_eq_of_card label jValue largeNorm l hcard
  have hcast : ((2 * l : ℕ) : ℝ) *
      (stepVLambdaOrder label jValue largeNorm l : ℝ) =
      (label : ℝ) ^ 2 * (inverseJInvariantOrder jValue largeNorm : ℝ) := by
    exact_mod_cast hspec
  have h2l_ne : ((2 * l : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hl)
  rw [eq_div_iff h2l_ne, mul_comm]
  exact hcast

/-- **Value-group statement:** under the card `2l ∣ ord(J⁻¹)`, the ramification
multiple of the normalized Step (v) exponent is exactly the integer
`stepVLambdaOrder = j²·(ord(J⁻¹)/(2l))`.  This says `e·λ ∈ ℤ`, i.e. `λ` lies in
the normalized value group `(1/e)ℤ` of the local field. -/
theorem ramification_mul_stepVLambda_eq_stepVLambdaOrder (label : ℕ)
    (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ) (hl : 0 < 2 * l)
    (hcard : StepVRootOrderCard jValue largeNorm l) :
    (logShellRamificationExponent (K := K) (p := p) : ℝ) *
        stepVLambda p label jValue l =
      (stepVLambdaOrder label jValue largeNorm l : ℝ) := by
  have hram_ne : (logShellRamificationExponent (K := K) (p := p) : ℝ) ≠ 0 := by
    exact_mod_cast (LocalFieldLogarithm.logShellRamificationExponent_pos
      (K := K) (p := p)).ne'
  have h2l_ne : ((2 * l : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hl)
  have hreal : (logShellRamificationExponent (K := K) (p := p) : ℝ) *
      stepVLambda p label jValue l =
      (label : ℝ) ^ 2 * (inverseJInvariantOrder jValue largeNorm : ℝ) /
        (2 * l : ℕ) := by
    rw [stepVLambda_eq_order_div_ramification (p := p) label jValue largeNorm l]
    field_simp
  rw [hreal, stepVLambdaOrder_cast_eq_div label jValue largeNorm l hl hcard]

/-- In a local-field extension, the Step (v) card `2l ∣ ord(J⁻¹)` is exactly
`2l·e_K ∣ v_K(a)·e_L`.  This is the extension form of the card, cited from
`LocalRootNormRepresentative.order_dvd_extension_iff_ramification` (not reproved). -/
theorem stepVRootOrderCard_extension_iff {L : Type*} [NormedField L] [CharZero L]
    [CompleteSpace L] [IsUltrametricDist L] [ProperSpace L]
    [NormedAlgebra ℚ_[p] L] [IsDiscreteValuationRing (Integers L)]
    [NormedAlgebra K L] (element : Integers K) (nonzero : element ≠ 0) (l : ℕ) :
    (2 * l) ∣ ((IsDiscreteValuationRing.addVal (Integers L)
        (LocalDifferentUpperBound.integersExtensionMap (L := L) element)).toNat) ↔
      (2 * l) * logShellRamificationExponent (K := K) (p := p) ∣
        ((IsDiscreteValuationRing.addVal (Integers K) element).toNat *
          logShellRamificationExponent (K := L) (p := p)) :=
  LocalRootNormRepresentative.order_dvd_extension_iff_ramification
    (p := p) (L := L) element nonzero (2 * l)

/-- The normalized q-pilot order scaled by the ramification exponent is the
actual DVR order of `J⁻¹`: `e·ord(q) = v(J⁻¹)` whenever `‖J‖·‖q‖ = 1`.  This
identifies the guidance card `2l ∣ e·ord(q)` with `StepVRootOrderCard`. -/
theorem ramification_mul_qOrder_eq_inverseJOrder {q : K}
    (jValue : K) (largeNorm : 1 < ‖jValue‖)
    (hprod : ‖jValue‖ * ‖q‖ = 1) :
    (logShellRamificationExponent (K := K) (p := p) : ℝ) * localNormOrder p q =
      (inverseJInvariantOrder jValue largeNorm : ℝ) := by
  have hram_ne : (logShellRamificationExponent (K := K) (p := p) : ℝ) ≠ 0 := by
    exact_mod_cast (LocalFieldLogarithm.logShellRamificationExponent_pos
      (K := K) (p := p)).ne'
  rw [localNormOrder_eq_neg_of_norm_mul_eq_one p jValue q hprod,
    neg_localNormOrder_eq_inverseJInvariantOrder_div jValue largeNorm]
  field_simp

/-- The Step (v) card in the guidance form `2l ∣ e·ord(q)`: for a q-parameter
with `ord q = -ord J` (norm-level Tate relation), the divisibility of `ord(J⁻¹)`
by `2l` is exactly the integrality of the scaled q-pilot order `e·ord(q)`
divided by `2l`.  No coprimality of the root order with `l` is assumed. -/
theorem StepVRootOrderCard_iff_scaled_qOrder {q : K}
    (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ)
    (hprod : ‖jValue‖ * ‖q‖ = 1) :
    StepVRootOrderCard jValue largeNorm l ↔
      ∃ k : ℤ, (logShellRamificationExponent (K := K) (p := p) : ℝ) *
        localNormOrder p q = ((2 * l : ℕ) : ℝ) * (k : ℝ) := by
  have hscaled := ramification_mul_qOrder_eq_inverseJOrder (p := p) jValue largeNorm hprod
  constructor
  · intro hcard
    have hdvd : ((2 * l : ℕ) : ℤ) ∣ (inverseJInvariantOrder jValue largeNorm : ℤ) :=
      Int.natCast_dvd_natCast.mpr hcard
    obtain ⟨k, hk⟩ := dvd_iff_exists_eq_mul_right.mp hdvd
    refine ⟨k, ?_⟩
    rw [hscaled]
    exact_mod_cast hk
  · rintro ⟨k, hk⟩
    have hki : (inverseJInvariantOrder jValue largeNorm : ℤ) =
        ((2 * l : ℕ) : ℤ) * k := by
      have hreal : (inverseJInvariantOrder jValue largeNorm : ℝ) =
          ((2 * l : ℕ) : ℝ) * (k : ℝ) := by
        rw [← hscaled]
        exact hk
      exact_mod_cast hreal
    exact Int.natCast_dvd_natCast.mp (dvd_iff_exists_eq_mul_right.mpr ⟨k, hki⟩)

end LocalFieldValueGroup

/-! ## 3. The norm-order representative from the actual j-invariant order -/

section Representative

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] [NormedAlgebra ℚ_[p] K]
  [IsDiscreteValuationRing (Integers K)]

/-- **Step (v) norm-order representative from the actual j-invariant order.**
If `2l` divides the actual DVR order of `J⁻¹` (`StepVRootOrderCard`), then
there is a nonzero `ϖ` whose normalized order is `stepVLambda = j²·(-ord J)/(2l)`.
This cites `LocalRootNormRepresentative.exists_stepV_j_normOrder_representative`;
no algebraic root of `q` and no Tate parameter is constructed. -/
theorem exists_stepV_normOrder_representative_of_stepVLambda
    (label : ℕ) (jValue : K) (largeNorm : 1 < ‖jValue‖) (l : ℕ) (hl : 0 < 2 * l)
    (hcard : StepVRootOrderCard jValue largeNorm l) :
    ∃ varpi : K, varpi ≠ 0 ∧ localNormOrder p varpi = stepVLambda p label jValue l := by
  obtain ⟨varpi, hne, hord⟩ :=
    LocalRootNormRepresentative.exists_stepV_j_normOrder_representative
      (p := p) jValue largeNorm (2 * l) hl label
      (by simpa [StepVRootOrderCard, inverseJInvariantOrder] using hcard)
  exact ⟨varpi, hne, by simpa [stepVLambda] using hord⟩

end Representative

/-! ## 4. The theta-side Step (v) hull bound with the explicit exponent -/

section ActualTuple

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
variable {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
  [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
  [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]

/-- **Theta-side Step (v) hull-volume bound with** `λ = stepVLambda`**.**
This feeds the norm-order representative `ϖ` of Section 3 into the already
proved actual-tuple Step (v) theorem `arithmeticTuple_stepV_hull_le_paperBound`
(`FinitePlaceStepVAssembly`), stating the paper's signed real bound
`(-λ + ∑ d_i + 1)·log p + ∑_{i∈I*}(3 + log e_i)` with
`λ = j²·(-ord J)/(2l)`.  Only the theta side is asserted: no q-pilot or Tate
parameter is produced. -/
theorem arithmeticTuple_stepV_hull_le_paperBound_of_stepVLambda [DecidableEq ι]
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [Measure.IsAddHaarMeasure μ]
    (e : ArithmeticTensorTupleBlock places tuple ≃ₐ[ℚ_[p]] ((j : J) → E j))
    (istar : ι)
    [IsDiscreteValuationRing
      (Integers (CommonPrimeCompletion (places istar (tuple istar))))]
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (largeNorm : 1 < ‖jValue‖) (l label : ℕ) (hl : 0 < 2 * l)
    (hcard : StepVRootOrderCard jValue largeNorm l)
    (Φ : Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
      ArithmeticTensorTupleBlock places tuple))
    (hΦne : Φ.Nonempty)
    (hΦ : ∀ φ ∈ Φ, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
      φ u ∈ arithmeticTupleUnitLogLattice places tuple)
    (exceptional : Finset ι)
    (small_outside : ∀ i, i ∉ exceptional →
      logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2) :
    ∃ varpi : CommonPrimeCompletion (places istar (tuple istar)), varpi ≠ 0 ∧
      localNormOrder p varpi = stepVLambda p label jValue l ∧
      arithmeticTupleNormalizedLogVolume places tuple μ
          (arithmeticTupleHolomorphicHull places tuple e
            (arithmeticTupleStepVPossibleImages places tuple istar varpi Φ)) ≤
        (-(stepVLambda p label jValue l) +
            ∑ i, localNormOrder p (arithmeticTupleLocalDifferent places tuple i) + 1) *
          Real.log (p : ℝ) +
        ∑ i ∈ exceptional, (3 + Real.log
          (logShellRamificationExponent
            (K := CommonPrimeCompletion (places i (tuple i))) (p := p) : ℝ)) := by
  obtain ⟨varpi, hvarpi, hord, hbound⟩ :=
    arithmeticTuple_stepV_hull_le_paperBound_of_jInvariant places tuple μ e istar
      jValue largeNorm l label hl
      (by simpa [StepVRootOrderCard, inverseJInvariantOrder] using hcard)
      Φ hΦne hΦ exceptional small_outside
  refine ⟨varpi, hvarpi, ?_, ?_⟩
  · simpa [stepVLambda] using hord
  · simpa [stepVLambda] using hbound

end ActualTuple

/-! ## 5. The residual q-side source condition of N8 -/

/-- The residual q-side source condition of N8 (workstream N5): the signed
value attached to the actual q-pilot is `-|log q|`.  This is the source
identification of IUT III Theorem 3.11 (ii) (the Kummer/Theta-pilot
containment), and it is NOT proved in this file; it is recorded as a named
hypothesis so that any conditional reduction must consume it explicitly. -/
def qSideSignedValueCondition (qPilot qSigned : ℝ) : Prop :=
  qSigned = -|Real.log qPilot|

/-- Under the residual condition and `0 < q < 1`, the signed q-side value is
the ordinary (negative) logarithm `log q`. -/
theorem qSideSignedValueCondition_eq_log {qPilot qSigned : ℝ}
    (h : qSideSignedValueCondition qPilot qSigned) (h0 : 0 < qPilot) (h1 : qPilot < 1) :
    qSigned = Real.log qPilot := by
  unfold qSideSignedValueCondition at h
  rw [h, abs_of_neg (Real.log_neg h0 h1), neg_neg]

/-- The residual condition forces a strictly negative signed q-side value for a
q-pilot inside the open unit ball. -/
theorem qSideSignedValueCondition_neg {qPilot qSigned : ℝ}
    (h : qSideSignedValueCondition qPilot qSigned) (h0 : 0 < qPilot) (h1 : qPilot < 1) :
    qSigned < 0 := by
  rw [qSideSignedValueCondition_eq_log h h0 h1]
  exact Real.log_neg h0 h1

/-- The negative of the signed q-side value is `|log q|`: this is the exact
signed-log content of the residual condition, written without the `0 < q < 1`
normalization. -/
theorem neg_qSideSignedValueCondition_eq_abs {qPilot qSigned : ℝ}
    (h : qSideSignedValueCondition qPilot qSigned) :
    -qSigned = |Real.log qPilot| := by
  unfold qSideSignedValueCondition at h
  rw [h, neg_neg]

end

end LeanFormal.IUT.NumberFieldFinitePlace
