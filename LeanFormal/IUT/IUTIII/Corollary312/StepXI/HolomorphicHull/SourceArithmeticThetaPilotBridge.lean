import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull

/-!
# The minimal source-arithmetic theta-pilot bridge (N5 section 4.2)

This module implements the minimal conditional bridge proposed in
`logs/coordination/n5-source-realization-gap-20261017.md` section 4.2, at the actual
Lean API of the source value carrier and of the arithmetic tensor tuple block.

## The bridge data

For fixed arithmetic data `places`, `tuple` and fixed source data `I`, `v`, `R`, `n`,
`ArithmeticThetaPilotBridge places tuple I v R n` records:

* `toSource : A^× →* I.ThetaPilotPoint v`, a multiplicative map from the units of the
  arithmetic tensor block `A := ArithmeticTensorTupleBlock places tuple` to the
  source value carrier;
* an additive log-degree map on those units, represented as
  `degreeMap : Additive A^× →+ Real`.  This is the report's `A^× →+ Real`; since
  `A^×` is multiplicatively a group, its additive view is `Additive A^×`, and the
  canonical comparison element is `Additive.ofMul a`;
* the degree compatibility
  `I.sourceLocalLogDegree v (toSource a) = degreeMap (Additive.ofMul a)`;
* a theta lift `thetaLift : SourceVolumeIndex l → A^×` whose images are the actual
  source theta-pilot points.  The actual arity of `sourceThetaPilotPoint` is
  `(v) (R) (n) (j)`, so for `q : SourceVolumeIndex l` the compatibility reads
  `toSource (thetaLift q) = I.sourceThetaPilotPoint v R q.1 q.2`;
* the directed hull cover
  `I.sourceHolomorphicHull v R n ⊆ toSource '' (H_A ∩ A^×)`, where
  `H_A := arithmeticTupleCanonicalHull places tuple`.  Units and ambient elements
  have different types, so `H_A ∩ A^×` is rendered as the set of units
  `{a : A^× | (a : A) ∈ H_A}`;
* the uniform bound on the arithmetic degrees of those units.

These are exactly the fields of the proposed bridge, with only the type corrections
forced by the actual API; no hypothesis is weakened and no conclusion is stored as a
field.

## Proved statements

* `sourceHullVolume_lt_top_of_arithmeticThetaPilotBridge`: from the bridge fields,
  `I.sourceHullVolume v R n < ⊤`.  The proof uses `hull_cover`, `degree_compat` and
  `unit_bound` together with the already proved reduction
  `sourceHullVolume_lt_top_of_hullBound`; finiteness is not a structure field.
* `no_degreeFaithful_fullHull_arithmeticThetaPilotBridge`: under pointwise degree
  faithfulness `hdeg`, the `hull_cover` proposition of any bridge is false.  F2
  (`sourceHolomorphicHull_logDegree_unbounded`) produces hull points of arbitrarily
  large source log-degree, while `unit_bound` bounds the degree on the arithmetic
  side; `degree_compat` transfers the bound to the source hull.
* `not_nonempty_arithmeticThetaPilotBridge_of_degreeFaithful`: consequently no bridge
  exists at all in the `hdeg` regime.

## Scope

No bridge is constructed, and no existence of `toSource`, `degreeMap`, `thetaLift`,
the hull cover, or the unit bound is derived from `OriginalInput` or from the
arithmetic tensor carrier.  This module does not claim that
`ArithmeticTensorTupleBlock` realizes the source theta-pilot carrier, and it does not
close N5.  The negative calibration shows that the full-hull, degree-faithful version
of the bridge cannot exist; closing N5 needs a non-degree-faithful comparison or a
different, justified carrier equivalence.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui uK vι wV

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

/-- The minimal comparison data from the arithmetic tensor tuple block to the source
theta-pilot value carrier.

The arithmetic side is `A := ArithmeticTensorTupleBlock places tuple`, and
`A^×` is its unit group.  The set `H_A ∩ A^×` appearing in `hull_cover` and
`unit_bound` is the set of units whose underlying element lies in the canonical
arithmetic hull `H_A := arithmeticTupleCanonicalHull places tuple`. -/
structure ArithmeticThetaPilotBridge
    {K : Type uK} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι → Type wV}
    (places : (i : ι) → Va i → FinitePlaceAtPrime K p)
    (tuple : (i : ι) → Va i)
    {l : PrimeGeFive} {V : Type uv}
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  /-- The multiplicative comparison from arithmetic units to source value points. -/
  toSource : (ArithmeticTensorTupleBlock places tuple)ˣ →* I.ThetaPilotPoint v
  /-- The additive log-degree on the arithmetic unit group, in its additive view. -/
  degreeMap : Additive (ArithmeticTensorTupleBlock places tuple)ˣ →+ Real
  /-- The source log-degree of an arithmetic unit equals its arithmetic degree. -/
  degree_compat : ∀ a : (ArithmeticTensorTupleBlock places tuple)ˣ,
    I.sourceLocalLogDegree v (toSource a) = degreeMap (Additive.ofMul a)
  /-- The arithmetic unit attached to each source theta-pilot index. -/
  thetaLift : SourceVolumeIndex l → (ArithmeticTensorTupleBlock places tuple)ˣ
  /-- The theta lift realizes the actual source theta-pilot points. -/
  theta_compat : ∀ q : SourceVolumeIndex l,
    toSource (thetaLift q) = I.sourceThetaPilotPoint v R q.1 q.2
  /-- The full source hull is covered by the image of the canonical arithmetic hull
  inside the arithmetic unit group. -/
  hull_cover :
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
      toSource '' {a : (ArithmeticTensorTupleBlock places tuple)ˣ |
        (a : ArithmeticTensorTupleBlock places tuple) ∈
          arithmeticTupleCanonicalHull places tuple}
  /-- The arithmetic degrees of the units in the canonical hull are uniformly
  bounded. -/
  unit_bound : ∃ C : Real, ∀ a : (ArithmeticTensorTupleBlock places tuple)ˣ,
    (a : ArithmeticTensorTupleBlock places tuple) ∈
      arithmeticTupleCanonicalHull places tuple →
        degreeMap (Additive.ofMul a) ≤ C

/-- The bridge fields imply finiteness of the source holomorphic hull volume.

The proof extracts the arithmetic degree bound from `unit_bound`, covers every point
of the source hull by `hull_cover`, and transfers degrees through `degree_compat`; the
already proved reduction `sourceHullVolume_lt_top_of_hullBound` then gives
`sourceHullVolume v R n < ⊤`.  The conclusion is derived from the fields and is not
stored in the structure. -/
theorem sourceHullVolume_lt_top_of_arithmeticThetaPilotBridge
    {K : Type uK} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι → Type wV}
    {places : (i : ι) → Va i → FinitePlaceAtPrime K p}
    {tuple : (i : ι) → Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (B : ArithmeticThetaPilotBridge places tuple I v R n) :
    I.sourceHullVolume v R n < ⊤ := by
  obtain ⟨C, hC⟩ := B.unit_bound
  refine I.sourceHullVolume_lt_top_of_hullBound v R n (C := C) ?_
  intro x hx
  obtain ⟨a, ha, hax⟩ := B.hull_cover hx
  rw [← hax, B.degree_compat a]
  exact hC a ha

/-- Negative calibration: under pointwise degree faithfulness, the full-hull cover
field of any arithmetic theta-pilot bridge is false.

F2 (`sourceHolomorphicHull_logDegree_unbounded`) gives, for the arithmetic bound `C`,
a point of the source hull whose log-degree exceeds `C`.  The cover field writes it as
`toSource a` for a unit `a` in the canonical arithmetic hull; `degree_compat` makes
its source log-degree equal to the bounded arithmetic degree, a contradiction. -/
theorem no_degreeFaithful_fullHull_arithmeticThetaPilotBridge
    {K : Type uK} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι → Type wV}
    {places : (i : ι) → Va i → FinitePlaceAtPrime K p}
    {tuple : (i : ι) → Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (B : ArithmeticThetaPilotBridge places tuple I v R n) :
    ¬ ((I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
        B.toSource '' {a : (ArithmeticTensorTupleBlock places tuple)ˣ |
          (a : ArithmeticTensorTupleBlock places tuple) ∈
            arithmeticTupleCanonicalHull places tuple}) := by
  intro hcover
  obtain ⟨C, hC⟩ := B.unit_bound
  obtain ⟨x, hx, hgt⟩ :=
    I.sourceHolomorphicHull_logDegree_unbounded v R n hdeg C
  obtain ⟨a, ha, hax⟩ := hcover hx
  have hle : I.sourceLocalLogDegree v x ≤ C := by
    rw [← hax, B.degree_compat a]
    exact hC a ha
  linarith

/-- Under pointwise degree faithfulness no arithmetic theta-pilot bridge exists: the
cover field required by the structure is exactly the proposition refuted by
`no_degreeFaithful_fullHull_arithmeticThetaPilotBridge`. -/
theorem not_nonempty_arithmeticThetaPilotBridge_of_degreeFaithful
    {K : Type uK} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {ι : Type vι} [Finite ι] {Va : ι → Type wV}
    {places : (i : ι) → Va i → FinitePlaceAtPrime K p}
    {tuple : (i : ι) → Va i}
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ Nonempty (ArithmeticThetaPilotBridge places tuple I v R n) := by
  rintro ⟨B⟩
  exact (no_degreeFaithful_fullHull_arithmeticThetaPilotBridge hdeg B) B.hull_cover

end

end LeanFormal.IUT
