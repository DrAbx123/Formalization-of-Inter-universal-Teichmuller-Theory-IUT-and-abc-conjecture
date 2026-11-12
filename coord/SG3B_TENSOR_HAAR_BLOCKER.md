# SG3b — tensor Haar product blocker

Date: 2026-11-07
Scope: audit of the C3 tensor log-volume identity
`actualC3LogShellTensorLogVolume C3 = packetLogVolume packet`.
Result: **no actual product-Haar formula exists**; exact blocker identified.
No fake packet/axiom.

## 1. What the actual tree proves

### Set-level image, no measure pushforward

`LeanFormal/IUT/Foundations/LocalFields/FinitePadicTensorIntegralRegion.lean`:

```lean
def tensorIntegralRegion (S : (i : ι) → Set (M i)) :
    Set (FinitePadicTensor (p := p) M) :=
  finitePadicTensorTprod (p := p) M '' Set.pi Set.univ S

theorem tensorIntegralRegion_eq_range (S) :
    tensorIntegralRegion (p := p) M S =
      Set.range (fun x : ((i) → S i) =>
        finitePadicTensorTprod (p := p) M (fun i => (x i).val))
```

Similarly `FinitePadicTensorLogShellRegion.tensorLogShellRegion_eq_range`.
These only identify the region as a range/image.  There is **no**
`Measure.map` / pushforward / product-Haar lemma for this image.

### Positivity/finiteness only

`FinitePadicTensorLogShellHull.lean`:

- `isCompact_tensorLogShellRegion`
- `one_mem_tensorLogShellRegion`
- `measure_tensorLogShellHull_pos_lt_top` (positivity/finiteness)
- `tensorLogShellHull_logVolume_nonneg`

`FinitePadicTensorLogShellRealization.lean`:

- `exists_realized_tensorLogShell_hull`: field-product realization of the hull
  with nonzero scales `lam`.

None of these gives a volume product formula.

### Closest actual exact substitute: lattice relative Haar log

`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceIntegralTensorCovolume.lean`:

```lean
theorem arithmeticTupleLogTensorUnitLogVolume_eq_relativeHaarLog
    (μ : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure μ] :
    arithmeticTupleLogTensorUnitLogVolume places tuple =
      Real.log (μ (arithmeticTupleIntegralLogLattice places tuple)).toReal -
        Real.log (μ (arithmeticTupleCanonicalUnitReference places tuple)).toReal
```

with

```lean
def arithmeticTupleLogTensorUnitLogVolume : ℝ :=
  Real.log (arithmeticTupleLogTensorIntersectionIndex) -
    Real.log (arithmeticTupleHolomorphicIntersectionIndex)
```

This is an **index/covolume normalization of the integral log lattice**, not a
product of local volumes of the compact log-shell region.
`FinitePlaceSelectedPrimeIntegralTensorVolume.lean` only gives weighted sums
of these lattice volumes, still not a `tprod` product formula.

### Exact fractional-lattice factor formula (different model)

`FinitePlaceNormalizedUnitScalingLogVolume.lean`:

```lean
theorem arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    (μ) [Measure.IsAddHaarMeasure μ] {c : ι → ℝ}
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) :
    arithmeticTupleNormalizedLogVolume places tuple μ
      ((F c * O_hol : Submodule ℤ_[p] ...) : Set ...) =
      -((∑ i, c i) * Real.log (p : ℝ))
```

Normalization factor: `1 / finrank_{Q_p}(ArithmeticTensorTupleBlock)`.
This is exact, but for `(F c) * O_hol`, **not** for the C3 tensor image of
local log-shells.

## 2. Exact missing pieces

1. **Product-Haar comparison**

```text
Measure.addHaar on a finite product  vs.  Measure.pi of local Haars
  including the normalization constants
```

Not available for the field-product realization used for the tensor block.

2. **Multilinear pushforward normalization**

```text
finitePadicTensorTprod : multilinear map, not a linear equivalence;
image of a product set is not a product set.
```

No Jacobian/determinant factor theorem for
`tensorIntegralRegion = finitePadicTensorTprod '' Set.pi ...`.

Consequently the identity

```lean
actualC3LogShellTensorLogVolume C3 =
  ∑ i : C3.tensorIndex, S2814LocalLogVolume C3 i
```

has no actual proof in the current tree.

## 2b. Actual product-Haar formula on the product side

`tmp/sheaf/xif/paper/S2827SG3bProductHaarActual.lean`
(ACTUAL, olean 33328 B, axioms trio) proves the product-Haar formula on the
product side:

```lean
theorem S2827_pi_pi {J} [Fintype J] {E} [∀ j, MeasurableSpace (E j)]
    (mu : (j : J) → Measure (E j)) [∀ j, SigmaFinite (mu j)]
    (S : (j : J) → Set (E j)) :
    Measure.pi mu (Set.pi Set.univ S) = ∏ j, mu j (S j)

theorem S2827_pi_pi_logVolume ... :
    Real.log ((Measure.pi mu (Set.pi Set.univ S)).toReal) =
      ∑ j, Real.log ((mu j (S j)).toReal)
```

This is exactly the product-Haar factor formula, but on the **Cartesian product
side**.  What is still missing is the tensor pushforward identification:

```lean
def S2827TensorRegionProductImage (e : X ≃ Y)
    (region : Set X) (localRegion : Set Y) : Prop :=
  e '' region = localRegion
```

No actual `e` for the C3 tensor block sends the tensor log-shell image to a
Cartesian product of local log-shell regions.  Thus `S2827_pi_pi_logVolume`
cannot yet be applied to `actualC3LogShellTensorRegion`.

## 3. Exact missing statement

```lean
def S2814TensorPacketIdentity (C3) : Prop :=
  actualC3LogShellTensorLogVolume C3 =
    ∑ i : C3.tensorIndex, S2814LocalLogVolume C3 i
```

This is the SG3b target; stated in
`tmp/sheaf/xif/paper/S2814SG3bLocalPacketActual.lean`, not proved.

## 4. Status / next step

```text
tensor region = image of product          ACTUAL (set level)
tensor region compact / positive measure  ACTUAL
tensor volume = product local volumes     MISSING
lattice relative Haar log                 ACTUAL (substitute)
fractional-lattice exact factor formula   ACTUAL (different model)
C3 local packet definition                ACTUAL
C3 tensor packet identity                 MISSING
```

To close SG3b one must prove the product-Haar + multilinear normalization
formula, or construct a different actual packet whose region is genuinely a
Cartesian product of local log-shells with known Haar volumes.

No ABC assumption, no fake object, no axiom beyond the permitted trio is used
by this audit.

## 4. Update 2026-11-07 — product-side formula ACTUAL (kummer)

`S2827SG3bProductHaarActual` is ACTUAL:

```text
src 1918 B SHA A26402E84DB62672206349397E9878B384224C85EE108F20F84858A9A48AEC2A
olean 33328 B SHA 27C26C62023400F07730E1573F1401CBBC28D45345C9FA00DA32E6363013B196
axioms trio
```

Actual:

```lean
S2827_pi_pi : Measure.pi mu (Set.pi univ S) = prod j, mu j (S j)
S2827_pi_pi_logVolume : log ((Measure.pi mu (Set.pi univ S)).toReal)
  = sum j, log ((mu j (S j)).toReal)
```

These are the product-Haar factor formulas (product side). The remaining
missing object is exactly the tensor pushforward identification:

```lean
S2827TensorRegionProductImage (e : X ≃ Y) (region : Set X) (localRegion : Set Y) : Prop :=
  e '' region = localRegion
```

For the C3 tensor block no actual `e` identifies the image of
`tensorLogShellRegion` with a Cartesian product of local log-shell regions.
Therefore `S2827_pi_pi_logVolume` cannot yet be applied to
`actualC3LogShellTensorRegion`.

Also: `S2818` fractional-lattice factor formula is ACTUAL, but it needs the
same tensor pushforward identification to connect to the C3 tensor block.
## 5. Update 2026-11-07 — conditional no-go for product decomposition

`S2828SG3bProductNoGoActual.lean` is ACTUAL:

```text
src 3160 B SHA 82B9DDFC512C8273BBFA96E799042B691E06F80813E0845305A1629E43E8D484
olean 169736 B SHA EA2756C0BF00DB5FBFD40A34B489F97AFF08373F27CCCE5970E01390BD45A859
axioms trio
```

Actual:

```lean
S2828NotAdditiveWitness C3 :=
  exists x y in actualC3LogShellTensorRegion C3, x + y notin region

S2828ProductDecomposition e localRegion :=
  e '' region = Set.pi univ localRegion

S2828_no_product_decomposition_of_not_additive :
  non-additivity witness + linear e + pointwise-additive localRegion
  -> no product decomposition
```

Remaining exact obligation: a concrete C3 non-additivity witness
(two pure tensors whose local components are independent in at least two
factors, with non-pure sum). No explicit local basis/independence data for C3
is present in the tree, so the unconditional counterexample is not constructed.
Alternatively, a positive route needs an explicit linear `e` and local regions
with the product decomposition; neither is present.

Product-side Haar formulas remain actual in `S2827_pi_pi` /
`S2827_pi_pi_logVolume`; they cannot be applied until the product decomposition
identity exists.
## 6. Update 2026-11-07 — product decomposition ⇔ additive, no-go reduced to witness

`S2828SG3bProductNoGoActual.lean` updated (ACTUAL conditional no-go + structure):

```text
src 4820 B SHA DAEFEF30A12BC5A2A0F5DD58377E3F96E7AE780E53ABD64459ACA7EFB39E6256
olean 222696 B SHA AA9D9A7A8515E7EEC2BBCD405C3E8A312D70AD3006B9BCD3824FF95F4ECE11B1
axioms trio
```

New actual theorem:

```lean
S2828_additive_of_productDecomposition :
  (e linear, localRegion pointwise additive,
   e '' region = Set.pi univ localRegion)
  -> forall x in region, forall y in region, x + y in region
```

Consequence:

- product decomposition ⇒ region additive ⇒ no non-additivity witness;
- non-additivity witness ⇒ no such product decomposition
  (`S2828_no_product_decomposition_of_not_additive`).

The unconditional no-go is now EXACTLY reduced to constructing

```lean
exists x y in actualC3LogShellTensorRegion C3,
  x + y notin actualC3LogShellTensorRegion C3
```

Not yet constructed: the C3 schema has arbitrary donor tensorIndex/local fields,
with no cardinal/dimension/independence assumptions. A witness needs donor
data with linearly independent local components in at least two tensor factors.
No explicit C3 local basis/independence is present in the tree, so the witness
cannot be derived from the current C3 data.