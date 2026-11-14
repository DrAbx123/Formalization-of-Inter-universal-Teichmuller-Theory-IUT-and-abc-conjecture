# A1-TENSOR-PROD-PROBE — A1 equality-case algebra equivalence: verdict and obstruction

Date: 2026-11-14 (Asia/Shanghai). Lane: stage4 / A1 tensor-vs-product probe.
Files: this report + `tmp/sheaf/xif/paper/Mzk1A1TensorProdProbeActual.lean`.

## 0. Verdict

**ILL-TYPED** for the literal target, in the current Lean instance graph.

The exact statement

```lean
ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple
  ≃ₐ[ℚ_[qVFamTensorP T b]]
    ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b')
```

does not elaborate. The right-hand dependent product is **not** a
`ℚ_[qVFamTensorP T b]`-algebra: the `b'`-th factor `rootNormedExtension T b'` has
its canonical p-adic scalar algebra over `ℚ_[qVFamTensorP T b']` (the rational
prime of `b'` itself), produced by `IntermediateField.algebra'` from
`SourceAlgebraicClosure.sourceAlgebraicClosurePadicAlgebra` and
`sourceAlgebraicClosureScalarTower`. There is no instance
`Algebra ℚ_[qVFamTensorP T b] (rootNormedExtension T b')` for the generic `b'`,
so the Pi-algebra instance required by `≃ₐ[·]` fails and the intended type
is not well-formed.

The nearest well-typed common-base repair (impose `[∀ b', Algebra ℚ_[p_b] (rootNormedExtension T b')]`)
is **not** the truth of A1: the canonical-equality obstruction shows that, with
one nontrivial root factor, any such equivalence forces
`card Bad < finrank(block)`; the equality case `card Bad = finrank(block)`
forces every factor to have `ℚ_p`-degree one. In other words the common-base
product can only meet the block in the fully collapsed (degree-one) situation,
which for actual qVFam data requires the root extensions to collapse to their
base completions. The per-factor matched-prime statement
`qVFamTensorBlock T b ≃ₐ[ℚ_[p_b]] rootNormedExtension T b` is well-typed but
**false whenever the root extension is nontrivial** (`[L_b : K_b] > 1`), by the
tower dimension formula.

Summary table:

| statement | status |
|---|---|
| literal target (one `p_b`-base product over all `Bad`) | **ILL-TYPED** (base-prime mismatch) |
| common-base repair with imposed per-factor `ℚ_[p_b]`-algebras | false unless every root factor has `ℚ_p`-degree 1; equality case forces collapse |
| per-factor matched-prime `qVFamTensorBlock T b ≃ₐ[ℚ_[p_b]] rootNormedExtension T b` | false if `1 < [L_b : K_b]` |
| `qVFamTensorBlock T b ≃ₐ[ℚ_[p_b]] rootBase T b` (base completion) | expected TRUE (dimension half proved in probe; AlgEquiv construction is the next task, section 4.1) |
| `rootTensorBlock T b ≃ₐ[ℚ_[p_b]] rootNormedExtension T b` (root tensor) | expected TRUE (same one-factor tensor lemma; section 4.1) |

## 1. Definition chain and the exact failure

The actual qVFam data are per-bad-place, each with its **own** rational prime:

* `qVFamTensorPlace T b = (nativeBadLift T).lift b` — a finite `F`-place
  (`tmp/sheaf/xif/paper/QVFamTensorCoefficientActual.lean:47-48`).
* `qVFamTensorP T b = (completionRationalPrime (qVFamTensorPlace T b)).val`
  (`QVFamTensorCoefficientActual.lean:51-52`); this is the prime under the
  `b`-th block.
* `qVFamTensorV = Unit`, `qVFamTensorPlaces T b : Unit → Unit → FinitePlaceAtPrime F (qVFamTensorP T b)`,
  `qVFamTensorTuple = ()` (`QVFamTensorCoefficientActual.lean:59-69`).
* `qVFamTensorBlock T b = ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple`
  (`QVFamTensorCoefficientActual.lean:72-73`).
* `ArithmeticTensorTupleBlock places tuple =
    FinitePadicTensor (fun i => CommonPrimeCompletion (places i (tuple i)))`
  (`LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceArithmeticTensorBlocks.lean:26-27`).
* `CommonPrimeCompletion place = NormalizedCompletion place`
  (`FinitePlaceCommonPrimeCompletion.lean:20`); `NormalizedCompletion place = Completion place`
  (`FinitePlaceNormalizedCompletion.lean:25`). Hence for the one-factor qVFam block
  the factor is the base completion `K_b = F_{v_b}`.
* `rootBase T b = sourceRootField T b = NormalizedCompletion (qVFamTensorPlace T b)`
  (`PaperRootCompletionTensorActual.lean:35` and
  `PaperThetaRootObstructionActual.lean:40-42`).
* `rootNormedExtension T b : IntermediateField (rootBase T b) (rootNormedAmbient T b)`
  (`PaperRootCompletionTensorActual.lean:58-60`), where
  `rootNormedAmbient T b = SourceAlgebraicClosure (qVFamTensorPlace T b)`.
* `PadicScalarField place = ℚ_[(completionRationalPrime place).val]`
  (`LeanFormal/IUT/ABCBridge/Geometry/FinitePlacePadicScalarStructure.lean:31-32`).
  Thus `PadicScalarField (qVFamTensorPlace T b) = ℚ_[qVFamTensorP T b]` definitionally.
* The ambient scalar algebra is
  `sourceAlgebraicClosurePadicAlgebra place :
    Algebra (PadicScalarField place) (SourceAlgebraicClosure place)`
  with the compatible `sourceAlgebraicClosureScalarTower`
  (`FinitePlaceSourceAlgebraicClosure.lean:42-50`).
* `IntermediateField.algebra'` turns that into an algebra on the intermediate
  field (`Mathlib/FieldTheory/IntermediateField/Basic.lean:407-409`): for
  `S : IntermediateField K L` and `[Algebra R' L]`, `[IsScalarTower R' K L]`,
  `[SMul R' K]` it yields `Algebra R' S`.

For `b' = b` the last step applies with `R' = ℚ_[qVFamTensorP T b]` because
`rootBase T b` and the ambient are both built at the *same* place
`qVFamTensorPlace T b`. For a generic `b'` the factor is built at
`qVFamTensorPlace T b'`, whose scalar field is `ℚ_[qVFamTensorP T b']`. There is
no definitional or instance-level identification with `ℚ_[qVFamTensorP T b]`.

Direct check (temporary probe, not in the final file):

```
#synth Algebra ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b)
-- (rootNormedExtension T b).algebra'            -- succeeds

#synth Algebra ℚ_[(qVFamTensorP T b)]
  ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b')
-- failed to synthesize Algebra ℚ_[qVFamTensorP T b]
--   ((b' : Bad ...) → ↥(rootNormedExtension T b'))

#check (ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple
  ≃ₐ[ℚ_[(qVFamTensorP T b)]] ((b' : Bad (nativePlaceSelection T)) → rootNormedExtension T b'))
-- error(lean.synthInstanceFailed): failed to synthesize instance of type class
--   Algebra ℚ_[qVFamTensorP T b] ((b' : Bad ...) → ↥(rootNormedExtension T b'))
```

This is a base-prime mismatch, not a missing proof: the statement compares one
place's prime with a product over the whole bad family.

## 2. Sub-gap decomposition

### 2.1 Base completion vs root extension (`K_b` vs `L_b`)

The left-hand side is the one-factor tensor of the **base completion** `K_b`,
not of the root extension:

* `qVFamTensorBlock T b = ⨂[ℚ_[p_b]] (_ : Unit), K_b` (definitional
  one-factor tensor), and
  `finrank ℚ_[p_b] (qVFamTensorBlock T b) = finrank ℚ_[p_b] (rootBase T b)`
  (probe `qVFamTensorBlock_finrank`, from
  `finrank_arithmeticTensorTupleBlock`,
  `FinitePlaceArithmeticTensorBlocks.lean:97-100`).
* `rootNormedExtension T b = L_b = K_b(root_b)` is a *different* object: the
  intermediate field generated by the `2l`-th root of the qVFamily parameter.
  Its dimension obeys
  `finrank ℚ_[p_b] L_b = finrank ℚ_[p_b] K_b * finrank K_b L_b`
  (probe `rootNormedExtension_finrank_tower`).
* If `1 < finrank K_b L_b` then no algebra equivalence
  `qVFamTensorBlock T b ≃ₐ[ℚ_[p_b]] L_b` exists (probe
  `no_algEquiv_rootNormedExtension_of_one_lt_finrank`). The dimension ratio is
  exactly the missing "degree factor" `[L_b : K_b]`.

The nontriviality `1 < [L_b : K_b]` is **not** currently a consequence of
`SourceNativeInitialThetaData`. The source gives
`0 < (qVFamily T b).order` and `Nat.Coprime (qVFamily T b).order l.value`, but
NOT `order = 1`: `order = 1` is the explicit `TateUniformizerCondition`
(`Mzk1QOrderOneActual.lean:71-77`) and `Mzk1QOrderOneActual` records that it is
not derivable from clause B. A sufficient valuation obstruction is
`¬ (2 * l.value ∣ (qVFamily T b).exponent)`: if `root_b ∈ K_b` then applying the
discrete valuation to `root_b^(2l) = q` forces `2l ∣ exponent`. This is the
exact open arithmetic input for an unconditional per-factor refutation.

### 2.2 Tensor factor vs root extension

The B2/finite-étale decomposition of `ArithmeticTensorTupleBlock places tuple`
produces field factors `E_j` that are finite `ℚ_[p]`-algebras and whose
dimensions sum to the tensor dimension:
`tensorCore_finrank_eq_sum` (`Mzk1P2TensorDetFactorActual.lean:47-55`), and
`exists_arithmeticTensorTuple_fieldProduct`
(`FinitePlaceArithmeticTensorBlockFields.lean:24-36`). The root extension `L_b`
is **not** one of those tensor factors. The P3 construction datum
`BlockProductAlignmentData` (`Mzk1P3NativeDReanchorActual.lean:33-41`) is
exactly the missing identification `J ≃ Bad` plus per-factor equivalences
`E_j ≃ rootNormedExtension T (JEquiv j)`. For the actual qVFam data the
one-factor block has `J = Unit` (not `Bad`), and the P3 cardinality obstruction
gives the necessary condition `card Bad ≤ finrank(block)`
(`Mzk1P3BlockProductAlignmentObstructionActual.lean:23-52`). So A1 is not a
field-product decomposition of the block; it asks to identify the tensor block
with a *different* carrier (a product of root extensions over the whole bad
family).

### 2.3 Base-prime mismatch (the fatal gap)

The bad places do not have a common rational prime in the current source. The
condition that would force one is

```lean
def NativeBadModuliFixedPrime (p : ℕ) : Prop :=
  ∀ b : Bad (nativePlaceSelection T), (completionRationalPrime b.1).val = p
```

(`Mzk1NativeBadPrimeSourceActual.lean:27-29`), and the file itself records the
source of a fixed prime as a GAP. This is the same A7 item marked in
`coord/P7-GATE-REVIEW.md` as "may be false" (Bad only has odd residue
characteristic, no fixed p). The literal A1 target silently assumes this
alignment and more: it uses one specific prime `qVFamTensorP T b` for the
whole family.

Even adding `NativeBadModuliFixedPrime` is not enough for the literal
statement: typeclass synthesis does not rewrite by a hypothesis, so each
factor's algebra would still have to be transported along
`qVFamTensorP T b' = p` (an `Eq.rec`/`▸` transport), and that transport is not
in the source data. The exact target is therefore ill-typed as written.

### 2.4 Quantitative consequences (probe theorems)

Instantiating the already-green canonical obstruction
(`Mzk1P3CanonicalEqualityObstructionActual.canonical_card_lt_finrank`,
lines 37-55, and `canonical_all_degree_one_of_card_eq_finrank`, lines 58-80)
at the qVFam one-factor block gives:

* `qVFam_card_lt_finrank_of_algEquiv_pi`: a common-base product algebra
  equivalence with some `b0` of `1 < finrank ℚ_[p] (rootNormedExtension T b0)`
  forces `card Bad < finrank(qVFamTensorBlock T b)`.
* `qVFam_card_lt_rootBase_finrank_of_algEquiv_pi`: hence
  `card Bad < finrank ℚ_[p_b] (rootBase T b)`.
* `qVFam_all_degree_one_of_card_eq_finrank`: in the equality case
  `card Bad = finrank(block)`, every root factor has `ℚ_p`-degree one.
  Thus the A1 equality case is *not* an equivalence theorem for actual qVFam
  data; it forces the root extensions (and, compatibly, the local base
  completions) to collapse to the base. Under the natural tower compatibility
  this means `[K_b' : ℚ_p] = 1` and `L_b' = K_b'` for all bad `b'`, leaving at
  most a degenerate `Bad`-singleton/degree-one situation.

Note the exact arithmetic of the common-base repair:
left `= [K_b : ℚ_p]`; right `= Σ_{b'} [L_b' : ℚ_p]`. The right side contains
the full `[L_b : ℚ_p] = [K_b : ℚ_p]·[L_b : K_b]` plus the other factors. This
is why even a common-base version cannot be an equality of vector spaces unless
the degrees collapse; the existing canonical theorem is the formal version of
this statement.

## 3. Correct candidate(s)

### 3.1 True per-place pair (use these, not the product equivalence)

1. **Base block = base completion** (matched prime):
   ```lean
   qVFamTensorBlock T b ≃ₐ[ℚ_[qVFamTensorP T b]] rootBase T b
   ```
   The dimension half is probe `qVFamTensorBlock_finrank`. The AlgEquiv is the
   next constructive task (see `4.1`). This is the honest content of the A1
   left-hand side.
2. **Root tensor block = root extension** (matched prime):
   ```lean
   rootTensorBlock T b ≃ₐ[ℚ_[qVFamTensorP T b]] rootNormedExtension T b
   ```
   `rootTensorBlock T b = FinitePadicTensor (fun _ : Unit => L_b)` is already
   defined (`PaperRootCompletionTensorActual.lean:178-181`), and its unit/theta
   images live there (lines 183-201). The one-factor tensor lemma of `4.1` gives
   the equivalence.

### 3.2 Correct global shape: per rational prime, not one `p_b`

Define the fiber of bad places with own prime `p`:

```lean
def badFiber (p : ℕ) : Type :=
  {b' : Bad (nativePlaceSelection T) // qVFamTensorP T b' = p}
```

(probe `badFiber`). Each fiber product
`(b' : badFiber p) → rootNormedExtension T b'.1` is the only canonical
single-base product (over `ℚ_[p]`), and even that requires transporting each
factor's own-prime algebra along the fiber equality. The probe records the
per-factor fact `rootNormedExtension_algebra_ownPrime`:
`Nonempty (Algebra ℚ_[qVFamTensorP T b'] (rootNormedExtension T b'))`.

The whole product over `Bad` is a product of fields with different base primes;
it is not a `ℚ_[p_b]`-algebra. A global A1 statement must therefore be a
dependent family of per-prime statements, or a statement at the level of
dimensions/log-volumes, not a single `≃ₐ[ℚ_[p_b]]`.

### 3.3 Honest A1 substitute for the consumers

The correct replacement for the A1 equality case in the P7 consumer chain is
the per-place dimension/log-volume relation, not an algebra equivalence:

* `finrank ℚ_[p_b] L_b = [L_b : K_b] * finrank ℚ_[p_b] K_b` (probe).
* Haar/log-volume transport with the degree factor:
  `Mzk1P3HaarScaleFactorLogActual.logMass_eq_add_log_addHaarScalarFactor`
  (the log-mass scale is exactly `log (addHaarScalarFactor)`), plus the product
  decompositions in `Mzk1P3ProductHaarPiActual` and the native tensor log
  comparison in `Mzk1P3NativeTensorLogComparisonActual` / `Mzk1P3ProductLogRatioActual`.
* The block-side carrier is `K_b`, not `L_b`; the root side is the separate
  `rootTensorBlock`. The `[L_b : K_b]`-factor enters the degree/determinant
  normalization exactly where the current `Mzk1P2TensorDetFactorActual` records
  the "missing arbitrary det law" (it is a scalar p-degree factor there).

Do not add `[∀ b', Algebra ℚ_[qVFamTensorP T b] (rootNormedExtension T b')]` as
a "source condition": it is an unjustified identification of all base primes
with `p_b`, not a paper input, and even with it the dimension obstruction
remains.

## 4. Next actionable Lean statements

### 4.1 One-factor tensor algebra equivalence (no new mathematics)

Construct the generic one-factor tensor equivalence and specialize:

```lean
-- generic, in any commutative R and R-algebra K
noncomputable def piTensorProductUnitAlgEquiv (R K : Type*) [CommSemiring R] [Field K]
    [Algebra R K] : (⨂[R] _ : Unit, K) ≃ₐ[R] K

-- qVFam base block:
noncomputable def qVFamTensorBlock_algEquiv_rootBase :
    qVFamTensorBlock T b ≃ₐ[ℚ_[qVFamTensorP T b]] rootBase T b

-- root tensor block:
noncomputable def rootTensorBlock_algEquiv_rootNormedExtension :
    rootTensorBlock T b ≃ₐ[ℚ_[qVFamTensorP T b]] rootNormedExtension T b
```

Implementation route: `FinitePadicTensor (fun _ : Unit => K) = ⨂[ℚ_[p]] _ : Unit, K`
(`FinitePadicTensorTopology.lean:29`); use
`PiTensorProduct.subsingletonEquiv ()` (`Mathlib/LinearAlgebra/PiTensorProduct/Basic.lean:804`)
and `AlgEquiv.ofLinearEquiv` with the one/mul proofs (as in
`FiniteTensorProductDistribution.tensorProductAlgEquiv`), or
`PiTensorProduct.liftAlgHom` + `PiTensorProduct.singleAlgHom`
(`Mathlib/RingTheory/PiTensorProduct.lean:207-211, 191-201`). Then specialize
along the definitional equalities `CommonPrimeCompletion (qVFamTensorPlace T b) = rootBase T b`
and `rootTensorBlock T b = FinitePadicTensor (fun _ : Unit => L_b)`.
This is the correct LHS identity and unblocks the per-place log-volume route.

### 4.2 Nontriviality of the root extension (the one real arithmetic input)

```lean
theorem one_lt_finrank_rootNormedExtension_of_not_dvd_exponent
    (h : ¬ (2 * l.value ∣ (qVFamily T b).exponent)) :
    1 < Module.finrank (rootBase T b) (rootNormedExtension T b)
```

Route: if `rootNormedElement T b ∈ rootBase T b`, apply the discrete valuation
`Valued.v` of the completion to `rootNormedElement_pow`
(`PaperRootCompletionTensorActual.lean:72-75`); using
`qValuation_eq_exp_neg_exponent` (`FinitePlaceQCandidateValuationActual.lean:41-46`)
this gives `2l ∣ exponent`, contradiction. Under
`TateUniformizerCondition` (`exponent = 1`) this makes the per-factor no-go
unconditional for that source reading. Without this input, the per-factor
statement remains conditionally false; this is the exact remaining arithmetic
gap, not a Lean gap.

### 4.3 Consumer statement (P7 #1/#6/#10)

Replace the impossible `blockEquiv` with:

```lean
theorem qVFam_block_dimension_factor :
    Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b)
      = (Module.finrank (rootBase T b) (rootNormedExtension T b)) *
        Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b)
```

(immediate from `qVFamTensorBlock_finrank` and
`rootNormedExtension_finrank_tower`), together with the
`logMass_eq_add_log_addHaarScalarFactor` transport. This is what the
`BlockProductAlignmentData` consumer should use instead of an algebra
equivalence.

## 5. Probe file and verification

File `tmp/sheaf/xif/paper/Mzk1A1TensorProdProbeActual.lean` (new file only; no
existing Lean file was modified).

Contents (all no-sorry/no-axiom):

| name | statement |
|---|---|
| `qVFamTensorBlock_finrank` | `finrank ℚ_[p_b] (qVFamTensorBlock T b) = finrank ℚ_[p_b] (rootBase T b)` |
| `rootNormedExtension_algebra_ownPrime` | per-factor own-prime algebra exists |
| `badFiber` | correct per-prime index set of the product side |
| `rootNormedExtension_finrank_tower` | tower law for `[L_b : ℚ_[p_b]]` |
| `no_algEquiv_rootNormedExtension_of_one_lt_finrank` | per-factor falsehood when `1 < [L_b:K_b]` |
| `A1ProductStatementWithCommonBase` | conditional common-base former (needs per-factor algebras) |
| `qVFam_card_lt_finrank_of_algEquiv_pi` | common-base AlgEquiv ⇒ `card Bad < finrank(block)` |
| `qVFam_card_lt_rootBase_finrank_of_algEquiv_pi` | ⇒ `card Bad < [K_b:ℚ_p]` |
| `qVFam_all_degree_one_of_card_eq_finrank` | equality case forces all root factors `ℚ_p`-degree 1 |

Verification:

* Local `lake env lean tmp/sheaf/xif/paper/Mzk1A1TensorProdProbeActual.lean`:
  **EXIT=0** (quick check of the new probe only; no existing file compiled).
* `#print axioms` on all six theorems: only `propext, Classical.choice, Quot.sound`.
  No `sorry`, no new axiom, no `True`/`PUnit` placeholder.
* Watchdog: file appended to `dag/watchdog/extra-targets.txt` and compiled by
  the running watchdog: `START ... 2026-11-13T20:19:41.595Z`, then
  `DONE EXIT=0 (106s) 2026-11-13T20:21:28.003Z`; olean
  `.lake/build/lib/lean/tmp/sheaf/xif/paper/Mzk1A1TensorProdProbeActual.olean`
  (222,448 B, 2026-11-14 04:21:27 local). Per-file log
  `dag/watchdog/logs/tmp_sheaf_xif_paper_Mzk1A1TensorProdProbeActual.lean.log`
  contains the same `#print axioms` output (only propext / Classical.choice /
  Quot.sound). The guarded results ledger records
  `EXIT=0 FILE=tmp/sheaf/xif/paper/Mzk1A1TensorProdProbeActual.lean`.

## 6. Consequence for the P7 A1 consumer

* A1 cannot be closed as an algebra equivalence (the old
  `BlockProductAlignmentData` route) for the actual qVFam data. The literal target is ill-typed; the common-base
  repair is obstructed by dimension and only possible in the degree-one
  collapse; the per-factor matched-prime equivalence is false unless the root
  extension is trivial.
* The correct next package is `4.1` (construct the true one-factor base/root
  algebra equivalences) plus `4.2` (nontriviality of the root extension under an
  explicit exponent condition), and the consumer re-route `4.3`.
* A7 (`NativeBadModuliFixedPrime`) is neither available nor sufficient: it
  would only make a common-base product well-typed up to transport, and the
  dimension obstruction survives.
* No fake completion was introduced: the two deliverables contain only proved
  statements, definitions, and the explicit conditional/gap statements above.


---

## A1.6 status after valuation composition (2026-11-14, stage4)

- Green: `Mzk1A1InverseLatticeNormActual` (`mem_lambdaLattice_iff`, `mem_qhatLattice_iff`, `inverseLambdaLattice_eq_normBall`, `qhatBall_subset_lambdaBall`), `Mzk1A1LatticeValuationIdentifyActual` (`inverseLambdaLattice_eq_inverseLattice`, `inverseLambdaLattice_eq_saturated_actual`), `Mzk1A1QhatSaturationReadoutActual` (`qVFamily_mem_saturatedLattice`, `signedReadout_eq_log_radius_sub_delta`), `Mzk1A1SignedReadoutProductActual` (product/weighted A1.6 with `totalDelta`).
- **Status: A1.6 conditional**, not unconditional. The local identity `(1/d_F)log(mu(qhatLattice)/mu(O)) = log||lambda|| - a1Delta` is unconditional (proved from actual measures); the qhat<->J_s saturated form is conditional on two explicit actual-source inputs that are **not yet proved**:
  1. `A1PrincipalLatticeRecognition`: `lambdaLattice T b = {y | m <= bval y}` for the actual normalized valuation order `bval` on `rootNormedExtension T b` and `m = v(lambda)`.
  2. `A1RamificationIdentity`: `bval (algebraMap (rootBase) (rootNormedExtension) x) = e * aval x` for the actual normalized base valuation `aval` and ramification index `e`.
- Both are concrete valuation statements, not arbitrary comparison hypotheses; the actual discrete DVR/uniformizer on `rootNormedExtension` exists (`PaperRootExtensionDiscreteValuationActual.rootDiscreteValuation`, `rootUniformizer`), but the base discrete valuation and the ramification theorem were not constructed in this batch.
- Do not report A1.6 as unconditionally closed. No hscale/hid/blockEquiv hypotheses were used.
