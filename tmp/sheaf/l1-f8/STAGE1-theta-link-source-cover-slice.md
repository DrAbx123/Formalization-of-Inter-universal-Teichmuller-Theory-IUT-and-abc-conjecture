# STAGE 1 — L1-F8 ThetaLinkSourceCover / Slice consumer scope

Status: phase-1 consumer/scope record only. No Lean file is created in this step. Nothing below is asserted as proved. This record uses the existing production donor `LeanFormal/IUT/IUTII/Theta/ThetaLinkSourceCover.lean`.

Sources read:
- coord/LAYER1-PLAN.md (L1-F8 row, L0.5 consumer row)
- LeanFormal/IUT/IUTII/Theta/ThetaLinkSourceCover.lean (declarations at lines 87–469)
- LeanFormal/IUT/IUTII/Theta/ThetaLinkAssembly.lean (abstract algebraic Theta-link header and declarations)

## 1. Exact donor object and quantifiers

The donor is the categorical model of IUT I, Example 3.2(v):

```lean
variable (diagram : Iut.SourceSemiGraphOfAnabelioids.{u})
variable (root : diagram.base.Vertex)
variable (Yddot : ConnectedTemperedCover diagram root)
variable (model : BaseFieldCoverModel diagram root)
variable (data : ThetaProductData diagram root Yddot model)
variable (factorization : SliceFactorization data)
```

Objects:
- `ConnectedTemperedCover diagram root := (connectedTemperedObjectProperty diagram root).FullSubcategory`; candidate model of `D_v = B^temp(X_v)^0`, not asserted equal to it.
- `BaseCover model`; candidate model of `D_v^⊢ = B(K_v)^0`, encoded by the explicit predicate `model.IsBaseFieldCover` and base object `model.base`.
- `YddotSlice diagram root Yddot := Over Yddot`; the slice `(D_v)_{Yddot_v}`.
- `ThetaProductData diagram root Yddot model`; explicit product cones `Yddot_v × A` with `fst`, `snd`, `lift`, universal property, and `snd_epi`.
- `ThetaCoverSubcategory data := (productFunctor data).EssImageSubcategory`; model of `D_v^Θ`.

Main donor statements:
```lean
def productFunctor (data : ThetaProductData diagram root Yddot model) :
  BaseCover model ⥤ YddotSlice diagram root Yddot

theorem productFunctor_full (data) (factorization : SliceFactorization data) :
  (productFunctor data).Full

noncomputable def thetaEquivalence (data) (factorization : SliceFactorization data) :
  BaseCover model ≌ ThetaCoverSubcategory data
```

The equivalence is conditional on `SliceFactorization`; faithfulness uses `ThetaProductData.snd_epi`; no global product instance for connected tempered covers is asserted.

## 2. Exact actual consumer

Consumer target: **L0.5 source Theta** (LAYER1-PLAN row L0.5), specifically the source side fed by:
- `AΘ` cover data;
- `Mq → MΘ` / source Theta unit comparison;
- source theta divisor/Kummer data;
- root/deck/tempered synchronization.

Consumer file(s) currently available:
- `LeanFormal/IUT/IUTII/Theta/ThetaLinkAssembly.lean` — the abstract algebraic link `unitGeneratedSubmonoid u q ≃* unitGeneratedSubmonoid v theta`, with unit/generator/orbit laws. It is **not** a geometric source-cover consumer.

Important negative finding: a search of `LeanFormal` and `Iut` found **no file importing** `ThetaLinkSourceCover`; the donor is currently not connected to any production consumer. L1-F8 therefore needs an explicit bridge file from the donor equivalence to the L0.5 source Theta package.

## 3. Missing identification to actual source

None of the following is currently proved:
1. an actual identification of `diagram` with the source semigraph of the real curve `X_v`;
2. an actual identification of `Yddot` with the source object `Yddot_v`;
3. an actual construction/proof of `BaseFieldCoverModel` from the paper's base field `K_v`;
4. an actual construction/proof of `ThetaProductData` (product objects, projections, universal property, `snd_epi`) from the source geometry;
5. an actual proof of `SliceFactorization` from the base-field condition;
6. the source `AΘ` cover / slice comparison and its map to `ThetaLinkAssembly`'s abstract monoids;
7. any transport of `thetaEquivalence` across the actual source objects.

## 4. Minimal freezeable local target (statement only)

`L1-F8-Consumer` (not yet created): a structure/statement whose fields are exactly the donor inputs and whose conclusion is the donor equivalence, plus a consumer theorem:

```lean
structure ThetaLinkSourceCoverConsumer where
  diagram : Iut.SourceSemiGraphOfAnabelioids.{u}
  root : diagram.base.Vertex
  Yddot : ConnectedTemperedCover diagram root
  model : BaseFieldCoverModel diagram root
  data : ThetaProductData diagram root Yddot model
  factorization : SliceFactorization data

theorem thetaLinkSourceCoverConsumer_equivalence
    (consumer : ThetaLinkSourceCoverConsumer) :
    BaseCover consumer.model ≌ ThetaCoverSubcategory consumer.data
```

This consumes the donor `thetaEquivalence`; it is still a generic categorical statement, not the real source curve.

`L1-F8-SourceBinding` (separate, later): actual identifications of `diagram`, `Yddot`, `model`, `data`, `factorization` with the source objects of `X_v`, plus the source `AΘ`/slice comparison. Do not identify the donor equivalence with a real source theorem by type cast.

## 5. Consumer-side status

- Donor equivalence: green in production at current file version (not recompiled in this step).
- Consumer file: not created; no file imports the donor (negative search result).
- L0.5 source Theta: not fed by this donor; no bridge exists.
- statement_compiles: not claimed for L1-F8.
- proof_body_checked / kernel_closed / target_accepted: not claimed.

## 6. Recommended next executable step

Freeze `ThetaLinkSourceCoverConsumer.lean` as a stage-2 statement that imports `ThetaLinkSourceCover` and exposes the exact equivalence type above. In parallel, record the actual `diagram`/`Yddot`/`model` source binding as a separate node; do not start by assuming `SliceFactorization` or the actual product data.
