import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorProductDistribution
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRealization
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellTransport
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActualTensorSpan
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorNontrivial
import tmp.sheaf.xif.paper.S1264SourceCapsuleInd1Actual

noncomputable section
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1474ReportBTensorRealizationActual

/-!
# S1474: route B actual tensor realization for the fixed source capsule/tuple

Gap report `coord/reports/gap-exploration-20261030.md`, route B: use the
genuine finite p-adic multi-factor tensor/hull donors and give the actual
factors, indices and a compatible realization for a fixed source capsule/tuple.

## The fixed source capsule

The finite p-adic tensor and hull donors are stated in the universe of the
actual finite local factors.  We therefore fix the source `OriginalInput` in
that universe (`Type`), which is the actual universe of the number field and
does not restrict the tuple or the number of factors.

The capsule is the source capsule of
`S1264SourceCapsuleInd1Actual.actualContract I n` at a fixed capsule level
`j < capsuleLevels l`, for a fixed `OriginalInput I` and procession index `n`.
Its rational place is the actual finite place `vQ : RationalPlaceAt l`, its
place type is the actual finite-place type `ActualPlace I` of `K` above the
fixed rational prime `l`, and its log-shell carrier at every label is the
actual common-prime completion `CommonPrimeCompletion v`.  The tuple

`t : (i : Capsule j) -> ActualPlace I`

is fixed.  The factor at label `i` is `CommonPrimeCompletion (t i)`; every
label `i` of `Capsule j = Fin (j+1)` occurs.  The packet is the tensor of the
actual function spaces over all places, and its distribution equivalence is
the actual `tensorPacketEquiv` of the source contract, not an arbitrary
function.

## What is constructed

* the actual factor family and both tensor blocks (`SourceBlk`, `SourcePacket`);
* the actual index cardinalities and the full tuple type `SourceTup`;
* the actual source `TensorPacket` identification and pure-tensor distribution
  law (`sourcePacket_eq_actualContract_tensorPacket`,
  `sourceProductTupleEquiv_toLinearEquiv_eq_contract`);
* the actual log-shell datum at each factor, its integral log-shell equality,
  its `IQSpan = top`, and the `SourceLogShellActualIQTensor` equivalence;
* a field-product decomposition by the proved finite etale classification,
  with continuous inverse;
* the finite log-shell hull realization: nonzero `lam`, exact hull equality,
  compactness, unit-region inclusion, positive finite Haar masses and the
  normalized log laws;
* transport of the hull under change of decomposition, through the actual
  composite algebra equivalence;
* the direct `FinitePadicTensorLogShellRealization` form of the same
  realization for the fixed source factors.

No arbitrary realization function, no constant zero map, and no reduced number
of factors is used.  The remaining source-level limitations, not claimed as
closed here, are the comparison of the rational `ActualTensorSpan` level with
the `Qp` tensor, the full Ind/Theta image family, and the final xi-f
comparison.
-/

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual

universe uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (n : Int) (vQ : RationalPlaceAt l)

/-- The actual rational prime of `PrimeGeFive` as a local instance. -/
local instance factPrimeOfPrimeGeFiveS1474 (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

/-! ## 1. Fixed source factors and indices -/

/-- The fixed tuple of actual finite places over the fixed rational place,
one place for every capsule label. -/
abbrev SourceTup (j : Nat) : Type _ :=
  Capsule j → ActualPlace I

/-- The actual factor family: at a label and a place it is the actual
common-prime completion.  It does not depend on the capsule label because the
source contract uses the same actual completion family at every label, but the
tuple still selects the actual factor at every label. -/
abbrev SourceFamily (j : Nat) : (i : Capsule j) → ActualPlace I → Type _ :=
  fun _ v => CommonPrimeCompletion v

/-- The actual tensor packet over the fixed rational place: tensor over all
capsule labels of the product of actual completions over the places. -/
abbrev SourcePacket (j : Nat) : Type _ :=
  FinitePadicTensor (p := l.value)
    (fun _ : Capsule j => (v : ActualPlace I) → CommonPrimeCompletion v)

/-- The actual tuple block: tensor over all capsule labels of the selected
actual completion.  No label is omitted. -/
abbrev SourceBlk (j : Nat) (t : SourceTup (I := I) j) : Type _ :=
  FinitePadicTensor (p := l.value) (fun i => CommonPrimeCompletion (t i))

/-- The packet is the tensor over all capsule labels of the actual place
function spaces. -/
theorem sourcePacket_tensor_factors (j : Nat) :
    SourcePacket (I := I) (l := l) j =
      ⨂[ℚ_[l.value]] _i : Capsule j,
        ((v : ActualPlace I) → CommonPrimeCompletion v) := rfl

/-- The tuple block is the tensor of all actual factors at the fixed tuple. -/
theorem sourceBlk_tensor_factors (j : Nat) (t : SourceTup (I := I) j) :
    SourceBlk (I := I) (l := l) (j := j) (t := t) =
      ⨂[ℚ_[l.value]] i : Capsule j, CommonPrimeCompletion (t i) := rfl

/-- The actual factor at a tuple index is exactly the common-prime completion
of the selected actual place. -/
theorem sourceFactor_eq_actualCompletion (j : Nat) (t : SourceTup (I := I) j)
    (i : Capsule j) :
    SourceFamily (I := I) (l := l) j i (t i) = CommonPrimeCompletion (t i) := rfl

/-- The fixed capsule has exactly the paper's `j+1` labels. -/
theorem sourceCapsule_card (j : Nat) :
    Fintype.card (Capsule j) = j + 1 := capsule_card j

/-- The full tuple type has the expected cardinality: one actual place for
each of the `j+1` capsule labels. -/
theorem sourceTuple_card (j : Nat) :
    Fintype.card (SourceTup (I := I) j) =
      (Fintype.card (ActualPlace I)) ^ (j + 1) := by
  change Fintype.card (Fin (j + 1) → ActualPlace I) = _
  rw [Fintype.card_fun, Fintype.card_fin]

/-! ## 2. The actual source tensor packet and its distribution -/

/-- The packet is exactly the actual `TensorPacket` of the source
`actualLogShellFamily` from S1264. -/
theorem sourcePacket_eq_actualTensorPacket (j : Nat) :
    SourcePacket (I := I) (l := l) j =
      TensorPacket (actualLogShellFamily I j) vQ := rfl

/-- At a source capsule level, the packet is exactly the tensor packet of the
actual source contract `actualContract I n`. -/
theorem sourcePacket_eq_actualContract_tensorPacket (j : Nat)
    (hj : j < capsuleLevels l) :
    SourcePacket (I := I) (l := l) j =
      SourceProcessionCapsuleContract.tensorPacket (R := ℚ_[l.value])
        (actualContract I n) ⟨j, hj⟩ vQ := rfl

/-- The continuous distribution equivalence from the actual packet to all
tuple blocks.  It is the genuine finite tensor-product distribution, with
every capsule label and every actual factor retained. -/
noncomputable def sourceProductTupleEquiv (j : Nat) :
    SourcePacket (I := I) (l := l) j ≃L[ℚ_[l.value]]
      ((t : SourceTup (I := I) j) → SourceBlk (I := I) (l := l) (j := j) (t := t)) :=
  finitePadicTensorProductLinearEquiv (p := l.value)
    (M := SourceFamily (I := I) (l := l) j)

/-- The distribution equivalence on an actual pure tensor is the coordinatewise
tensor, exactly as in the source `TensorPacket` distribution law. -/
theorem sourceProductTupleEquiv_tprod (j : Nat)
    (x : (i : Capsule j) → (v : ActualPlace I) → CommonPrimeCompletion v)
    (t : SourceTup (I := I) j) :
    sourceProductTupleEquiv (I := I) (l := l) (j := j)
        (finitePadicTensorTprod (p := l.value) _ x) t =
      finitePadicTensorTprod (p := l.value) _
        (fun i => x i (t i)) :=
  finitePadicTensorProductLinearEquiv_tprod (p := l.value)
    (M := SourceFamily (I := I) (l := l) j) x t

/-- The actual linear distribution equivalence of the source contract. -/
noncomputable def sourceContractTupleEquiv (j : Nat) (hj : j < capsuleLevels l) :
    SourcePacket (I := I) (l := l) j ≃ₗ[ℚ_[l.value]]
      ((t : SourceTup (I := I) j) → SourceBlk (I := I) (l := l) (j := j) (t := t)) :=
  SourceProcessionCapsuleContract.tensorPacketEquiv (R := ℚ_[l.value])
    (actualContract I n) ⟨j, hj⟩ vQ

/-- The continuous distribution equivalence of the product-distribution donor
is exactly the source contract's distribution equivalence. -/
theorem sourceProductTupleEquiv_toLinearEquiv_eq_contract (j : Nat)
    (hj : j < capsuleLevels l) :
    (sourceProductTupleEquiv (I := I) (l := l) (j := j)).toLinearEquiv =
      sourceContractTupleEquiv (I := I) (n := n) (vQ := vQ) (j := j) (hj := hj) := rfl

/-- The source contract's distribution equivalence has the actual pure-tensor
law. -/
theorem sourceContractTupleEquiv_tprod (j : Nat) (hj : j < capsuleLevels l)
    (x : (i : Capsule j) → (v : ActualPlace I) → CommonPrimeCompletion v)
    (t : SourceTup (I := I) j) :
    sourceContractTupleEquiv (I := I) (n := n) (vQ := vQ) (j := j) (hj := hj)
        (PiTensorProduct.tprod ℚ_[l.value] x) t =
      PiTensorProduct.tprod ℚ_[l.value] (fun i => x i (t i)) := by
  change tensorPacketEquiv (actualLogShellFamily I j) vQ
      (PiTensorProduct.tprod ℚ_[l.value] x) t =
    PiTensorProduct.tprod ℚ_[l.value] (fun i => x i (t i))
  exact tensorPacketEquiv_tprod (actualLogShellFamily I j) vQ x t

/-- No factor is dropped: the continuous distribution equivalence is bijective
on the full tuple space. -/
theorem sourceProductTupleEquiv_bijective (j : Nat) :
    Function.Bijective (sourceProductTupleEquiv (I := I) (l := l) (j := j)) :=
  (sourceProductTupleEquiv (I := I) (l := l) (j := j)).bijective

/-! ## 3. The actual `ActualTensorSpan` rational level -/

/-- The actual local log-shell datum at a selected actual place. -/
noncomputable abbrev sourceDatum (j : Nat) (t : SourceTup (I := I) j)
    (i : Capsule j) : SourceLogShellDatum :=
  sourceLocalLogShellDatum (p := l.value) (t i)

/-- The actual log-shell of the source datum is the actual integral log-shell
of the selected completion. -/
theorem sourceDatum_logShell_eq (j : Nat) (t : SourceTup (I := I) j)
    (i : Capsule j) :
    (sourceDatum (I := I) (j := j) (t := t) (i := i)).logShell =
      (integralLogShell (K := CommonPrimeCompletion (t i)) (p := l.value) :
        Set (CommonPrimeCompletion (t i))) :=
  sourceLocalLogShellDatum_logShell_eq_integralLogShell (p := l.value) (t i)

/-- The source datum's log-shell is the actual local log-shell recorded in
S1264 for the same actual place. -/
theorem sourceDatum_logShell_eq_actualLocalLogShell (j : Nat)
    (t : SourceTup (I := I) j) (i : Capsule j) :
    (sourceDatum (I := I) (j := j) (t := t) (i := i)).logShell =
      actualLocalLogShell I (t i) := rfl

/-- The actual integral log-shell spans the whole local field rationally. -/
theorem sourceDatum_IQSpan_eq_top (j : Nat) (t : SourceTup (I := I) j)
    (i : Capsule j) :
    (sourceDatum (I := I) (j := j) (t := t) (i := i)).IQSpan = ⊤ := by
  rw [SourceLogShellDatum.IQSpan, sourceDatum_logShell_eq]
  exact rat_span_integralLogShell_eq_top (p := l.value)
    (A := fun _ : Unit => CommonPrimeCompletion (t i)) ()

/-- The actual rational identification of each `IQSpan` factor with the
selected completion. -/
noncomputable def sourceIQSpanEquiv (j : Nat) (t : SourceTup (I := I) j)
    (i : Capsule j) :
    (sourceDatum (I := I) (j := j) (t := t) (i := i)).IQSpan ≃ₗ[ℚ]
      CommonPrimeCompletion (t i) :=
  (LinearEquiv.ofEq _ _
    (sourceDatum_IQSpan_eq_top (I := I) (j := j) (t := t) (i := i))).trans Submodule.topEquiv

/-- The actual `SourceLogShellActualIQTensor` of the fixed source factors is
the rational tensor of the actual completions. -/
noncomputable def sourceIQTensorEquiv (j : Nat) (t : SourceTup (I := I) j) :
    SourceLogShellActualIQTensor (sourceDatum (I := I) (j := j) (t := t)) ≃ₗ[ℚ]
      (⨂[ℚ] i : Capsule j, CommonPrimeCompletion (t i)) :=
  PiTensorProduct.congr (fun i => sourceIQSpanEquiv (I := I) (j := j) (t := t) (i := i))

/-- The rational IQ tensor equivalence has the actual pure-tensor formula. -/
theorem sourceIQTensorEquiv_tprod (j : Nat) (t : SourceTup (I := I) j)
    (x : (i : Capsule j) → CommonPrimeCompletion (t i)) :
    sourceIQTensorEquiv (I := I) (j := j) (t := t)
        (PiTensorProduct.tprod ℚ (fun i =>
          (⟨x i, by rw [sourceDatum_IQSpan_eq_top (I := I) (j := j) (t := t) (i := i)]; trivial⟩ :
            (sourceDatum (I := I) (j := j) (t := t) (i := i)).IQSpan))) =
      PiTensorProduct.tprod ℚ x := by
  rw [sourceIQTensorEquiv, PiTensorProduct.congr_tprod]
  rfl

/-- The actual integral pure tensors span the whole actual IQ tensor. -/
theorem sourceIQTensor_integralTensors_span_eq_top (j : Nat)
    (t : SourceTup (I := I) j) :
    Submodule.span ℚ
      (sourceLogShellActualIntegralTensors (sourceDatum (I := I) (j := j) (t := t))) = ⊤ :=
  sourceLogShellActualIntegralTensors_span_eq_top
    (sourceDatum (I := I) (j := j) (t := t))

/-! ## 4. The actual field-product decomposition -/

/-- A field-product decomposition of the actual source tuple block, with the
finite normed output fields and the continuous inverse. -/
structure SourceFieldProductDecomposition (j : Nat) (t : SourceTup (I := I) j) where
  J : Type
  [fintypeJ : Fintype J]
  E : J → Type
  [normedField : ∀ j, NontriviallyNormedField (E j)]
  [normedAlgebra : ∀ j, NormedAlgebra ℚ_[l.value] (E j)]
  [finiteDimensional : ∀ j, FiniteDimensional ℚ_[l.value] (E j)]
  [completeSpace : ∀ j, CompleteSpace (E j)]
  [ultrametric : ∀ j, IsUltrametricDist (E j)]
  [properSpace : ∀ j, ProperSpace (E j)]
  equiv : SourceBlk (I := I) (l := l) (j := j) (t := t) ≃ₐ[ℚ_[l.value]] ((j : J) → E j)
  continuous_equiv : Continuous equiv
  continuous_symm : Continuous equiv.symm

/-- The proved finite etale decomposition supplies an actual field-product
decomposition of every fixed source tuple block. -/
theorem exists_sourceFieldProductDecomposition (j : Nat)
    (t : SourceTup (I := I) j) :
    Nonempty (SourceFieldProductDecomposition (I := I) (l := l) (j := j) (t := t)) := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, he, hinv⟩ :=
    exists_finiteNormedFieldProduct_piTensor (p := l.value)
      (A := fun i => CommonPrimeCompletion (t i))
  letI : Fintype J := hJ
  letI : ∀ j, NontriviallyNormedField (E j) := hfield
  letI : ∀ j, NormedAlgebra ℚ_[l.value] (E j) := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[l.value] (E j) := fun j => (hE j).1
  letI : ∀ j, CompleteSpace (E j) := fun j => (hE j).2.1
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[l.value] (E j)
  exact ⟨{
    J := J
    fintypeJ := hJ
    E := E
    normedField := hfield
    normedAlgebra := halgebra
    finiteDimensional := fun j => (hE j).1
    completeSpace := fun j => (hE j).2.1
    ultrametric := fun j => (hE j).2.2
    properSpace := fun j => FiniteDimensional.proper ℚ_[l.value] (E j)
    equiv := e
    continuous_equiv := he
    continuous_symm := hinv }⟩

/-- Every actual decomposition equivalence is injective. -/
theorem sourceDecomposition_equiv_injective {j : Nat} {t : SourceTup (I := I) j}
    (D : SourceFieldProductDecomposition (I := I) (l := l) (j := j) (t := t)) :
    Function.Injective D.equiv := by
  letI := D.fintypeJ
  letI := D.normedField
  letI := D.normedAlgebra
  letI := D.finiteDimensional
  letI := D.completeSpace
  letI := D.ultrametric
  letI := D.properSpace
  exact D.equiv.injective

/-- The actual tuple block is nontrivial, so the realization cannot be a
constant zero map onto a zero carrier. -/
theorem sourceBlk_nontrivial (j : Nat) (t : SourceTup (I := I) j) :
    Nontrivial (SourceBlk (I := I) (l := l) (j := j) (t := t)) :=
  finitePadicTensorNontrivial (p := l.value)
    (M := fun i => CommonPrimeCompletion (t i))

/-- The actual source log-shell region of the fixed factors is exactly the
pure-tensor image of the actual source log-shells. -/
theorem sourceTensorLogShellRegion_eq_datum (j : Nat)
    (t : SourceTup (I := I) j) :
    tensorLogShellRegion (p := l.value)
        (fun i => CommonPrimeCompletion (t i)) =
      finitePadicTensorTprod (p := l.value)
          (fun i => CommonPrimeCompletion (t i)) ''
        Set.pi Set.univ (fun i => (sourceDatum (I := I) (j := j) (t := t) (i := i)).logShell) := by
  unfold tensorLogShellRegion
  congr 1
  ext x
  constructor
  · intro hx i hi
    simpa [sourceDatum_logShell_eq (I := I) (j := j) (t := t) (i := i)] using hx i hi
  · intro hx i hi
    simpa [sourceDatum_logShell_eq (I := I) (j := j) (t := t) (i := i)] using hx i hi

/-- The same region is exactly the pure-tensor image of S1264's actual local
log-shells at the selected places. -/
theorem sourceTensorLogShellRegion_eq_actualLocalLogShell (j : Nat)
    (t : SourceTup (I := I) j) :
    tensorLogShellRegion (p := l.value)
        (fun i => CommonPrimeCompletion (t i)) =
      finitePadicTensorTprod (p := l.value)
          (fun i => CommonPrimeCompletion (t i)) ''
        Set.pi Set.univ (fun i => actualLocalLogShell I (t i)) := by
  rw [sourceTensorLogShellRegion_eq_datum]
  rfl

/-! ## 5. The compatible finite log-shell hull realization -/

open MeasureTheory

/-- The complete realization specification for a fixed actual decomposition:
nonzero scale, exact hull equality, compactness, unit-region inclusion,
positive finite Haar masses and the normalized log laws. -/
def SourceRealizationSpec (j : Nat) (t : SourceTup (I := I) j)
    (D : SourceFieldProductDecomposition (I := I) (l := l) (j := j) (t := t)) : Prop :=
  letI : Fintype D.J := D.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D.E j) := D.normedField
  letI : ∀ j, NormedAlgebra ℚ_[l.value] (D.E j) := D.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[l.value] (D.E j) := D.finiteDimensional
  letI : ∀ j, CompleteSpace (D.E j) := D.completeSpace
  letI : ∀ j, IsUltrametricDist (D.E j) := D.ultrametric
  letI : ∀ j, ProperSpace (D.E j) := D.properSpace
  letI : MeasurableSpace ((j : D.J) → D.E j) := borel _
  letI : BorelSpace ((j : D.J) → D.E j) := ⟨rfl⟩
  ∃ lam : (j : D.J) → D.E j, (∀ j, lam j ≠ 0) ∧
    hull (tensorLogShellProductImage (A := fun i => CommonPrimeCompletion (t i)) D.equiv) =
      region lam ∧
    IsCompact (hull (tensorLogShellProductImage
      (A := fun i => CommonPrimeCompletion (t i)) D.equiv)) ∧
    unitRegion (K := D.E) ⊆ hull (tensorLogShellProductImage
      (A := fun i => CommonPrimeCompletion (t i)) D.equiv) ∧
    0 < Measure.addHaar (unitRegion (K := D.E)) ∧
    Measure.addHaar (unitRegion (K := D.E)) < ⊤ ∧
    0 < Measure.addHaar (hull (tensorLogShellProductImage
      (A := fun i => CommonPrimeCompletion (t i)) D.equiv)) ∧
    Measure.addHaar (hull (tensorLogShellProductImage
      (A := fun i => CommonPrimeCompletion (t i)) D.equiv)) < ⊤ ∧
    normalizedLogVolume Measure.addHaar (unitRegion (K := D.E)) = 0 ∧
    0 ≤ normalizedLogVolume Measure.addHaar
      (hull (tensorLogShellProductImage
        (A := fun i => CommonPrimeCompletion (t i)) D.equiv))

/-- The realization specification is proved for every actual decomposition of
the fixed source tuple; no realization field is assumed. -/
theorem sourceRealizationSpec (j : Nat) (t : SourceTup (I := I) j)
    (D : SourceFieldProductDecomposition (I := I) (l := l) (j := j) (t := t)) :
    SourceRealizationSpec (I := I) (j := j) (t := t) (D := D) := by
  letI : Fintype D.J := D.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D.E j) := D.normedField
  letI : ∀ j, NormedAlgebra ℚ_[l.value] (D.E j) := D.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[l.value] (D.E j) := D.finiteDimensional
  letI : ∀ j, CompleteSpace (D.E j) := D.completeSpace
  letI : ∀ j, IsUltrametricDist (D.E j) := D.ultrametric
  letI : ∀ j, ProperSpace (D.E j) := D.properSpace
  obtain ⟨lam, hlam, hhull⟩ :=
    exists_tensorLogShellHull_eq_region (A := fun i => CommonPrimeCompletion (t i)) D.equiv
  letI : MeasurableSpace ((j : D.J) → D.E j) := borel _
  letI : BorelSpace ((j : D.J) → D.E j) := ⟨rfl⟩
  have hunit := measure_unitRegion_pos_lt_top (E := D.E) Measure.addHaar
  have hlog := measure_tensorLogShellHull_pos_lt_top
    (A := fun i => CommonPrimeCompletion (t i)) D.equiv Measure.addHaar
  exact ⟨lam, hlam, hhull,
    isCompact_tensorLogShellHull (A := fun i => CommonPrimeCompletion (t i)) D.equiv,
    unitRegion_subset_tensorLogShellHull (A := fun i => CommonPrimeCompletion (t i)) D.equiv,
    hunit.1, hunit.2, hlog.1, hlog.2, normalizedLogVolume_unitRegion _,
    tensorLogShellHull_logVolume_nonneg (A := fun i => CommonPrimeCompletion (t i)) D.equiv
      Measure.addHaar⟩

/-- For every fixed source tuple there is an actual decomposition carrying the
full realization. -/
theorem exists_sourceRealization (j : Nat) (t : SourceTup (I := I) j) :
    ∃ D : SourceFieldProductDecomposition (I := I) (l := l) (j := j) (t := t),
      SourceRealizationSpec (I := I) (j := j) (t := t) (D := D) := by
  obtain ⟨D⟩ := exists_sourceFieldProductDecomposition (I := I) (j := j) (t := t)
  exact ⟨D, sourceRealizationSpec (I := I) (j := j) (t := t) (D := D)⟩

/-- The direct `FinitePadicTensorLogShellRealization` form of the same fixed
source realization.  Its `e` is a field-product decomposition of the actual
tuple block, and all analytic properties are the donor's constructed ones. -/
theorem exists_sourceRealization_donor (j : Nat) (t : SourceTup (I := I) j) :
    ∃ (J : Type) (_ : Fintype J) (E : J → Type)
      (_ : ∀ j, NontriviallyNormedField (E j))
      (_ : ∀ j, NormedAlgebra ℚ_[l.value] (E j))
      (_ : ∀ j, FiniteDimensional ℚ_[l.value] (E j))
      (_ : ∀ j, ProperSpace (E j))
      (_ : ∀ j, IsUltrametricDist (E j))
      (e : SourceBlk (I := I) (l := l) (j := j) (t := t) ≃ₐ[ℚ_[l.value]] ((j : J) → E j))
      (lam : (j : J) → E j),
      (∀ j, lam j ≠ 0) ∧
      hull (tensorLogShellProductImage
        (A := fun i => CommonPrimeCompletion (t i)) e) = region lam ∧
      IsCompact (hull (tensorLogShellProductImage
        (A := fun i => CommonPrimeCompletion (t i)) e)) ∧
      unitRegion (K := E) ⊆ hull (tensorLogShellProductImage
        (A := fun i => CommonPrimeCompletion (t i)) e) ∧
      (letI : MeasurableSpace ((j : J) → E j) := borel _
       letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
       0 < Measure.addHaar (unitRegion (K := E)) ∧
       Measure.addHaar (unitRegion (K := E)) < ⊤ ∧
       0 < Measure.addHaar (hull (tensorLogShellProductImage
         (A := fun i => CommonPrimeCompletion (t i)) e)) ∧
       Measure.addHaar (hull (tensorLogShellProductImage
         (A := fun i => CommonPrimeCompletion (t i)) e)) < ⊤ ∧
       normalizedLogVolume Measure.addHaar (unitRegion (K := E)) = 0 ∧
       0 ≤ normalizedLogVolume Measure.addHaar
         (hull (tensorLogShellProductImage
           (A := fun i => CommonPrimeCompletion (t i)) e))) :=
  exists_realized_tensorLogShell_hull (p := l.value)
    (A := fun i => CommonPrimeCompletion (t i))

/-! ## 6. Compatibility under change of actual decomposition -/

/-- Two actual decompositions of the same fixed source tuple give the same hull
up to the actual composite algebra equivalence. -/
def SourceTransportSpec (j : Nat) (t : SourceTup (I := I) j)
    (D₁ D₂ : SourceFieldProductDecomposition (I := I) (l := l) (j := j) (t := t)) : Prop :=
  letI : Fintype D₁.J := D₁.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D₁.E j) := D₁.normedField
  letI : ∀ j, NormedAlgebra ℚ_[l.value] (D₁.E j) := D₁.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[l.value] (D₁.E j) := D₁.finiteDimensional
  letI : ∀ j, CompleteSpace (D₁.E j) := D₁.completeSpace
  letI : ∀ j, IsUltrametricDist (D₁.E j) := D₁.ultrametric
  letI : ∀ j, ProperSpace (D₁.E j) := D₁.properSpace
  letI : Fintype D₂.J := D₂.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D₂.E j) := D₂.normedField
  letI : ∀ j, NormedAlgebra ℚ_[l.value] (D₂.E j) := D₂.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[l.value] (D₂.E j) := D₂.finiteDimensional
  letI : ∀ j, CompleteSpace (D₂.E j) := D₂.completeSpace
  letI : ∀ j, IsUltrametricDist (D₂.E j) := D₂.ultrametric
  letI : ∀ j, ProperSpace (D₂.E j) := D₂.properSpace
  (D₁.equiv.symm.trans D₂.equiv) ''
      hull (tensorLogShellProductImage
        (A := fun i => CommonPrimeCompletion (t i)) D₁.equiv) =
    hull (tensorLogShellProductImage
      (A := fun i => CommonPrimeCompletion (t i)) D₂.equiv)

/-- The transport compatibility is proved, not assumed: the composite of the
two actual algebra equivalences carries the actual hull of the first
decomposition onto the actual hull of the second. -/
theorem sourceTransportSpec (j : Nat) (t : SourceTup (I := I) j)
    (D₁ D₂ : SourceFieldProductDecomposition (I := I) (l := l) (j := j) (t := t)) :
    SourceTransportSpec (I := I) (j := j) (t := t) (D₁ := D₁) (D₂ := D₂) := by
  letI : Fintype D₁.J := D₁.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D₁.E j) := D₁.normedField
  letI : ∀ j, NormedAlgebra ℚ_[l.value] (D₁.E j) := D₁.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[l.value] (D₁.E j) := D₁.finiteDimensional
  letI : ∀ j, CompleteSpace (D₁.E j) := D₁.completeSpace
  letI : ∀ j, IsUltrametricDist (D₁.E j) := D₁.ultrametric
  letI : ∀ j, ProperSpace (D₁.E j) := D₁.properSpace
  letI : Fintype D₂.J := D₂.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D₂.E j) := D₂.normedField
  letI : ∀ j, NormedAlgebra ℚ_[l.value] (D₂.E j) := D₂.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[l.value] (D₂.E j) := D₂.finiteDimensional
  letI : ∀ j, CompleteSpace (D₂.E j) := D₂.completeSpace
  letI : ∀ j, IsUltrametricDist (D₂.E j) := D₂.ultrametric
  letI : ∀ j, ProperSpace (D₂.E j) := D₂.properSpace
  exact tensorLogShellHull_decomposition_change
    (A := fun i => CommonPrimeCompletion (t i)) D₁.equiv D₂.equiv

/-! ## 7. Axiom probes -/

#print axioms sourceProductTupleEquiv_tprod
#print axioms sourceContractTupleEquiv_tprod
#print axioms sourceIQTensorEquiv_tprod
#print axioms exists_sourceFieldProductDecomposition
#print axioms sourceRealizationSpec
#print axioms exists_sourceRealization
#print axioms exists_sourceRealization_donor
#print axioms sourceTransportSpec

end LeanFormal.IUT.XiFPaper.S1474ReportBTensorRealizationActual
