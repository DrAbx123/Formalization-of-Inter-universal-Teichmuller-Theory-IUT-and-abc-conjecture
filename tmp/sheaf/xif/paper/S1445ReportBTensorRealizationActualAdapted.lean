import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorProductDistribution
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorFieldDecomposition
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActualTensorSpan
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellRealization
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorLogShellTransport

noncomputable section
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1445ReportBTensorRealizationActualAdapted

/-!
# S1445: route B actual tensor realization for a fixed source capsule/tuple

Gap report coord/reports/gap-exploration-20261030.md, route B: use the genuine
finite p-adic multi-factor tensor/hull donors and give the actual factors,
indices and a compatible realization for a fixed source capsule/tuple. This
file does that for the fixed finite capsule Capsule j = Fin (j+1) and the
fixed place tuple t : (i : Capsule j) -> Place vQ.

## What is fixed, and what is constructed

* fixed source data: p, j, VQ, Place, vQ, the actual local factors A i v,
  and the tuple t; no factor of the capsule is omitted;
* actual tensor packet: Packet = tensor over the capsule of the direct sums
  over the places, with the actual distribution equivalence productTupleEquiv
  to the tuple-indexed tensor blocks;
* actual source log-shell data: sourceDatum t i, whose log-shell is the
  constructed integralLogShell, and whose rational span is the whole local
  field; this gives the ActualTensorSpan-level tensor
  SourceLogShellActualIQTensor;
* field-product decomposition: exists_fpd applies the proved finite etale
  field decomposition to the same tensor block, with continuous inverse;
* compatible realization: FullRealizationSpec gives a nonzero hull scale lam,
  the exact hull equality, compactness, the unit-region inclusion, Haar
  positivity/finiteness and the normalized log laws;
* change of decomposition: transportSpec proves that the actual composite
  algebra equivalence carries one hull onto the other.

No arbitrary realization function, no constant zero map, and no reduced number
of factors is used. The rational ActualTensorSpan layer is kept separate from
the Qp tensor packet: no identification of the rational Q-span with the Qp
tensor is asserted. The remaining source-level limitations, not claimed as
closed here, are the comparison of these two scalar levels, the full Ind/Theta
image family, and the final xi-f comparison.
-/

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

universe u v

variable {p : ℕ} [Fact p.Prime] {j : ℕ}
variable {VQ : Type u} {Place : VQ → Type v} (vQ : VQ) [Fintype (Place vQ)]
variable (A : (i : Capsule j) → Place vQ → Type)
variable [∀ i v, NormedField (A i v)]
variable [∀ i v, NormedAlgebra ℚ_[p] (A i v)]
variable [∀ i v, FiniteDimensional ℚ_[p] (A i v)]
variable [∀ i v, CharZero (A i v)]
variable [∀ i v, IsUltrametricDist (A i v)]
variable [∀ i v, CompleteSpace (A i v)]
variable [∀ i v, ProperSpace (A i v)]

abbrev Tup := (i : Capsule j) → Place vQ

/-- The fixed capsule has exactly the source labels 0, ..., j. -/
theorem capsule_card_actual : Fintype.card (Capsule j) = j + 1 := capsule_card j

/-- The actual factor at capsule label i and tuple t is the source local field
`A i (t i)`. -/
abbrev Blk (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) :=
  FinitePadicTensor (p := p) (fun i => A i (t i))

/-- The block is the tensor of all capsule factors, with no factor dropped. -/
theorem block_tensor_factors (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) :
    Blk (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t =
      ⨂[ℚ_[p]] i : Capsule j, A i (t i) := rfl

structure FieldProductDecomposition (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) where
  J : Type
  fintypeJ : Fintype J
  E : J → Type
  normedField : ∀ j, NontriviallyNormedField (E j)
  normedAlgebra : ∀ j, NormedAlgebra ℚ_[p] (E j)
  finiteDimensional : ∀ j, FiniteDimensional ℚ_[p] (E j)
  completeSpace : ∀ j, CompleteSpace (E j)
  ultrametric : ∀ j, IsUltrametricDist (E j)
  properSpace : ∀ j, ProperSpace (E j)
  equiv : Blk (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t ≃ₐ[ℚ_[p]] ((j : J) → E j)
  continuous_equiv : Continuous equiv
  continuous_symm : Continuous equiv.symm

theorem exists_fieldProductDecomposition (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) :
    Nonempty (FieldProductDecomposition (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t) := by
  obtain ⟨J, hJ, E, hfield, halgebra, e, hE, he, hinv⟩ :=
    exists_finiteNormedFieldProduct_piTensor (p := p) (A := fun i => A i (t i))
  letI : Fintype J := hJ
  letI : ∀ j, NontriviallyNormedField (E j) := hfield
  letI : ∀ j, NormedAlgebra ℚ_[p] (E j) := halgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (E j) := fun j => (hE j).1
  letI : ∀ j, CompleteSpace (E j) := fun j => (hE j).2.1
  letI : ∀ j, IsUltrametricDist (E j) := fun j => (hE j).2.2
  letI : ∀ j, ProperSpace (E j) := fun j => FiniteDimensional.proper ℚ_[p] (E j)
  exact ⟨{
    J := J
    fintypeJ := hJ
    E := E
    normedField := hfield
    normedAlgebra := halgebra
    finiteDimensional := fun j => (hE j).1
    completeSpace := fun j => (hE j).2.1
    ultrametric := fun j => (hE j).2.2
    properSpace := fun j => FiniteDimensional.proper ℚ_[p] (E j)
    equiv := e
    continuous_equiv := he
    continuous_symm := hinv }⟩

section Distribution

abbrev Packet := FinitePadicTensor (p := p) (fun i => (v : Place vQ) → A i v)

/-- The packet is the tensor over all capsule labels of the direct sums over
all places; no capsule label is omitted. -/
theorem packet_tensor_factors :
    Packet (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A =
      ⨂[ℚ_[p]] i : Capsule j, ((v : Place vQ) → A i v) := rfl

abbrev TupleDist := (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) →
  Blk (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t

def productTupleEquiv :
    Packet (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A ≃L[ℚ_[p]]
      TupleDist (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A :=
  finitePadicTensorProductLinearEquiv (p := p) (fun i (v : Place vQ) => A i v)

theorem productTupleEquiv_tprod
    (x : (i : Capsule j) → (v : Place vQ) → A i v)
    (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) :
    productTupleEquiv (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A
      (PiTensorProduct.tprod ℚ_[p] x) t =
      PiTensorProduct.tprod ℚ_[p] (fun i => x i (t i)) :=
  finitePadicTensorProductLinearEquiv_tprod (p := p)
    (M := fun i (v : Place vQ) => A i v) x t

theorem productTupleEquiv_bijective :
    Function.Bijective (productTupleEquiv (p := p) (j := j) (VQ := VQ)
      (Place := Place) (vQ := vQ) A) :=
  (productTupleEquiv (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A).bijective

end Distribution

section ActualSource

open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

theorem sourceLogShellStar_eq_logShellScale :
    sourceLogShellStar p = logShellScale p := by
  unfold sourceLogShellStar logShellScale
  rcases (Fact.out : Nat.Prime p).eq_two_or_odd with h2 | hodd
  · subst h2
    norm_num
  · rw [if_pos hodd, if_neg]
    exact fun h => by omega

theorem logShellScale_pos : 0 < logShellScale p := by
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  unfold logShellScale
  split <;> positivity

noncomputable abbrev datumOf (K : Type) [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedAlgebra ℚ_[p] K] [ProperSpace K] : SourceLogShellDatum where
  p := p
  hp := Fact.out
  K := K
  fieldK := inferInstance
  charZeroK := inferInstance
  Units := (Integers K)ˣ
  groupUnits := inferInstance
  invariants := ⊤
  logMap := unitLogHom (p := p)

theorem datumOf_logShell_eq (K : Type) [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedAlgebra ℚ_[p] K] [ProperSpace K] :
    (datumOf (p := p) K).logShell = (integralLogShell (K := K) (p := p) : Set K) := by
  have hD : (datumOf (p := p) K).logShell =
      {a : K | (sourceLogShellStar p : K) * a ∈ Set.range (fun u : (Integers K)ˣ => unitLog u)} := by
    ext a
    simp [datumOf, SourceLogShellDatum.logShell, SourceLogShellDatum.preLogShell,
      SourceLogShellDatum.pStar, unitLogHom]
  rw [hD]
  ext a
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    change (logShellScale p : K)⁻¹ * unitLog u = a
    have hu' : unitLog u = (sourceLogShellStar p : K) * a := hu
    rw [sourceLogShellStar_eq_logShellScale] at hu'
    rw [hu', ← mul_assoc, inv_mul_cancel₀, one_mul]
    exact Nat.cast_ne_zero.mpr (ne_of_gt logShellScale_pos)
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    change unitLog u = (sourceLogShellStar p : K) * a
    have hu' : (logShellScale p : K)⁻¹ * unitLog u = a := hu
    rw [← hu']
    rw [sourceLogShellStar_eq_logShellScale, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact Nat.cast_ne_zero.mpr (ne_of_gt logShellScale_pos)

theorem datumOf_IQSpan_eq_top (K : Type) [NormedField K] [CharZero K] [CompleteSpace K]
    [IsUltrametricDist K] [NormedAlgebra ℚ_[p] K] [ProperSpace K]
    [FiniteDimensional ℚ_[p] K] :
    (datumOf (p := p) K).IQSpan = ⊤ := by
  rw [SourceLogShellDatum.IQSpan, datumOf_logShell_eq]
  exact rat_span_integralLogShell_eq_top (p := p) (A := fun _ : Unit => K) ()

noncomputable abbrev sourceDatum (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ))
    (i : Capsule j) : SourceLogShellDatum :=
  datumOf (p := p) (K := A i (t i))

theorem sourceDatum_logShell_eq (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ))
    (i : Capsule j) :
    (sourceDatum (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t i).logShell =
      (integralLogShell (K := A i (t i)) (p := p) : Set (A i (t i))) :=
  datumOf_logShell_eq (p := p) (K := A i (t i))

theorem sourceDatum_IQSpan_eq_top (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ))
    (i : Capsule j) :
    (sourceDatum (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t i).IQSpan = ⊤ :=
  datumOf_IQSpan_eq_top (p := p) (K := A i (t i))

noncomputable def iqSpanEquiv (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ))
    (i : Capsule j) :
    (sourceDatum (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t i).IQSpan ≃ₗ[ℚ]
      A i (t i) :=
  (LinearEquiv.ofEq _ _ (sourceDatum_IQSpan_eq_top (p := p) (j := j) (VQ := VQ)
    (Place := Place) (vQ := vQ) A t i)).trans Submodule.topEquiv

noncomputable def actualIQTensorEquiv (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) :
    SourceLogShellActualIQTensor (sourceDatum (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t) ≃ₗ[ℚ]
      (⨂[ℚ] i : Capsule j, A i (t i)) :=
  PiTensorProduct.congr (fun i => iqSpanEquiv (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t i)

theorem actualIQTensorEquiv_tprod
    (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ))
    (x : (i : Capsule j) → A i (t i)) :
    actualIQTensorEquiv (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t
      (PiTensorProduct.tprod ℚ (fun i =>
        (⟨x i, by rw [sourceDatum_IQSpan_eq_top (p := p) (j := j) (VQ := VQ)
          (Place := Place) (vQ := vQ) A t i]; trivial⟩ : (sourceDatum (p := p) (j := j)
            (VQ := VQ) (Place := Place) (vQ := vQ) A t i).IQSpan))) =
      PiTensorProduct.tprod ℚ x := by
  rw [actualIQTensorEquiv, PiTensorProduct.congr_tprod]
  rfl

end ActualSource

section HullData

open MeasureTheory

def FullRealizationSpec (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ))
    (D : FieldProductDecomposition (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t) : Prop :=
  letI : Fintype D.J := D.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D.E j) := D.normedField
  letI : ∀ j, NormedAlgebra ℚ_[p] (D.E j) := D.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (D.E j) := D.finiteDimensional
  letI : ∀ j, CompleteSpace (D.E j) := D.completeSpace
  letI : ∀ j, IsUltrametricDist (D.E j) := D.ultrametric
  letI : ∀ j, ProperSpace (D.E j) := D.properSpace
  letI : MeasurableSpace ((j : D.J) → D.E j) := borel _
  letI : BorelSpace ((j : D.J) → D.E j) := ⟨rfl⟩
  ∃ lam : (j : D.J) → D.E j, (∀ j, lam j ≠ 0) ∧
    hull (tensorLogShellProductImage (A := fun i => A i (t i)) D.equiv) = region lam ∧
    IsCompact (hull (tensorLogShellProductImage (A := fun i => A i (t i)) D.equiv)) ∧
    unitRegion (K := D.E) ⊆ hull (tensorLogShellProductImage (A := fun i => A i (t i)) D.equiv) ∧
    0 < Measure.addHaar (unitRegion (K := D.E)) ∧
    Measure.addHaar (unitRegion (K := D.E)) < ⊤ ∧
    0 < Measure.addHaar (hull (tensorLogShellProductImage (A := fun i => A i (t i)) D.equiv)) ∧
    Measure.addHaar (hull (tensorLogShellProductImage (A := fun i => A i (t i)) D.equiv)) < ⊤ ∧
    normalizedLogVolume Measure.addHaar (unitRegion (K := D.E)) = 0 ∧
    0 ≤ normalizedLogVolume Measure.addHaar
      (hull (tensorLogShellProductImage (A := fun i => A i (t i)) D.equiv))

theorem fullRealizationSpec (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ))
    (D : FieldProductDecomposition (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t) :
    FullRealizationSpec (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t D := by
  letI : Fintype D.J := D.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D.E j) := D.normedField
  letI : ∀ j, NormedAlgebra ℚ_[p] (D.E j) := D.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (D.E j) := D.finiteDimensional
  letI : ∀ j, CompleteSpace (D.E j) := D.completeSpace
  letI : ∀ j, IsUltrametricDist (D.E j) := D.ultrametric
  letI : ∀ j, ProperSpace (D.E j) := D.properSpace
  obtain ⟨lam, hlam, hhull⟩ :=
    exists_tensorLogShellHull_eq_region (A := fun i => A i (t i)) D.equiv
  letI : MeasurableSpace ((j : D.J) → D.E j) := borel _
  letI : BorelSpace ((j : D.J) → D.E j) := ⟨rfl⟩
  have hunit := measure_unitRegion_pos_lt_top (E := D.E) Measure.addHaar
  have hlog := measure_tensorLogShellHull_pos_lt_top
    (A := fun i => A i (t i)) D.equiv Measure.addHaar
  exact ⟨lam, hlam, hhull,
    isCompact_tensorLogShellHull (A := fun i => A i (t i)) D.equiv,
    unitRegion_subset_tensorLogShellHull (A := fun i => A i (t i)) D.equiv,
    hunit.1, hunit.2, hlog.1, hlog.2, normalizedLogVolume_unitRegion _,
    tensorLogShellHull_logVolume_nonneg (A := fun i => A i (t i)) D.equiv Measure.addHaar⟩

theorem tuple_card :
    Fintype.card (Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) =
      (Fintype.card (Place vQ)) ^ (j + 1) := by
  change Fintype.card (Fin (j + 1) → Place vQ) = _
  rw [Fintype.card_fun, Fintype.card_fin]

theorem exists_fullRealization (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ)) :
    ∃ D : FieldProductDecomposition (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t,
      FullRealizationSpec (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t D := by
  obtain ⟨D⟩ := exists_fieldProductDecomposition (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t
  exact ⟨D, fullRealizationSpec (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t D⟩

end HullData

section Transport

def TransportSpec (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ))
    (D₁ D₂ : FieldProductDecomposition (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t) : Prop :=
  letI : Fintype D₁.J := D₁.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D₁.E j) := D₁.normedField
  letI : ∀ j, NormedAlgebra ℚ_[p] (D₁.E j) := D₁.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (D₁.E j) := D₁.finiteDimensional
  letI : ∀ j, CompleteSpace (D₁.E j) := D₁.completeSpace
  letI : ∀ j, IsUltrametricDist (D₁.E j) := D₁.ultrametric
  letI : ∀ j, ProperSpace (D₁.E j) := D₁.properSpace
  letI : Fintype D₂.J := D₂.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D₂.E j) := D₂.normedField
  letI : ∀ j, NormedAlgebra ℚ_[p] (D₂.E j) := D₂.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (D₂.E j) := D₂.finiteDimensional
  letI : ∀ j, CompleteSpace (D₂.E j) := D₂.completeSpace
  letI : ∀ j, IsUltrametricDist (D₂.E j) := D₂.ultrametric
  letI : ∀ j, ProperSpace (D₂.E j) := D₂.properSpace
  (D₁.equiv.symm.trans D₂.equiv) ''
      hull (tensorLogShellProductImage (A := fun i => A i (t i)) D₁.equiv) =
    hull (tensorLogShellProductImage (A := fun i => A i (t i)) D₂.equiv)

theorem transportSpec (t : Tup (j := j) (VQ := VQ) (Place := Place) (vQ := vQ))
    (D₁ D₂ : FieldProductDecomposition (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t) :
    TransportSpec (p := p) (j := j) (VQ := VQ) (Place := Place) (vQ := vQ) A t D₁ D₂ := by
  letI : Fintype D₁.J := D₁.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D₁.E j) := D₁.normedField
  letI : ∀ j, NormedAlgebra ℚ_[p] (D₁.E j) := D₁.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (D₁.E j) := D₁.finiteDimensional
  letI : ∀ j, CompleteSpace (D₁.E j) := D₁.completeSpace
  letI : ∀ j, IsUltrametricDist (D₁.E j) := D₁.ultrametric
  letI : ∀ j, ProperSpace (D₁.E j) := D₁.properSpace
  letI : Fintype D₂.J := D₂.fintypeJ
  letI : ∀ j, NontriviallyNormedField (D₂.E j) := D₂.normedField
  letI : ∀ j, NormedAlgebra ℚ_[p] (D₂.E j) := D₂.normedAlgebra
  letI : ∀ j, FiniteDimensional ℚ_[p] (D₂.E j) := D₂.finiteDimensional
  letI : ∀ j, CompleteSpace (D₂.E j) := D₂.completeSpace
  letI : ∀ j, IsUltrametricDist (D₂.E j) := D₂.ultrametric
  letI : ∀ j, ProperSpace (D₂.E j) := D₂.properSpace
  exact tensorLogShellHull_decomposition_change
    (A := fun i => A i (t i)) D₁.equiv D₂.equiv

end Transport

end LeanFormal.IUT.XiFPaper.S1445ReportBTensorRealizationActualAdapted