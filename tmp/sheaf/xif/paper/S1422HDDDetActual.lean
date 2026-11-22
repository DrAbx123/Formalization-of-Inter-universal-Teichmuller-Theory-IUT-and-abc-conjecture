import tmp.sheaf.xif.paper.S1402HDDDependentSourceActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-!
# S1422: the dependent HDD source's detData from the actual hull determinant

S1402 constructed the dependent local-field family
E v = localField v and the actual LocalFieldProductHull.hull of the
output-dependent image, but its detData field remained the free
DetTensorPowerLogVolumeBookkeeping interface.

This file constructs that detData from actual data:

* the region type is the actual dependent product of completions, not a
  Fin 1 / rank-one surrogate;
* the first field logVolume is the actual Haar mass of the actual
  holomorphic hull LocalFieldProductHull.hull, i.e. the actual hull
  determinant volume;
* the det (x) M operation is the actual multiplicative dilation by the
  diagonal unit whose coordinates are the inverses of the residue
  characteristics of the dependent places;
* the tensor-power exponent is the natural number equal to the product of
  those residue characteristics.

The single exact input left is the distributive Haar character identity
DependentProductScalingChar: the diagonal prime-inverse unit has Haar
character dependentExponent.  It is recorded as a Prop, with no
inhabitant.  Given it, the full DetTensorPowerLogVolumeBookkeeping is
constructed.  No rank-one, Fin 1, arbitrary Set, or free region map is
introduced.

The frozen finite-packet determinant/tensor/rescaling laws of
HullDeterminantLogVolumeFrozenSpec are used for the positive packet of
hull radii; see Section 6.

Boundary of the construction.  The chosen measure is the canonical
Measure.addHaar on the dependent product; the paper's residue-degree / N_v
weights and its precise procession normalization are not constructed here.
The positivity theorem takes properness of the canonical completions as an
explicit analytic hypothesis, because the current donors supply local
compactness through the normalized-completion homeomorphism but not a
ProperSpace instance for the canonical completion norm.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open MeasureTheory
open scoped Pointwise BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.S1422HDDDetActual

universe u v

/-! ## 1. The actual local-field completion instances

The canonical completion of a rational finite place is locally compact and
second countable.  We obtain both by transporting the corresponding instances
of the normalized completion along the proved homeomorphism
normalizedCompletionHomeomorph.
-/

local instance completionMeasurableSpace (P : NumberField.FinitePlace ℚ) :
    MeasurableSpace (Completion P) := borel (Completion P)

local instance completionBorelSpace (P : NumberField.FinitePlace ℚ) :
    BorelSpace (Completion P) := ⟨rfl⟩

local instance completionLocallyCompact (P : NumberField.FinitePlace ℚ) :
    LocallyCompactSpace (Completion P) :=
  (normalizedCompletionHomeomorph P).locallyCompactSpace_iff.mp inferInstance

local instance completionSecondCountable (P : NumberField.FinitePlace ℚ) :
    SecondCountableTopology (Completion P) :=
  (normalizedCompletionHomeomorph P).symm.secondCountableTopology

/-! ## 2. Hull scaling by coordinatewise units

The paper's regions are the multiplicative dilates of the unit region.  A
coordinatewise nonzero scaling sends region lam to region (u * lam), hence it
commutes with the intersection defining the hull.  This is the actual scaling
law used by the det (x) M bookkeeping below.
-/

theorem smul_region {ι : Type*} {K : ι → Type*} [∀ i, NormedField (K i)]
    (u : (i : ι) → (K i)ˣ) (lam : (i : ι) → K i) :
    (fun x : (i : ι) → K i => fun i => (u i : K i) * x i) ''
        region lam =
      region (fun i => (u i : K i) * lam i) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    change ‖(u i : K i) * x i‖ ≤ ‖(u i : K i) * lam i‖
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _)
  · intro hy
    refine ⟨fun i => (u i : K i)⁻¹ * y i, ?_, ?_⟩
    · intro i
      have hu : (u i : K i) ≠ 0 := Units.ne_zero (u i)
      have hpos : 0 < ‖(u i : K i)‖ := norm_pos_iff.mpr hu
      have h := hy i
      change ‖y i‖ ≤ ‖(u i : K i) * lam i‖ at h
      rw [norm_mul] at h
      calc
        ‖(u i : K i)⁻¹ * y i‖ = ‖(u i : K i)⁻¹‖ * ‖y i‖ := norm_mul _ _
        _ = ‖(u i : K i)‖⁻¹ * ‖y i‖ := by rw [norm_inv]
        _ ≤ ‖(u i : K i)‖⁻¹ * (‖(u i : K i)‖ * ‖lam i‖) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (norm_nonneg _))
        _ = ‖lam i‖ := by field_simp [hpos.ne']
    · ext i
      have hu : (u i : K i) ≠ 0 := Units.ne_zero (u i)
      change (u i : K i) * ((u i : K i)⁻¹ * y i) = y i
      rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]

theorem hull_smul {ι : Type*} {K : ι → Type*} [∀ i, NormedField (K i)]
    (u : (i : ι) → (K i)ˣ) (S : Set ((i : ι) → K i)) :
    hull ((fun x : (i : ι) → K i => fun i => (u i : K i) * x i) '' S) =
      (fun x : (i : ι) → K i => fun i => (u i : K i) * x i) '' hull S := by
  ext x
  constructor
  · intro hx
    refine ⟨fun i => (u i : K i)⁻¹ * x i, ?_, ?_⟩
    · intro lam hlam hsub
      have hx' : x ∈ region (fun i => (u i : K i) * lam i) :=
        hx (fun i => (u i : K i) * lam i)
          (fun i => mul_ne_zero (Units.ne_zero (u i)) (hlam i))
          (by
            intro z hz
            rcases hz with ⟨s, hs, rfl⟩
            intro i
            change ‖(u i : K i) * s i‖ ≤ ‖(u i : K i) * lam i‖
            rw [norm_mul, norm_mul]
            exact mul_le_mul_of_nonneg_left (hsub hs i) (norm_nonneg _))
      intro i
      have hu : (u i : K i) ≠ 0 := Units.ne_zero (u i)
      have hpos : 0 < ‖(u i : K i)‖ := norm_pos_iff.mpr hu
      have h := hx' i
      change ‖x i‖ ≤ ‖(u i : K i) * lam i‖ at h
      rw [norm_mul] at h
      calc
        ‖(u i : K i)⁻¹ * x i‖ = ‖(u i : K i)⁻¹‖ * ‖x i‖ := norm_mul _ _
        _ = ‖(u i : K i)‖⁻¹ * ‖x i‖ := by rw [norm_inv]
        _ ≤ ‖(u i : K i)‖⁻¹ * (‖(u i : K i)‖ * ‖lam i‖) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (norm_nonneg _))
        _ = ‖lam i‖ := by field_simp [hpos.ne']
    · ext i
      have hu : (u i : K i) ≠ 0 := Units.ne_zero (u i)
      change (u i : K i) * ((u i : K i)⁻¹ * x i) = x i
      rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  · rintro ⟨y, hy, rfl⟩
    intro lam hlam hsub
    have hsub' : S ⊆ region (fun i => (u i : K i)⁻¹ * lam i) := by
      intro s hs i
      have hu : (u i : K i) ≠ 0 := Units.ne_zero (u i)
      have h := hsub ⟨s, hs, rfl⟩ i
      change ‖(u i : K i) * s i‖ ≤ ‖lam i‖ at h
      rw [norm_mul] at h
      calc
        ‖s i‖ = ‖(u i : K i)⁻¹ * ((u i : K i) * s i)‖ := by
          congr 1
          rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
        _ = ‖(u i : K i)⁻¹‖ * ‖(u i : K i) * s i‖ := norm_mul _ _
        _ = ‖(u i : K i)⁻¹‖ * (‖(u i : K i)‖ * ‖s i‖) := by rw [norm_mul]
        _ ≤ ‖(u i : K i)⁻¹‖ * ‖lam i‖ :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
        _ = ‖(u i : K i)⁻¹ * lam i‖ := by rw [norm_mul]
    have hy' := hy (fun i => (u i : K i)⁻¹ * lam i)
      (fun i => mul_ne_zero (inv_ne_zero (Units.ne_zero (u i))) (hlam i)) hsub'
    intro i
    have hu : (u i : K i) ≠ 0 := Units.ne_zero (u i)
    have hpos : 0 < ‖(u i : K i)‖ := norm_pos_iff.mpr hu
    calc
      ‖(fun x i => (u i : K i) * x i) y i‖ = ‖(u i : K i) * y i‖ := rfl
      _ = ‖(u i : K i)‖ * ‖y i‖ := norm_mul _ _
      _ ≤ ‖(u i : K i)‖ * ‖(u i : K i)⁻¹ * lam i‖ :=
        mul_le_mul_of_nonneg_left (hy' i) (norm_nonneg _)
      _ = ‖(u i : K i)‖ * (‖(u i : K i)‖⁻¹ * ‖lam i‖) := by rw [norm_mul, norm_inv]
      _ = ‖lam i‖ := by field_simp [hpos.ne']

/-! ## 3. The unit action of the product field -/

variable {ι : Type*} {K : ι → Type*}

local instance unitsMulAction [∀ i, Monoid (K i)] :
    MulAction ((i : ι) → K i)ˣ ((i : ι) → K i) where
  smul u x := (u : (i : ι) → K i) * x
  one_smul x := one_mul x
  mul_smul u v x := mul_assoc (u : (i : ι) → K i) (v : (i : ι) → K i) x

local instance unitsDistribMulAction [∀ i, Semiring (K i)] :
    DistribMulAction ((i : ι) → K i)ˣ ((i : ι) → K i) where
  smul_zero u := mul_zero _
  smul_add u x y := mul_add _ _ _

local instance unitsContinuousConstSMul [∀ i, NormedField (K i)] :
    ContinuousConstSMul ((i : ι) → K i)ˣ ((i : ι) → K i) where
  continuous_const_smul u := by
    change Continuous (fun x : (i : ι) → K i => (u : (i : ι) → K i) * x)
    exact continuous_const.mul continuous_id

/-- The coordinate units of a unit of the product field. -/
noncomputable def coordUnits [∀ i, Monoid (K i)]
    (G : ((i : ι) → K i)ˣ) : (i : ι) → (K i)ˣ :=
  MulEquiv.piUnits G

theorem coe_coordUnits [∀ i, Monoid (K i)] (G : ((i : ι) → K i)ˣ) :
    (G : (i : ι) → K i) = fun i => (coordUnits G i : K i) := by
  ext i
  rfl

theorem smul_eq_image [∀ i, Monoid (K i)] (G : ((i : ι) → K i)ˣ)
    (S : Set ((i : ι) → K i)) :
    G • S = (fun x : (i : ι) → K i => fun i => (coordUnits G i : K i) * x i) '' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by ext i; rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by ext i; rfl⟩

theorem hull_smul_unit [∀ i, NormedField (K i)] (G : ((i : ι) → K i)ˣ)
    (S : Set ((i : ι) → K i)) :
    hull (G • S) = G • hull S := by
  rw [smul_eq_image G S, smul_eq_image G (hull S)]
  exact hull_smul (coordUnits G) S

/-! ## 4. The detData built from the actual hull Haar volume -/

section DetData

variable [Fintype ι] [∀ i, NormedField (K i)]
variable [MeasurableSpace ((i : ι) → K i)] [BorelSpace ((i : ι) → K i)]
variable [LocallyCompactSpace ((i : ι) → K i)]
variable [IsTopologicalAddGroup ((i : ι) → K i)]

/-- The actual hull log-volume of a region: the Haar mass of its holomorphic
hull.  This is the exact first field of the det (x) M bookkeeping, built from
the actual LocalFieldProductHull.hull. -/
noncomputable def hullLogVolume
    (μ : Measure ((i : ι) → K i)) : Set ((i : ι) → K i) → ENNReal :=
  fun S => μ (hull S)

theorem hullLogVolume_apply (μ : Measure ((i : ι) → K i))
    (S : Set ((i : ι) → K i)) :
    hullLogVolume (K := K) μ S = μ (hull S) := rfl

/-- A full DetTensorPowerLogVolumeBookkeeping for the region type, built from
the actual hull Haar volume and an actual product-field unit whose distributive
Haar character is the natural number M.  The det (x) M operation is the
actual multiplicative dilation by that unit, not an arbitrary region map. -/
noncomputable def detDataOfHull
    (μ : Measure ((i : ι) → K i)) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ]
    (G : ((i : ι) → K i)ˣ) (M : Nat) (hM : 0 < M)
    (hchar : (distribHaarChar ((i : ι) → K i) G : ENNReal) = (M : ENNReal)) :
    DetTensorPowerLogVolumeBookkeeping (Set ((i : ι) → K i)) where
  logVolume := hullLogVolume (K := K) μ
  tensorPowerExponent := M
  tensorPowerExponent_pos := hM
  detTensorPower S := G • S
  logVolume_detTensorPower := by
    intro S
    change μ (hull (G • S)) = (M : ENNReal) * μ (hull S)
    rw [hull_smul_unit]
    rw [← distribHaarChar_mul μ G (hull S)]
    rw [hchar]

@[simp] theorem detDataOfHull_logVolume
    (μ : Measure ((i : ι) → K i)) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ]
    (G : ((i : ι) → K i)ˣ) (M : Nat) (hM : 0 < M)
    (hchar : (distribHaarChar ((i : ι) → K i) G : ENNReal) = (M : ENNReal))
    (S : Set ((i : ι) → K i)) :
    (detDataOfHull (K := K) μ G M hM hchar).logVolume S = μ (hull S) := rfl

@[simp] theorem detDataOfHull_detTensorPower
    (μ : Measure ((i : ι) → K i)) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    [MeasureTheory.Measure.Regular μ]
    (G : ((i : ι) → K i)ˣ) (M : Nat) (hM : 0 < M)
    (hchar : (distribHaarChar ((i : ι) → K i) G : ENNReal) = (M : ENNReal))
    (S : Set ((i : ι) → K i)) :
    (detDataOfHull (K := K) μ G M hM hchar).detTensorPower S = G • S := rfl

end DetData

/-! ## 5. The dependent HDD source -/

section Dependent

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]

/-- The actual dependent local-field product. -/
abbrev dependentPoint (s : Finset (NumberField.FinitePlace ℚ)) : Type :=
  (v : {v // v ∈ s}) → S1402DependentE s v

/-- The actual region type of the dependent source. -/
abbrev dependentRegion (s : Finset (NumberField.FinitePlace ℚ)) : Type :=
  Set (dependentPoint s)

/-- The actual additive Haar measure on the dependent local-field product. -/
noncomputable abbrev dependentHaar (s : Finset (NumberField.FinitePlace ℚ)) :
    Measure (dependentPoint s) :=
  Measure.addHaar

/-- The exact first field: the actual Haar mass of the actual holomorphic hull. -/
noncomputable def dependentHullLogVolume (s : Finset (NumberField.FinitePlace ℚ)) :
    dependentRegion s → ENNReal :=
  fun S => dependentHaar s (hull S)

variable {I : Input Label Choice}

theorem dependentHullLogVolume_dependentHull
    {s : Finset (NumberField.FinitePlace ℚ)}
    (D : S1402DependentHDDSource I s) (o : Theorem311Output I) :
    dependentHullLogVolume s (D.dependentHull o) =
      dependentHaar s (D.dependentHull o) := by
  simp only [dependentHullLogVolume, S1402DependentHDDSource.dependentHull]
  rw [LocalFieldProductHull.hull_idempotent]

/-- The prime underlying a dependent place. -/
noncomputable def dependentPlacePrime (s : Finset (NumberField.FinitePlace ℚ))
    (v : {v // v ∈ s}) : Nat :=
  (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime v.1).val

theorem dependentPlacePrime_prime (s : Finset (NumberField.FinitePlace ℚ))
    (v : {v // v ∈ s}) : Nat.Prime (dependentPlacePrime s v) := by
  unfold dependentPlacePrime
  exact (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime v.1).property

/-- The actual inverse of the residue characteristic, as a unit of the local
field at each dependent place. -/
noncomputable def dependentPrimeInverseUnit
    (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s}) :
    (S1402DependentE s v)ˣ :=
  Units.mk0 ((dependentPlacePrime s v : S1402DependentE s v)⁻¹)
    (inv_ne_zero (Nat.cast_ne_zero.mpr (dependentPlacePrime_prime s v).ne_zero))

/-- The actual diagonal scaling unit of the dependent product. -/
noncomputable def dependentPrimeUnit (s : Finset (NumberField.FinitePlace ℚ)) :
    (dependentPoint s)ˣ :=
  MulEquiv.piUnits.symm (fun v => dependentPrimeInverseUnit s v)

/-- The natural tensor-power exponent: the product of the residue
characteristics of the dependent places. -/
noncomputable def dependentExponent (s : Finset (NumberField.FinitePlace ℚ)) : Nat :=
  ∏ v, dependentPlacePrime s v

theorem dependentExponent_pos (s : Finset (NumberField.FinitePlace ℚ)) :
    0 < dependentExponent s := by
  unfold dependentExponent
  exact Finset.prod_pos (fun v _ => (dependentPlacePrime_prime s v).pos)

/-- Exact first field left by the dependent construction: the distributive Haar
character of the actual diagonal prime-inverse scaling is the natural number
dependentExponent s.  No inhabitant is asserted. -/
abbrev DependentProductScalingChar (s : Finset (NumberField.FinitePlace ℚ)) : Prop :=
  (distribHaarChar (dependentPoint s) (dependentPrimeUnit s) : ENNReal) =
    (dependentExponent s : ENNReal)

/-- The dependent source's detData, constructed from the actual hull Haar
volume and the actual diagonal prime-inverse unit, conditional on the exact
scaling-character field.  No rank-one surrogate, no arbitrary region map. -/
noncomputable def dependentDetDataOfChar
    (s : Finset (NumberField.FinitePlace ℚ))
    (hchar : DependentProductScalingChar s) :
    DetTensorPowerLogVolumeBookkeeping (dependentRegion s) :=
  detDataOfHull (K := fun v => S1402DependentE s v) (dependentHaar s)
    (dependentPrimeUnit s) (dependentExponent s) (dependentExponent_pos s) hchar

@[simp] theorem dependentDetDataOfChar_logVolume
    (s : Finset (NumberField.FinitePlace ℚ))
    (hchar : DependentProductScalingChar s) (S : dependentRegion s) :
    (dependentDetDataOfChar s hchar).logVolume S = dependentHaar s (hull S) :=
  hullLogVolume_apply (dependentHaar s) S

/-- The hull measure is positive and finite on the actual dependent source hull
when the local completions are proper, which is the exact analytic input used
by the existing LocalFieldProductHull finite-measure theorem. -/
theorem dependentHullLogVolume_dependentHull_pos_lt_top
    {s : Finset (NumberField.FinitePlace ℚ)}
    [∀ v, ProperSpace (S1402DependentE s v)]
    (D : S1402DependentHDDSource I s) (o : Theorem311Output I) :
    0 < dependentHullLogVolume s (D.dependentHull o) ∧
      dependentHullLogVolume s (D.dependentHull o) < ⊤ := by
  rw [dependentHullLogVolume_dependentHull]
  exact measure_hull_pos_lt_top (dependentHaar s)
    (D.compact_closure o) (D.nonempty o) (D.coordinate_nonzero o)

end Dependent

/-! ## 6. The frozen positive packet of hull radii -/

section FrozenPacket

open LeanFormal.IUT

/-- The frozen specification, instantiated at the universe levels of the
finite positive packets used here. -/
abbrev frozenSpecZero : Prop :=
  HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0}

theorem frozenSpecZero_holds : frozenSpecZero :=
  hullDeterminantLogVolumeFrozenSpec_holds

/-- The positive packet whose label set is the dependent set of places and
whose scales are the coordinate radii of a hull region.  This is the actual
finite positive packet of the hull determinant, with rank equal to the number
of dependent places. -/
noncomputable def hullPacket {s : Finset (NumberField.FinitePlace ℚ)}
    (lam : (v : {v // v ∈ s}) → S1402DependentE s v)
    (hpos : ∀ v, 0 < ‖lam v‖) : PositivePacket {v // v ∈ s} where
  scale v := ‖lam v‖
  positive v := hpos v

/-- The frozen determinant law reads off the actual hull determinant
prod_v ‖lam v‖. -/
theorem hullPacket_det_eq_prod {s : Finset (NumberField.FinitePlace ℚ)}
    (lam : (v : {v // v ∈ s}) → S1402DependentE s v)
    (hpos : ∀ v, 0 < ‖lam v‖) :
    packetDet (hullPacket lam hpos) = ∏ v, ‖lam v‖ :=
  frozenSpecZero_holds.det_eq_prod (hullPacket lam hpos)

/-- The frozen log-volume law identifies the log of the actual hull
determinant. -/
theorem hullPacket_logVolume_eq_log_det {s : Finset (NumberField.FinitePlace ℚ)}
    (lam : (v : {v // v ∈ s}) → S1402DependentE s v)
    (hpos : ∀ v, 0 < ‖lam v‖) :
    packetLogVolume (hullPacket lam hpos) =
      Real.log (packetDet (hullPacket lam hpos)) :=
  frozenSpecZero_holds.log_eq_log_det (hullPacket lam hpos)

end FrozenPacket

end LeanFormal.IUT.XiFPaper.S1422HDDDetActual

/-! ## 7. Audit record -/

namespace LeanFormal.IUT.Audit

/-- Audit record for S1422: dependent-source detData from the actual hull
determinant. -/
def s1422HDDDetActual : Obligation :=
  { id := "IUT-III.xif.s1422-hdd-det-actual"
    source :=
      "S1402 dependent local-field hull; IUT III Corollary 3.12 Step (xi-d), " ++
        "Remark 3.9.5, (Ob3-2)/(Ob3-3)"
    status := VerificationStatus.interface
    note :=
      "Constructed: (i) the actual coordinatewise hull-scaling law " ++
        "hull_smul / hull_smul_unit; (ii) a full " ++
        "DetTensorPowerLogVolumeBookkeeping from the actual hull Haar mass " ++
        "and an actual product-field unit with natural distributive Haar " ++
        "character (detDataOfHull); (iii) the dependent source first field " ++
        "dependentHullLogVolume = Haar mass of the actual " ++
        "LocalFieldProductHull.hull; (iv) the actual diagonal prime-inverse " ++
        "unit and exponent prod_v p_v; (v) dependentDetDataOfChar, the " ++
        "dependent detData, conditional on the exact character field " ++
        "DependentProductScalingChar; (vi) the frozen positive-packet " ++
        "determinant/log-volume laws for the hull radii. Not proved: the " ++
        "character identity DependentProductScalingChar (the single exact " ++
        "first field); properness of the canonical completions is an " ++
        "explicit hypothesis of the positivity theorem. No rank-one/Fin 1/" ++
        "arbitrary Set surrogate."
    dependsOn := [ "IUT-III.holomorphic-hull-determinant-log-volume" ] }

end LeanFormal.IUT.Audit

/-! ## 8. Axiom audit -/

#print axioms LeanFormal.IUT.XiFPaper.S1422HDDDetActual.smul_region
#print axioms LeanFormal.IUT.XiFPaper.S1422HDDDetActual.hull_smul
#print axioms LeanFormal.IUT.XiFPaper.S1422HDDDetActual.hull_smul_unit
#print axioms LeanFormal.IUT.XiFPaper.S1422HDDDetActual.detDataOfHull
#print axioms LeanFormal.IUT.XiFPaper.S1422HDDDetActual.dependentHullLogVolume_dependentHull
#print axioms LeanFormal.IUT.XiFPaper.S1422HDDDetActual.dependentDetDataOfChar
#print axioms LeanFormal.IUT.XiFPaper.S1422HDDDetActual.dependentHullLogVolume_dependentHull_pos_lt_top
#print axioms LeanFormal.IUT.XiFPaper.S1422HDDDetActual.hullPacket_det_eq_prod

end