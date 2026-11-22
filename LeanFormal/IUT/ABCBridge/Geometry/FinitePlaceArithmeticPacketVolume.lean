import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQHullVolume
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorNontrivial
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldPacketNormalizedVolume

/-!
# Actual packet-normalized volume for the whole arithmetic prime packet

Every tensor factor contains all places v|p. Their fiber is proved nonempty,
so the actual tensor has positive Qp dimension. Dividing its constructed
unit-relative hull log-volume by this dimension gives the packet-normalized
value, calculated by every actual field-product decomposition. Multiplying
that hull by p changes its packet log-volume by exactly -log p.

These remain the actual integral log-shell regions; no Gaussian region or
mono-analytic/holomorphic discrepancy is supplied by this construction.

This full-prime packet uses all places of K with uniform dimension
normalization. III Remark 3.1.1(ii) instead specifies a selected section
over places of Fmod and reciprocal relative-local-degree weights. Those
data and weights are not identified with this full-prime construction.
-/

namespace LeanFormal.IUT.NumberFieldFinitePlace

open LeanFormal.IUT.LocalFieldProductHull LeanFormal.IUT.LocalFieldPadicTensor MeasureTheory
open scoped Pointwise

noncomputable section

universe u v

variable (K : Type u) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
variable (ι : Type v) [Finite ι]

abbrev fullPrimeArithmeticPlaces :=
  fun (_ : ι) (place : FinitePlaceAtPrime K p) => place

abbrev FullPrimeArithmeticTensor := ArithmeticPacketTensor (fullPrimeArithmeticPlaces K p ι)

instance fullPrimeArithmeticTensorNontrivial : Nontrivial (FullPrimeArithmeticTensor K p ι) := by
  letI := Fintype.ofFinite ι
  exact finitePadicTensorNontrivial (fun _ : ι => FullPrimeCompletionPacket K p)

def fullPrimeArithmeticTensorDimension : ℕ := Module.finrank ℚ_[p] (FullPrimeArithmeticTensor K p ι)

theorem fullPrimeArithmeticTensorDimension_pos : 0 < fullPrimeArithmeticTensorDimension K p ι :=
  Module.finrank_pos

def fullPrimeArithmeticHullPacketLogVolume : ℝ :=
  arithmeticTensorHullUnitLogVolume (fullPrimeArithmeticPlaces K p ι) /
    (fullPrimeArithmeticTensorDimension K p ι : ℝ)

theorem fullPrimeArithmeticHullPacketLogVolume_nonneg :
    0 ≤ fullPrimeArithmeticHullPacketLogVolume K p ι :=
  div_nonneg (arithmeticTensorHullUnitLogVolume_nonneg _) (Nat.cast_nonneg _)

variable {J : Type (max u v)} [Finite J] {E : J → Type (max u v)}
variable [∀ j, NormedField (E j)] [∀ j, NormedAlgebra ℚ_[p] (E j)]
variable [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)]

theorem fullPrimeArithmeticHullPacketLogVolume_eq
    (e : FullPrimeArithmeticTensor K p ι ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    letI : MeasurableSpace ((j : J) → E j) := borel _
    letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
    fullPrimeArithmeticHullPacketLogVolume K p ι =
      padicPacketLogVolume (p := p) E Measure.addHaar
        (hull (arithmeticTensorProductImage (fullPrimeArithmeticPlaces K p ι) e)) := by
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  unfold fullPrimeArithmeticHullPacketLogVolume padicPacketLogVolume
  rw [arithmeticTensorHullUnitLogVolume_eq (fullPrimeArithmeticPlaces K p ι) e]
  unfold fullPrimeArithmeticTensorDimension
  rw [e.toLinearEquiv.finrank_eq]

theorem fullPrimeArithmeticHullPacketLogVolume_mul_prime
    (e : FullPrimeArithmeticTensor K p ι ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    letI : MeasurableSpace ((j : J) → E j) := borel _
    letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
    padicPacketLogVolume (p := p) E Measure.addHaar
      ((fun x : (j : J) → E j => (p : (j : J) → E j) * x) ''
        hull (arithmeticTensorProductImage (fullPrimeArithmeticPlaces K p ι) e)) =
      -Real.log (p : ℝ) + fullPrimeArithmeticHullPacketLogVolume K p ι := by
  letI : MeasurableSpace ((j : J) → E j) := borel _
  letI : BorelSpace ((j : J) → E j) := ⟨rfl⟩
  have hindex : Nonempty J := by
    by_contra hnone
    have hzeroone : (0 : (j : J) → E j) = 1 := by
      funext j
      exact False.elim (hnone ⟨j⟩)
    have hsource : (0 : FullPrimeArithmeticTensor K p ι) = 1 := by
      apply e.injective
      simpa only [map_zero, map_one] using hzeroone
    exact zero_ne_one hsource
  letI := hindex
  have hmass := addHaar_arithmeticTensorHull_pos_lt_top (fullPrimeArithmeticPlaces K p ι) e
  have hscale := padicPacketLogVolume_mul_prime (p := p) E Measure.addHaar hmass.1 hmass.2
  rw [← fullPrimeArithmeticHullPacketLogVolume_eq K p ι e] at hscale
  exact hscale

omit [∀ j, FiniteDimensional ℚ_[p] (E j)] [∀ j, ProperSpace (E j)] in
theorem isOpen_fullPrimeArithmeticHull [∀ j, IsUltrametricDist (E j)]
    (e : FullPrimeArithmeticTensor K p ι ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsOpen (hull (arithmeticTensorProductImage (fullPrimeArithmeticPlaces K p ι) e)) := by
  obtain ⟨lam, hlam, heq⟩ := exists_arithmeticTensorHull_eq_region
    (fullPrimeArithmeticPlaces K p ι) e
  rw [heq]
  change IsOpen {x : (j : J) → E j | ∀ j, ‖x j‖ ≤ ‖lam j‖}
  simp only [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  change IsOpen ((fun x : (j : J) → E j => x j) ⁻¹' {y : E j | ‖y‖ ≤ ‖lam j‖})
  apply IsOpen.preimage (continuous_apply j)
  apply Metric.isOpen_iff.mpr
  intro x hx
  refine ⟨‖lam j‖, norm_pos_iff.mpr (hlam j), ?_⟩
  intro y hy
  have hsmall : ‖y - x‖ < ‖lam j‖ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hbound := IsUltrametricDist.norm_add_le_max (y - x) x
  rw [sub_add_cancel] at hbound
  exact hbound.trans (max_le hsmall.le hx)

omit [∀ j, FiniteDimensional ℚ_[p] (E j)] in
theorem fullPrimeArithmeticHull_compactOpen_nonempty [∀ j, IsUltrametricDist (E j)]
    (e : FullPrimeArithmeticTensor K p ι ≃ₐ[ℚ_[p]] ((j : J) → E j)) :
    IsCompact (hull (arithmeticTensorProductImage (fullPrimeArithmeticPlaces K p ι) e)) ∧
      IsOpen (hull (arithmeticTensorProductImage (fullPrimeArithmeticPlaces K p ι) e)) ∧
      (hull (arithmeticTensorProductImage (fullPrimeArithmeticPlaces K p ι) e)).Nonempty :=
  ⟨isCompact_arithmeticTensorHull (fullPrimeArithmeticPlaces K p ι) e,
    isOpen_fullPrimeArithmeticHull K p ι e,
    ⟨1, subset_hull _ (one_mem_arithmeticTensorProductImage (fullPrimeArithmeticPlaces K p ι) e)⟩⟩

end

end LeanFormal.IUT.NumberFieldFinitePlace
