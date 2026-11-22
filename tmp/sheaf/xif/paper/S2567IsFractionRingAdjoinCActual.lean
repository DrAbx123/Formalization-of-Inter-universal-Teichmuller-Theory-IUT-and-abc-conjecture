/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2566AdjoinIntegralCActual

/-!
# S2567: `Aoc2 = R[HZc2-roots]` is a fraction ring of `L = F'`

The actual target is

  `IsFractionRing Aoc2 L`

where `Aoc2 = Algebra.adjoin R (HZc2.rootSet L)`, `R = ℤ[1/Cden]` (the `Cden`-localization)
and `L = S1720Field = SplittingField S1720H` over `ℚ`.  This is the `Cden`-version of S2559:
`HZc2` is the monic model of the integral polynomial `HZR2 = S2481HZ.map (algebraMap ℤ R2)`,
and `HZc2 = C (cu2⁻¹) * HZR2` differs from `HZR2` by a unit scalar.

Strategy (actual, no axiomatization):

* `HZR2.map (algebraMap R L) = S1720H.map (algebraMap ℚ L)` by `S2481HZ_map_rat` and the
  towers `ℤ → R → L` and `ℤ → ℚ → L`.  Hence `HZc2` and `S1720H` evaluate the same up to the
  nonzero scalar `algebraMap R L (cu2⁻¹)`, so `HZc2.rootSet L = S1720H.rootSet L`.
* `Polynomial.SplittingField.adjoin_rootSet` gives `Algebra.adjoin ℚ (S1720H.rootSet L) = ⊤`,
  hence `Algebra.adjoin ℚ (HZc2.rootSet L) = ⊤`.
* Every element of `L` is therefore a quotient of two elements of `Aoc2`, which is exactly the
  surjectivity axiom of `IsLocalization` `(nonZeroDivisors Aoc2) L`.

No `sorry`, no new axiom, no `True`/`native_decide` gate.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2567IsFractionRingAdjoinCActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2566AdjoinIntegralCActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- `R2` is definitionally the `S2565` localization `R` (both are
`Localization (Submonoid.powers Cden)`); we register the corresponding `R2`-algebra
structure on `L`, as in `S2566`. -/
local instance : Algebra R2 L := inferInstanceAs (Algebra R L)
/-- The scalar tower `ℤ → R2 → L`.  The SMul structures are pinned to the
`Algebra.toSMul` instances, so that this instance is found by the tower lemmas used below
(a bare `IsScalarTower ℤ R2 L` would elaborate its `SMul ℤ _` arguments as `ZSMul.toSMul`). -/
theorem instScalarTowerIntR2L :
    @IsScalarTower ℤ R2 L Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
attribute [local instance] instScalarTowerIntR2L

/-! ## 1. Comparison of the two polynomials over `L` -/

lemma cast_int_rat : (algebraMap ℤ ℚ) = Int.castRingHom ℚ := RingHom.ext_int _ _

/-- Over `R`, the integer model `S2481HZ` is `HZR2`. -/
lemma HZR2_map_eq : HZR2.map (algebraMap R2 L) = S1720H.map (algebraMap ℚ L) := by
  have h : (algebraMap R2 L).comp (algebraMap ℤ R2) = (algebraMap ℚ L).comp (algebraMap ℤ ℚ) := by
    rw [← IsScalarTower.algebraMap_eq ℤ R2 L, ← IsScalarTower.algebraMap_eq ℤ ℚ L]
  rw [HZR2, Polynomial.map_map, h, ← Polynomial.map_map, cast_int_rat, S2481HZ_map_rat]

/-- `HZc2` and `S1720H` differ over `L` by the nonzero scalar `cu2⁻¹`. -/
lemma HZc2_map_eq :
    HZc2.map (algebraMap R2 L) =
      C (algebraMap R2 L ((cu2⁻¹ : R2ˣ) : R2)) * S1720H.map (algebraMap ℚ L) := by
  rw [HZc2, Polynomial.map_mul, Polynomial.map_C, HZR2_map_eq]

lemma cu2_inv_ne_zero : algebraMap R2 L ((cu2⁻¹ : R2ˣ) : R2) ≠ 0 :=
  ((cu2⁻¹).isUnit.map (algebraMap R2 L)).ne_zero

/-- Evaluation of `HZR2` in `L` agrees with evaluation of `S1720H`. -/
lemma aeval_HZR2_eq (x : L) : aeval x HZR2 = aeval x S1720H := by
  rw [HZR2, Polynomial.aeval_map_algebraMap (A := R2) (x := x),
    ← Polynomial.aeval_map_algebraMap (A := ℚ) (B := L) (x := x) (p := S2481HZ),
    cast_int_rat, S2481HZ_map_rat]

/-- Evaluation of `HZc2` in `L`. -/
lemma aeval_HZc2_eq (x : L) :
    aeval x HZc2 = algebraMap R2 L ((cu2⁻¹ : R2ˣ) : R2) * aeval x S1720H := by
  have h1 : aeval x HZc2 = algebraMap R2 L ((cu2⁻¹ : R2ˣ) : R2) * aeval x HZR2 := by
    rw [HZc2, map_mul, aeval_C]
  rw [h1, aeval_HZR2_eq]

/-- **The root sets coincide**: the roots in `L` of `HZc2` are the roots of `S1720H`. -/
theorem HZc2_rootSet_eq : HZc2.rootSet L = S1720H.rootSet L := by
  ext x
  rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [HZc2_map_eq] at h1
      intro h0
      exact h1 (by rw [h0, mul_zero])
    · rw [aeval_HZc2_eq] at h2
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h cu2_inv_ne_zero
      · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [HZc2_map_eq]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr cu2_inv_ne_zero) h1
    · rw [aeval_HZc2_eq, h2, mul_zero]

/-! ## 2. The roots generate `L` over `ℚ` -/

/-- `L` is generated over `ℚ` by the roots of `HZc2`: `Algebra.adjoin ℚ (HZc2.rootSet L) = ⊤`. -/
theorem adjoin2_rootSet_top : Algebra.adjoin ℚ (HZc2.rootSet L) = ⊤ := by
  rw [HZc2_rootSet_eq]
  exact Polynomial.SplittingField.adjoin_rootSet S1720H

/-! ## 3. Every element of `L` is a quotient of two elements of `Aoc2` -/

@[simp]
lemma coe_algebraMap_Aoc2 (x : Aoc2) : algebraMap Aoc2 L x = (x : L) := rfl

lemma image_int (n : ℤ) :
    algebraMap R L (algebraMap ℤ R n) = algebraMap ℚ L (algebraMap ℤ ℚ n) := by
  have hR : algebraMap ℤ L = (algebraMap R L).comp (algebraMap ℤ R) :=
    IsScalarTower.algebraMap_eq ℤ R L
  have hQ : algebraMap ℤ L = (algebraMap ℚ L).comp (algebraMap ℤ ℚ) :=
    IsScalarTower.algebraMap_eq ℤ ℚ L
  have h1 : algebraMap R L (algebraMap ℤ R n) = algebraMap ℤ L n := by
    rw [hR, RingHom.comp_apply]
  have h2 : algebraMap ℚ L (algebraMap ℤ ℚ n) = algebraMap ℤ L n := by
    rw [hQ, RingHom.comp_apply]
  rw [h1, h2]

lemma image_int_ne_zero {n : ℤ} (hn : algebraMap ℤ ℚ n ≠ 0) :
    (⟨algebraMap R L (algebraMap ℤ R n), Aoc2.algebraMap_mem _⟩ : Aoc2) ≠ 0 := by
  intro h
  have h1 : algebraMap R L (algebraMap ℤ R n) = 0 := by
    simpa using congrArg (Subtype.val) h
  rw [image_int] at h1
  exact hn (FaithfulSMul.algebraMap_injective ℚ L (by simpa using h1))

lemma rational_is_quotient (q : ℚ) :
    ∃ a b : Aoc2, b ≠ 0 ∧ algebraMap ℚ L q * (b : L) = (a : L) := by
  obtain ⟨m, n, hn, hq⟩ := IsFractionRing.div_surjective (A := ℤ) q
  have hn0 : n ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hn
  have hinjZ : Function.Injective (algebraMap ℤ ℚ) := IsFractionRing.injective ℤ ℚ
  have hnq : algebraMap ℤ ℚ n ≠ 0 := fun h => hn0 (hinjZ (by simpa using h))
  refine ⟨⟨algebraMap R L (algebraMap ℤ R m), Aoc2.algebraMap_mem _⟩,
    ⟨algebraMap R L (algebraMap ℤ R n), Aoc2.algebraMap_mem _⟩, ?_, ?_⟩
  · exact image_int_ne_zero hnq
  · have hq' : q * algebraMap ℤ ℚ n = algebraMap ℤ ℚ m := by
      rw [← hq]
      exact div_mul_cancel₀ _ hnq
    have h2 : algebraMap ℚ L q * algebraMap ℚ L (algebraMap ℤ ℚ n)
        = algebraMap ℚ L (algebraMap ℤ ℚ m) := by
      rw [← map_mul, hq']
    rw [show ((⟨algebraMap R L (algebraMap ℤ R n), Aoc2.algebraMap_mem _⟩ : Aoc2) : L)
          = algebraMap ℚ L (algebraMap ℤ ℚ n) from image_int n,
      show ((⟨algebraMap R L (algebraMap ℤ R m), Aoc2.algebraMap_mem _⟩ : Aoc2) : L)
          = algebraMap ℚ L (algebraMap ℤ ℚ m) from image_int m]
    exact h2

/-- **The key computation**: every element of `L` is `a / b` with `a, b ∈ Aoc2`, `b ≠ 0`. -/
theorem exists_quotient (z : L) :
    ∃ a b : Aoc2, b ≠ 0 ∧ z * (b : L) = (a : L) := by
  have key : ∀ (x : L), x ∈ Algebra.adjoin ℚ (HZc2.rootSet L) →
      ∃ y : Aoc2 × nonZeroDivisors Aoc2, x * algebraMap Aoc2 L (y.2 : Aoc2) = algebraMap Aoc2 L y.1 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem a ha => exact ⟨(⟨a, Algebra.subset_adjoin ha⟩, 1), by simp⟩
    | algebraMap q =>
        obtain ⟨a, b, hb, hq⟩ := rational_is_quotient q
        exact ⟨(a, ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩), by simpa using hq⟩
    | add a b ha hb iha ihb =>
        obtain ⟨⟨a1, b1⟩, h1⟩ := iha
        obtain ⟨⟨a2, b2⟩, h2⟩ := ihb
        refine ⟨⟨a1 * (b2 : Aoc2) + a2 * (b1 : Aoc2),
          ⟨(b1 : Aoc2) * (b2 : Aoc2), mul_mem b1.2 b2.2⟩⟩, ?_⟩
        dsimp only
        rw [map_mul, map_add, map_mul, map_mul]
        calc (a + b) * (algebraMap Aoc2 L (b1 : Aoc2) * algebraMap Aoc2 L (b2 : Aoc2))
            = a * algebraMap Aoc2 L (b1 : Aoc2) * algebraMap Aoc2 L (b2 : Aoc2)
              + b * algebraMap Aoc2 L (b2 : Aoc2) * algebraMap Aoc2 L (b1 : Aoc2) := by ring
          _ = algebraMap Aoc2 L a1 * algebraMap Aoc2 L (b2 : Aoc2)
              + algebraMap Aoc2 L a2 * algebraMap Aoc2 L (b1 : Aoc2) := by rw [h1, h2]
    | mul a b ha hb iha ihb =>
        obtain ⟨⟨a1, b1⟩, h1⟩ := iha
        obtain ⟨⟨a2, b2⟩, h2⟩ := ihb
        refine ⟨⟨a1 * a2, ⟨(b1 : Aoc2) * (b2 : Aoc2), mul_mem b1.2 b2.2⟩⟩, ?_⟩
        dsimp only
        rw [map_mul, map_mul]
        calc (a * b) * (algebraMap Aoc2 L (b1 : Aoc2) * algebraMap Aoc2 L (b2 : Aoc2))
            = (a * algebraMap Aoc2 L (b1 : Aoc2)) * (b * algebraMap Aoc2 L (b2 : Aoc2)) := by ring
          _ = algebraMap Aoc2 L a1 * algebraMap Aoc2 L a2 := by rw [h1, h2]
  obtain ⟨⟨a, b⟩, hab⟩ := key z (by rw [adjoin2_rootSet_top]; exact trivial)
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp b.2, hab⟩

/-! ## 4. The main theorem -/

/-- **`Aoc2` is a fraction ring of `L`.** -/
theorem S2567_isFractionRing : IsFractionRing (↥Aoc2) L := by
  show IsLocalization (nonZeroDivisors Aoc2) L
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [isUnit_iff_ne_zero, coe_algebraMap_Aoc2]
    intro h
    exact mem_nonZeroDivisors_iff_ne_zero.mp y.2 (Subtype.ext h)
  · intro z
    obtain ⟨a, b, hb, hab⟩ := exists_quotient z
    exact ⟨(a, ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩), hab⟩
  · intro x y hxy
    have h : x = y := Subtype.ext (by simpa using hxy)
    exact ⟨1, by rw [h]⟩

#print axioms S2567_isFractionRing
#print axioms HZc2_rootSet_eq
#print axioms adjoin2_rootSet_top
#print S2567_isFractionRing

end LeanFormal.IUT.XiFPaper.S2567IsFractionRingAdjoinCActual
end
