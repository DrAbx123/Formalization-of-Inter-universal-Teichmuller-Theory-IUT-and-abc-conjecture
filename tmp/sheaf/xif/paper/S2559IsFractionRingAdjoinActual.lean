/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2558ReverseReductionActual

/-!
# S2559: `Aoc = R[HZc-roots]` is a fraction ring of `L = F'`

The actual target is

  `IsFractionRing Aoc L`

where `Aoc = Algebra.adjoin R (HZc.rootSet L)`, `R = ℤ[1/c]` (c = 463856467968) and
`L = S1720Field = SplittingField S1720H` over `ℚ`.

Strategy (actual, no axiomatization):

* `HZR = S2481HZ.map (algebraMap ℤ R)` and `S2481HZ.map (Int.castRingHom ℚ) = S1720H`
  (the actual S2481 lemma), hence over `L` the polynomials `HZR` and `S1720H` evaluate the
  same, and `HZc = C (cu⁻¹) * HZR` differs from `HZR` by a unit scalar.  Therefore
  `HZc.rootSet L = S1720H.rootSet L`.
* `Polynomial.SplittingField.adjoin_rootSet` gives `Algebra.adjoin ℚ (S1720H.rootSet L) = ⊤`,
  hence `Algebra.adjoin ℚ (HZc.rootSet L) = ⊤`.
* Every element of `L` is therefore a quotient of two elements of `Aoc`
  (`ℚ`-coefficients are quotients of integers, hence of elements of `R ⊆ Aoc`, and the roots
  lie in `Aoc`), which is exactly the surjectivity axiom of `IsLocalization`
  `(nonZeroDivisors Aoc) L`.

No `sorry`, no new axiom, no `True`/`native_decide` gate.
-/

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial
namespace LeanFormal.IUT.XiFPaper.S2559IsFractionRingAdjoinActual
open LeanFormal.IUT.XiFPaper.S2555ConcreteIntegralClosureActual
open LeanFormal.IUT.XiFPaper.S2556HZcMonicActual
open LeanFormal.IUT.XiFPaper.S2557AdjoinIntegralActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-! ## 1. Comparison of the two polynomials over `L` -/

lemma cast_int_rat : (algebraMap ℤ ℚ) = Int.castRingHom ℚ := RingHom.ext_int _ _

/-- Over `R`, the integer model `S2481HZ` is `HZR`. -/
lemma HZR_map_eq : HZR.map (algebraMap R L) = S1720H.map (algebraMap ℚ L) := by
  have h : (algebraMap R L).comp (algebraMap ℤ R) = (algebraMap ℚ L).comp (algebraMap ℤ ℚ) := by
    rw [← IsScalarTower.algebraMap_eq ℤ R L, ← IsScalarTower.algebraMap_eq ℤ ℚ L]
  rw [HZR, Polynomial.map_map, h, ← Polynomial.map_map, cast_int_rat, S2481HZ_map_rat]

/-- `HZc` and `S1720H` differ over `L` by the nonzero scalar `cu⁻¹`. -/
lemma HZc_map_eq :
    HZc.map (algebraMap R L) =
      C (algebraMap R L ((cu⁻¹ : Rˣ) : R)) * S1720H.map (algebraMap ℚ L) := by
  rw [HZc, Polynomial.map_mul, Polynomial.map_C, HZR_map_eq]

lemma cu_inv_ne_zero : algebraMap R L ((cu⁻¹ : Rˣ) : R) ≠ 0 :=
  ((cu⁻¹).isUnit.map (algebraMap R L)).ne_zero

/-- Evaluation of `HZR` in `L` agrees with evaluation of `S1720H`. -/
lemma aeval_HZR_eq (x : L) : aeval x HZR = aeval x S1720H := by
  rw [HZR, Polynomial.aeval_map_algebraMap (A := R) (x := x),
    ← Polynomial.aeval_map_algebraMap (A := ℚ) (B := L) (x := x) (p := S2481HZ),
    cast_int_rat, S2481HZ_map_rat]

/-- Evaluation of `HZc` in `L`. -/
lemma aeval_HZc_eq (x : L) :
    aeval x HZc = algebraMap R L ((cu⁻¹ : Rˣ) : R) * aeval x S1720H := by
  have h1 : aeval x HZc = algebraMap R L ((cu⁻¹ : Rˣ) : R) * aeval x HZR := by
    rw [HZc, map_mul, aeval_C]
  rw [h1, aeval_HZR_eq]

/-- **The root sets coincide**: the roots in `L` of `HZc` are the roots of `S1720H`. -/
theorem HZc_rootSet_eq : HZc.rootSet L = S1720H.rootSet L := by
  ext x
  rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [HZc_map_eq] at h1
      intro h0
      exact h1 (by rw [h0, mul_zero])
    · rw [aeval_HZc_eq] at h2
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h cu_inv_ne_zero
      · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [HZc_map_eq]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr cu_inv_ne_zero) h1
    · rw [aeval_HZc_eq, h2, mul_zero]

/-! ## 2. The roots generate `L` over `ℚ` -/

/-- `L` is generated over `ℚ` by the roots of `HZc`: `Algebra.adjoin ℚ (HZc.rootSet L) = ⊤`. -/
theorem adjoin_rootSet_top : Algebra.adjoin ℚ (HZc.rootSet L) = ⊤ := by
  rw [HZc_rootSet_eq]
  exact Polynomial.SplittingField.adjoin_rootSet S1720H

/-! ## 3. Every element of `L` is a quotient of two elements of `Aoc` -/

@[simp]
lemma coe_algebraMap_Aoc (x : Aoc) : algebraMap Aoc L x = (x : L) := rfl

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
    (⟨algebraMap R L (algebraMap ℤ R n), Aoc.algebraMap_mem _⟩ : Aoc) ≠ 0 := by
  intro h
  have h1 : algebraMap R L (algebraMap ℤ R n) = 0 := by
    simpa using congrArg (Subtype.val) h
  rw [image_int] at h1
  exact hn (FaithfulSMul.algebraMap_injective ℚ L (by simpa using h1))

lemma rational_is_quotient (q : ℚ) :
    ∃ a b : Aoc, b ≠ 0 ∧ algebraMap ℚ L q * (b : L) = (a : L) := by
  obtain ⟨m, n, hn, hq⟩ := IsFractionRing.div_surjective (A := ℤ) q
  have hn0 : n ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hn
  have hinjZ : Function.Injective (algebraMap ℤ ℚ) := IsFractionRing.injective ℤ ℚ
  have hnq : algebraMap ℤ ℚ n ≠ 0 := fun h => hn0 (hinjZ (by simpa using h))
  refine ⟨⟨algebraMap R L (algebraMap ℤ R m), Aoc.algebraMap_mem _⟩,
    ⟨algebraMap R L (algebraMap ℤ R n), Aoc.algebraMap_mem _⟩, ?_, ?_⟩
  · exact image_int_ne_zero hnq
  · have hq' : q * algebraMap ℤ ℚ n = algebraMap ℤ ℚ m := by
      rw [← hq]
      exact div_mul_cancel₀ _ hnq
    have h2 : algebraMap ℚ L q * algebraMap ℚ L (algebraMap ℤ ℚ n)
        = algebraMap ℚ L (algebraMap ℤ ℚ m) := by
      rw [← map_mul, hq']
    rw [show ((⟨algebraMap R L (algebraMap ℤ R n), Aoc.algebraMap_mem _⟩ : Aoc) : L)
          = algebraMap ℚ L (algebraMap ℤ ℚ n) from image_int n,
      show ((⟨algebraMap R L (algebraMap ℤ R m), Aoc.algebraMap_mem _⟩ : Aoc) : L)
          = algebraMap ℚ L (algebraMap ℤ ℚ m) from image_int m]
    exact h2

/-- **The key computation**: every element of `L` is `a / b` with `a, b ∈ Aoc`, `b ≠ 0`. -/
theorem exists_quotient (z : L) :
    ∃ a b : Aoc, b ≠ 0 ∧ z * (b : L) = (a : L) := by
  have key : ∀ (x : L), x ∈ Algebra.adjoin ℚ (HZc.rootSet L) →
      ∃ y : Aoc × nonZeroDivisors Aoc, x * algebraMap Aoc L (y.2 : Aoc) = algebraMap Aoc L y.1 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem a ha => exact ⟨(⟨a, Algebra.subset_adjoin ha⟩, 1), by simp⟩
    | algebraMap q =>
        obtain ⟨a, b, hb, hq⟩ := rational_is_quotient q
        exact ⟨(a, ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩), by simpa using hq⟩
    | add a b ha hb iha ihb =>
        obtain ⟨⟨a1, b1⟩, h1⟩ := iha
        obtain ⟨⟨a2, b2⟩, h2⟩ := ihb
        refine ⟨⟨a1 * (b2 : Aoc) + a2 * (b1 : Aoc),
          ⟨(b1 : Aoc) * (b2 : Aoc), mul_mem b1.2 b2.2⟩⟩, ?_⟩
        dsimp only
        rw [map_mul, map_add, map_mul, map_mul]
        calc (a + b) * (algebraMap Aoc L (b1 : Aoc) * algebraMap Aoc L (b2 : Aoc))
            = a * algebraMap Aoc L (b1 : Aoc) * algebraMap Aoc L (b2 : Aoc)
              + b * algebraMap Aoc L (b2 : Aoc) * algebraMap Aoc L (b1 : Aoc) := by ring
          _ = algebraMap Aoc L a1 * algebraMap Aoc L (b2 : Aoc)
              + algebraMap Aoc L a2 * algebraMap Aoc L (b1 : Aoc) := by rw [h1, h2]
    | mul a b ha hb iha ihb =>
        obtain ⟨⟨a1, b1⟩, h1⟩ := iha
        obtain ⟨⟨a2, b2⟩, h2⟩ := ihb
        refine ⟨⟨a1 * a2, ⟨(b1 : Aoc) * (b2 : Aoc), mul_mem b1.2 b2.2⟩⟩, ?_⟩
        dsimp only
        rw [map_mul, map_mul]
        calc (a * b) * (algebraMap Aoc L (b1 : Aoc) * algebraMap Aoc L (b2 : Aoc))
            = (a * algebraMap Aoc L (b1 : Aoc)) * (b * algebraMap Aoc L (b2 : Aoc)) := by ring
          _ = algebraMap Aoc L a1 * algebraMap Aoc L a2 := by rw [h1, h2]
  obtain ⟨⟨a, b⟩, hab⟩ := key z (by rw [adjoin_rootSet_top]; exact trivial)
  exact ⟨a, b, mem_nonZeroDivisors_iff_ne_zero.mp b.2, hab⟩

/-! ## 4. The main theorem -/

/-- **`Aoc` is a fraction ring of `L`.** -/
theorem S2559_isFractionRing : IsFractionRing Aoc L := by
  show IsLocalization (nonZeroDivisors Aoc) L
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    rw [isUnit_iff_ne_zero, coe_algebraMap_Aoc]
    intro h
    exact mem_nonZeroDivisors_iff_ne_zero.mp y.2 (Subtype.ext h)
  · intro z
    obtain ⟨a, b, hb, hab⟩ := exists_quotient z
    exact ⟨(a, ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩), hab⟩
  · intro x y hxy
    have h : x = y := Subtype.ext (by simpa using hxy)
    exact ⟨1, by rw [h]⟩

#print axioms S2559_isFractionRing
#print axioms HZc_rootSet_eq
#print axioms adjoin_rootSet_top

end LeanFormal.IUT.XiFPaper.S2559IsFractionRingAdjoinActual
end
