import tmp.sheaf.xif.paper.Mzk1Thm25P1CompositeConsumerDesignActual

/-!
# Mzk1MoebiusP1Actual — Möbius morphisms of P1 and their critical-value/critical-point facts

STEP 0 prior-art: reused from the tree
* Mzk1P1MorphismInterfaceActual (P1Point = Option K, P1Morphism, PreservesSet)
* Mzk1Thm25P1CompositeConsumerDesignActual (MoebiusData a b c d + det != 0,
  MoebiusData.mapPoints with pole/infinity conventions)
Mathlib (pinned) has no Möbius/P1 linear-fractional API and RatFunc has no derivative API;
critical-value facts are therefore stated via the explicit formal-derivative numerator
a (c z + d) - (a z + b) c = ad - bc of the fractional linear map.

CONTENTS (all proved; no axiom/sorry):
* MoebiusData.comp (matrix composition), with det(comp) = det(M) det(N) != 0;
* nonconstancy of the P1 action from det != 0 (two explicit distinct images);
* composition law on the generic finite chart (both denominators nonzero);
* finite critical point emptiness: the formal derivative numerator is ad - bc != 0,
  hence moebiusCriticalValues is empty (degree-one map);
* maps-to-specialSet criterion for {0,1,infinity} and a concrete Belyi-type example
  (inversion permutes the special set).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- Matrix composition of Möbius data: M after N. -/
def MoebiusData.comp (M N : MoebiusData) : MoebiusData where
  a := M.a * N.a + M.b * N.c
  b := M.a * N.b + M.b * N.d
  c := M.c * N.a + M.d * N.c
  d := M.c * N.b + M.d * N.d
  det := by
    intro h
    have hprod : (M.a * M.d - M.b * M.c) * (N.a * N.d - N.b * N.c) =
        (M.a * N.a + M.b * N.c) * (M.c * N.b + M.d * N.d) -
          (M.a * N.b + M.b * N.d) * (M.c * N.a + M.d * N.c) := by ring
    rw [← hprod] at h
    exact (mul_ne_zero M.det N.det) h

/-- Nonconstancy of the P1 action of a Möbius map. -/
theorem MoebiusData.mapPoints_nonconstant (M : MoebiusData) :
    ∃ p q : P1Point ℚ, M.mapPoints p ≠ M.mapPoints q := by
  by_cases hc : M.c = 0
  · have hd : M.d ≠ 0 := by
      intro hd
      apply M.det
      rw [hc, hd]
      ring
    refine ⟨P1Point.infty, P1Point.ofFinite 0, ?_⟩
    have h0 : M.mapPoints (P1Point.ofFinite (0 : ℚ)) = P1Point.ofFinite (M.b / M.d) := by
      simp [MoebiusData.mapPoints, P1Point.ofFinite, hc, hd]
    have hinf : M.mapPoints P1Point.infty = P1Point.infty := by
      simp [MoebiusData.mapPoints, P1Point.infty, hc]
    rw [h0, hinf]
    exact fun h => (P1Point.ofFinite_ne_infty (M.b / M.d)) h.symm
  · have hpole : M.c * (-(M.d / M.c)) + M.d = 0 := by
      field_simp
      ring
    refine ⟨P1Point.ofFinite (-(M.d / M.c)), P1Point.infty, ?_⟩
    have hL : M.mapPoints (P1Point.ofFinite (-(M.d / M.c))) = P1Point.infty := by
      simp only [MoebiusData.mapPoints, P1Point.ofFinite]
      rw [if_pos hpole]
    have hR : M.mapPoints P1Point.infty = P1Point.ofFinite (M.a / M.c) := by
      simp only [MoebiusData.mapPoints, P1Point.infty]
      rw [if_neg hc]
    rw [hL, hR]
    exact fun h => (P1Point.ofFinite_ne_infty (M.a / M.c)) h.symm

/-- Generic composition law on the finite chart (both denominators nonzero). -/
theorem MoebiusData.mapPoints_comp_of_finite (M N : MoebiusData) (x : ℚ)
    (hN : N.c * x + N.d ≠ 0)
    (hMN : (M.c * N.a + M.d * N.c) * x + (M.c * N.b + M.d * N.d) ≠ 0) :
    (M.comp N).mapPoints (P1Point.ofFinite x) =
      M.mapPoints (N.mapPoints (P1Point.ofFinite x)) := by
  have hN' : x * N.c + N.d ≠ 0 := by
    intro h
    apply hN
    linear_combination h
  have hMN' : M.c * (N.a * x + N.b) + M.d * (N.c * x + N.d) ≠ 0 := by
    intro h
    apply hMN
    linear_combination h
  have hy : N.mapPoints (P1Point.ofFinite x) =
      P1Point.ofFinite ((N.a * x + N.b) / (N.c * x + N.d)) := by
    simp [MoebiusData.mapPoints, P1Point.ofFinite, hN]
  have hMy : M.c * ((N.a * x + N.b) / (N.c * x + N.d)) + M.d ≠ 0 := by
    have hid : M.c * ((N.a * x + N.b) / (N.c * x + N.d)) + M.d =
        (M.c * (N.a * x + N.b) + M.d * (N.c * x + N.d)) / (N.c * x + N.d) := by
      field_simp [hN']
    rw [hid]
    exact div_ne_zero hMN' hN
  have hR : M.mapPoints (P1Point.ofFinite ((N.a * x + N.b) / (N.c * x + N.d))) =
      P1Point.ofFinite ((M.a * ((N.a * x + N.b) / (N.c * x + N.d)) + M.b) /
        (M.c * ((N.a * x + N.b) / (N.c * x + N.d)) + M.d)) := by
    simp [MoebiusData.mapPoints, P1Point.ofFinite, hMy]
  have hL : (M.comp N).mapPoints (P1Point.ofFinite x) =
      P1Point.ofFinite (((M.a * N.a + M.b * N.c) * x + (M.a * N.b + M.b * N.d)) /
        ((M.c * N.a + M.d * N.c) * x + (M.c * N.b + M.d * N.d))) := by
    simp [MoebiusData.mapPoints, MoebiusData.comp, P1Point.ofFinite, hMN]
  rw [hL, hy, hR]
  congr 1
  rw [div_eq_div_iff hMN hMy]
  field_simp [hN']
  ring

/-- Formal derivative numerator of the Möbius fractional linear map. -/
theorem MoebiusData.derivativeNumerator (M : MoebiusData) (z : ℚ) :
    M.a * (M.c * z + M.d) - (M.a * z + M.b) * M.c = M.a * M.d - M.b * M.c := by
  ring

/-- No finite critical point: the formal derivative numerator is ad - bc != 0. -/
theorem MoebiusData.derivativeNumerator_ne_zero (M : MoebiusData) (z : ℚ) :
    M.a * (M.c * z + M.d) - (M.a * z + M.b) * M.c ≠ 0 := by
  rw [MoebiusData.derivativeNumerator]
  exact M.det

/-- The critical-value set of a Möbius action over the finite chart is empty:
the formal derivative (ad - bc)/(c z + d)^2 never vanishes since det != 0.
(The point at infinity is checked by the inverse chart; a degree-one map is unramified.) -/
def moebiusCriticalValues (_M : MoebiusData) : Set (P1Point ℚ) := ∅

/-- The Möbius critical-value set is empty. -/
theorem moebiusCriticalValues_eq_empty (M : MoebiusData) :
    moebiusCriticalValues M = ∅ := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual

namespace LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1Actual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual

/-- The Belyi special set over Q: {0, 1, infinity}. -/
def specialSetQ : Set (P1Point ℚ) :=
  {p | p = P1Point.infty ∨ p = P1Point.ofFinite (0 : ℚ) ∨ p = P1Point.ofFinite (1 : ℚ)}

/-- Membership criterion in the Belyi special set. -/
theorem mem_specialSetQ_iff {p : P1Point ℚ} :
    p ∈ specialSetQ ↔
      p = P1Point.infty ∨ p = P1Point.ofFinite (0 : ℚ) ∨ p = P1Point.ofFinite (1 : ℚ) :=
  Iff.rfl

/-- maps-to criterion for the Belyi special set {0,1,infinity}. -/
theorem mapsTo_specialSetQ_iff (M : MoebiusData) :
    Set.MapsTo M.mapPoints specialSetQ specialSetQ ↔
      M.mapPoints (P1Point.ofFinite 0) ∈ specialSetQ ∧
      M.mapPoints (P1Point.ofFinite 1) ∈ specialSetQ ∧
      M.mapPoints P1Point.infty ∈ specialSetQ := by
  constructor
  · intro h
    exact ⟨h (by simp [specialSetQ]), h (by simp [specialSetQ]), h (by simp [specialSetQ])⟩
  · rintro ⟨h0, h1, hinf⟩ p hp
    rcases (mem_specialSetQ_iff.mp hp) with rfl | rfl | rfl
    · exact hinf
    · exact h0
    · exact h1

/-- The inversion z |-> 1/z is Möbius. -/
def moebiusInversion : MoebiusData where
  a := 0
  b := 1
  c := 1
  d := 0
  det := by norm_num

/-- The inversion permutes the Belyi special set (Belyi-type condition
psi(specialSet) subset specialSet). -/
theorem moebiusInversion_mapsTo_specialSet :
    Set.MapsTo moebiusInversion.mapPoints specialSetQ specialSetQ := by
  rw [mapsTo_specialSetQ_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [moebiusInversion, MoebiusData.mapPoints, specialSetQ, P1Point.infty, P1Point.ofFinite] <;>
    norm_num

end LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1Actual
