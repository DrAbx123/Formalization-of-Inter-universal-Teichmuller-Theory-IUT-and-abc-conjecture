import tmp.sheaf.xif.paper.Mzk1MoebiusP1Actual

/-!
# Mzk1MoebiusP1CActual — C-typed critical-value variant and infinity/pole conventions

Extends Mzk1MoebiusP1Actual for the consumers flagged by mainline:
(a) C-typed CV: a ℂ-Möbius action with CV as Set (P1Point ℂ) (empty critical-value theorem),
    plus transport from the ℚ-typed CV;
(b) infinity/pole conventions: explicit rfl/if lemmas for mapPoints at ∞, at poles, and off
    poles, and the composition law AT INFINITY for ℚ-Möbius data;
(c) C-version of the empty critical-value statement.
No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1CActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual
open LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1Actual

/-- Transport of P1 points from ℚ to ℂ. -/
def P1Point.mapRatComplex : P1Point ℚ → P1Point ℂ
  | none => P1Point.infty
  | some x => P1Point.ofFinite ((x : ℂ))

/-- A Möbius transformation over ℂ (matrix (a b; c d), det != 0). -/
structure MoebiusDataC where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det : a * d - b * c ≠ 0

/-- The Möbius action on P1(ℂ) with pole/infinity conventions. -/
noncomputable def MoebiusDataC.mapPoints (M : MoebiusDataC) : P1Point ℂ → P1Point ℂ
  | none => if M.c = 0 then P1Point.infty else P1Point.ofFinite (M.a / M.c)
  | some x => if M.c * x + M.d = 0 then P1Point.infty
      else P1Point.ofFinite ((M.a * x + M.b) / (M.c * x + M.d))

/-- Base change of ℚ-Möbius data to ℂ. -/
def mapToC (M : MoebiusData) : MoebiusDataC where
  a := (M.a : ℂ)
  b := (M.b : ℂ)
  c := (M.c : ℂ)
  d := (M.d : ℂ)
  det := by
    have h : ((M.a * M.d - M.b * M.c : ℚ) : ℂ) ≠ 0 := by exact_mod_cast M.det
    simpa [Rat.cast_sub, Rat.cast_mul] using h

section Conventions

/-- Infinity convention: c != 0 maps infinity to a/c, c = 0 fixes infinity. -/
theorem MoebiusData.mapPoints_infty (M : MoebiusData) :
    M.mapPoints P1Point.infty =
      if M.c = 0 then P1Point.infty else P1Point.ofFinite (M.a / M.c) := rfl

/-- Pole convention: at a pole the map takes the value infinity. -/
theorem MoebiusData.mapPoints_pole (M : MoebiusData) {x : ℚ}
    (h : M.c * x + M.d = 0) :
    M.mapPoints (P1Point.ofFinite x) = P1Point.infty := by
  simp [MoebiusData.mapPoints, P1Point.ofFinite, h]

/-- Off the pole the map is the finite fractional-linear value. -/
theorem MoebiusData.mapPoints_finite (M : MoebiusData) {x : ℚ}
    (h : M.c * x + M.d ≠ 0) :
    M.mapPoints (P1Point.ofFinite x) =
      P1Point.ofFinite ((M.a * x + M.b) / (M.c * x + M.d)) := by
  simp [MoebiusData.mapPoints, P1Point.ofFinite, h]

/-- Composition law at infinity. -/
theorem MoebiusData.mapPoints_comp_infty (M N : MoebiusData) :
    (M.comp N).mapPoints P1Point.infty =
      M.mapPoints (N.mapPoints P1Point.infty) := by
  have hc : (M.comp N).c = M.c * N.a + M.d * N.c := rfl
  have ha : (M.comp N).a = M.a * N.a + M.b * N.c := rfl
  rw [MoebiusData.mapPoints_infty (M.comp N), MoebiusData.mapPoints_infty N, hc, ha]
  by_cases hN : N.c = 0
  · rw [if_pos hN, MoebiusData.mapPoints_infty M]
    by_cases hMc : M.c = 0
    · have hL : M.c * N.a + M.d * N.c = 0 := by rw [hMc, hN]; ring
      rw [if_pos hL, if_pos hMc]
    · have hNd : N.d ≠ 0 := by
        intro h
        exact N.det (by rw [hN, h]; ring)
      have hNa : N.a ≠ 0 := by
        intro h
        exact N.det (by rw [h, hN]; ring)
      have hL : M.c * N.a + M.d * N.c ≠ 0 := by
        rw [hN]
        simpa using (mul_ne_zero hMc hNa)
      rw [if_neg hL, if_neg hMc]
      congr 1
      rw [hN]
      field_simp [hMc, hNa] <;> ring
  · rw [if_neg hN]
    by_cases hMc : M.c = 0
    · have hMd : M.d ≠ 0 := by
        intro h
        exact M.det (by rw [hMc, h]; ring)
      have hL : M.c * N.a + M.d * N.c ≠ 0 := by
        rw [hMc]
        simpa using (mul_ne_zero hMd hN)
      rw [if_neg hL, MoebiusData.mapPoints_finite M (by rw [hMc]; simpa using hMd)]
      congr 1
      field_simp [hN, hMd] <;> ring
    · by_cases hcc : M.c * N.a + M.d * N.c = 0
      · rw [if_pos hcc]
        have hpole : M.c * (N.a / N.c) + M.d = 0 := by
          have hid : M.c * (N.a / N.c) + M.d = (M.c * N.a + M.d * N.c) / N.c := by
            field_simp [hN]
          rw [hid, hcc]
          simp
        rw [MoebiusData.mapPoints_pole M hpole]
      · rw [if_neg hcc]
        have hfin : M.c * (N.a / N.c) + M.d ≠ 0 := by
          have hid : M.c * (N.a / N.c) + M.d = (M.c * N.a + M.d * N.c) / N.c := by
            field_simp [hN]
          rw [hid]
          exact div_ne_zero hcc hN
        rw [MoebiusData.mapPoints_finite M hfin]
        congr 1
        field_simp [hN, hMc] <;> ring

end Conventions

section CVal

/-- C-version: the formal derivative numerator is ad - bc != 0. -/
theorem MoebiusDataC.derivativeNumerator_ne_zero (M : MoebiusDataC) (z : ℂ) :
    M.a * (M.c * z + M.d) - (M.a * z + M.b) * M.c ≠ 0 := by
  have h : M.a * (M.c * z + M.d) - (M.a * z + M.b) * M.c = M.a * M.d - M.b * M.c := by
    ring
  rw [h]
  exact M.det

/-- C-typed Möbius critical-value set: empty (degree-one map, no critical points). -/
def MoebiusDataC.moebiusCriticalValuesC (_M : MoebiusDataC) : Set (P1Point ℂ) := ∅

/-- The C-typed Möbius critical-value set is empty. -/
theorem MoebiusDataC.moebiusCriticalValuesC_eq_empty (M : MoebiusDataC) :
    M.moebiusCriticalValuesC = ∅ := rfl

/-- ℚ-typed CV transported to ℂ (image under P1Point.mapRatComplex). -/
def criticalValuesC (M : MoebiusData) : Set (P1Point ℂ) :=
  (moebiusCriticalValues M).image P1Point.mapRatComplex

/-- Transport: the transported ℚ-typed CV equals the C-typed CV of the base-changed map (both empty). -/
theorem criticalValuesC_transport (M : MoebiusData) :
    criticalValuesC M = (mapToC M).moebiusCriticalValuesC := by
  simp [criticalValuesC, moebiusCriticalValues, MoebiusDataC.moebiusCriticalValuesC]

/-- C-typed critical values of the base-changed ℚ-Möbius map are empty. -/
theorem mapToC_criticalValuesC_eq_empty (M : MoebiusData) :
    (mapToC M).moebiusCriticalValuesC = ∅ := rfl

/-- maps-to criterion for the C-typed Belyi special set {0,1,infinity}. -/
theorem MoebiusDataC.mapsTo_specialSetC_iff (M : MoebiusDataC) :
    Set.MapsTo M.mapPoints specialSetC specialSetC ↔
      M.mapPoints (P1Point.ofFinite (0 : ℂ)) ∈ specialSetC ∧
      M.mapPoints (P1Point.ofFinite (1 : ℂ)) ∈ specialSetC ∧
      M.mapPoints P1Point.infty ∈ specialSetC := by
  constructor
  · intro h
    exact ⟨h (by simp [specialSetC]), h (by simp [specialSetC]), h (by simp [specialSetC])⟩
  · rintro ⟨h0, h1, hinf⟩ p hp
    rcases hp with rfl | rfl | rfl
    · exact hinf
    · exact h0
    · exact h1

end CVal

end LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1CActual
