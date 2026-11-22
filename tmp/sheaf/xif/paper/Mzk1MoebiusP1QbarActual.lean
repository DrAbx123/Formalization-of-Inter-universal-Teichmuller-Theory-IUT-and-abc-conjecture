import tmp.sheaf.xif.paper.Mzk1MoebiusP1Actual
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Mzk1MoebiusP1QbarActual — ℚ̄-typed Möbius library (algebraic coefficients)

Port of Mzk1MoebiusP1Actual / Mzk1MoebiusP1CActual from the coefficient fields ℚ and ℂ
to the algebraic closure ℚ̄ = AlgebraicClosure ℚ.  AlgebraicClosure ℚ is a field (Mathlib
instance AlgebraicClosure.instField), with IsAlgClosed and CharZero instances; the
if in the action is decided classically (open scoped Classical, core propDecidable).

STEP 0 prior-art: the ℚ-typed source of truth is
Mzk1Thm25P1CompositeConsumerDesignActual (structure MoebiusData, action with pole/infinity
conventions); its proved extensions are Mzk1MoebiusP1Actual (comp, nonconstancy, composition
law, formal derivative numerator, empty critical values, special-set criterion) and
Mzk1MoebiusP1CActual (ℂ-typed variant and conventions).  The present file repeats the same
field-generic arguments verbatim over ℚ̄, so no new mathematics is invented here.

CONTENTS (all proved; no sorry, no new axiom; the only axioms used are propext,
Classical.choice, Quot.sound):
* MoebiusDataAC: a b c d : AlgebraicClosure ℚ with det : a * d - b * c ≠ 0;
* MoebiusDataAC.mapPoints : P¹(ℚ̄) → P¹(ℚ̄), finite case x ↦ (a x + b)/(c x + d) when
  c x + d ≠ 0, a pole is sent to ∞, and ∞ ↦ a/c if c ≠ 0, ∞ ↦ ∞ if c = 0;
* conventions: mapPoints_infty (rfl), mapPoints_pole, mapPoints_finite;
* MoebiusDataAC.comp (matrix composition) with det(comp) = det(M) * det(N) ≠ 0;
* mapPoints_nonconstant (the action is nonconstant, from det ≠ 0);
* composition laws mapPoints_comp_of_finite (common finite chart) and mapPoints_comp_infty;
* derivativeNumerator: the formal derivative numerator of the fractional linear map is
  a (c z + d) - (a z + b) c = a d - b c ≠ 0, hence there is no finite critical point;
* finiteCriticalPoints = ∅ and the critical-value set moebiusCriticalValues = ∅
  (a degree-one map is unramified);
* specialSet = {∞, 0, 1} in P¹(ℚ̄), mem_specialSet_iff, and the maps-to criterion
  mapsTo_specialSet_iff;
* example: the inversion z ↦ 1/z over ℚ̄ preserves the special set.
-/

noncomputable section
open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1QbarActual

open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-! ### Möbius data over ℚ̄ and its action on P¹(ℚ̄) -/

/-- Möbius data over ℚ̄ = AlgebraicClosure ℚ: the matrix (a b; c d) with
det = a * d - b * c ≠ 0. -/
structure MoebiusDataAC where
  a : AlgebraicClosure ℚ
  b : AlgebraicClosure ℚ
  c : AlgebraicClosure ℚ
  d : AlgebraicClosure ℚ
  det : a * d - b * c ≠ 0

/-- The Möbius action on P¹(ℚ̄) with the standard pole/infinity conventions:
off the pole c x + d = 0 it is x ↦ (a x + b)/(c x + d); a pole is sent to ∞; and
∞ ↦ a/c if c ≠ 0, while c = 0 fixes ∞. -/
noncomputable def MoebiusDataAC.mapPoints (M : MoebiusDataAC) :
    P1Point (AlgebraicClosure ℚ) → P1Point (AlgebraicClosure ℚ)
  | none => if M.c = 0 then P1Point.infty else P1Point.ofFinite (M.a / M.c)
  | some x =>
      if M.c * x + M.d = 0 then P1Point.infty
      else P1Point.ofFinite ((M.a * x + M.b) / (M.c * x + M.d))

/-! ### Conventions at infinity and at poles -/

/-- Infinity convention: c ≠ 0 maps infinity to a/c; c = 0 fixes infinity. -/
theorem MoebiusDataAC.mapPoints_infty (M : MoebiusDataAC) :
    M.mapPoints P1Point.infty =
      if M.c = 0 then P1Point.infty else P1Point.ofFinite (M.a / M.c) := rfl

/-- Pole convention: at a pole the map takes the value infinity. -/
theorem MoebiusDataAC.mapPoints_pole (M : MoebiusDataAC) {x : AlgebraicClosure ℚ}
    (h : M.c * x + M.d = 0) :
    M.mapPoints (P1Point.ofFinite x) = P1Point.infty := by
  simp [MoebiusDataAC.mapPoints, P1Point.ofFinite, h]

/-- Off the pole the map is the finite fractional-linear value. -/
theorem MoebiusDataAC.mapPoints_finite (M : MoebiusDataAC) {x : AlgebraicClosure ℚ}
    (h : M.c * x + M.d ≠ 0) :
    M.mapPoints (P1Point.ofFinite x) =
      P1Point.ofFinite ((M.a * x + M.b) / (M.c * x + M.d)) := by
  simp [MoebiusDataAC.mapPoints, P1Point.ofFinite, h]

/-! ### Composition of ℚ̄-Möbius data -/

/-- Matrix composition of Möbius data over ℚ̄: M after N. -/
def MoebiusDataAC.comp (M N : MoebiusDataAC) : MoebiusDataAC where
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

/-! ### Nonconstancy and composition law of the P¹-action -/

/-- Nonconstancy of the P¹ action of a ℚ̄-Möbius map, from det ≠ 0. -/
theorem MoebiusDataAC.mapPoints_nonconstant (M : MoebiusDataAC) :
    ∃ p q : P1Point (AlgebraicClosure ℚ), M.mapPoints p ≠ M.mapPoints q := by
  by_cases hc : M.c = 0
  · have hd : M.d ≠ 0 := by
      intro hd
      exact M.det (by rw [hc, hd]; ring)
    refine ⟨P1Point.infty, P1Point.ofFinite 0, ?_⟩
    have hzero : M.c * (0 : AlgebraicClosure ℚ) + M.d ≠ 0 := by
      rw [hc, zero_mul, zero_add]
      exact hd
    have h0 : M.mapPoints (P1Point.ofFinite (0 : AlgebraicClosure ℚ)) =
        P1Point.ofFinite (M.b / M.d) := by
      have h := MoebiusDataAC.mapPoints_finite M hzero
      simpa using h
    have hinf : M.mapPoints P1Point.infty = P1Point.infty := by
      rw [MoebiusDataAC.mapPoints_infty, if_pos hc]
    rw [h0, hinf]
    exact fun h => P1Point.ofFinite_ne_infty (M.b / M.d) h.symm
  · have hpole : M.c * (-(M.d / M.c)) + M.d = 0 := by
      field_simp
      ring
    refine ⟨P1Point.ofFinite (-(M.d / M.c)), P1Point.infty, ?_⟩
    have hL : M.mapPoints (P1Point.ofFinite (-(M.d / M.c))) = P1Point.infty :=
      MoebiusDataAC.mapPoints_pole M hpole
    have hR : M.mapPoints P1Point.infty = P1Point.ofFinite (M.a / M.c) := by
      rw [MoebiusDataAC.mapPoints_infty, if_neg hc]
    rw [hL, hR]
    exact fun h => P1Point.ofFinite_ne_infty (M.a / M.c) h.symm

/-- Generic composition law on the finite chart (both denominators nonzero). -/
theorem MoebiusDataAC.mapPoints_comp_of_finite (M N : MoebiusDataAC)
    (x : AlgebraicClosure ℚ)
    (hN : N.c * x + N.d ≠ 0)
    (hMN : (M.c * N.a + M.d * N.c) * x + (M.c * N.b + M.d * N.d) ≠ 0) :
    (M.comp N).mapPoints (P1Point.ofFinite x) =
      M.mapPoints (N.mapPoints (P1Point.ofFinite x)) := by
  have hN' : x * N.c + N.d ≠ 0 := by
    intro h
    exact hN (by linear_combination h)
  have hMN' : M.c * (N.a * x + N.b) + M.d * (N.c * x + N.d) ≠ 0 := by
    intro h
    exact hMN (by linear_combination h)
  have hy : N.mapPoints (P1Point.ofFinite x) =
      P1Point.ofFinite ((N.a * x + N.b) / (N.c * x + N.d)) :=
    MoebiusDataAC.mapPoints_finite N hN
  have hMy : M.c * ((N.a * x + N.b) / (N.c * x + N.d)) + M.d ≠ 0 := by
    have hid : M.c * ((N.a * x + N.b) / (N.c * x + N.d)) + M.d =
        (M.c * (N.a * x + N.b) + M.d * (N.c * x + N.d)) / (N.c * x + N.d) := by
      field_simp [hN']
    rw [hid]
    exact div_ne_zero hMN' hN
  have hR : M.mapPoints (P1Point.ofFinite ((N.a * x + N.b) / (N.c * x + N.d))) =
      P1Point.ofFinite ((M.a * ((N.a * x + N.b) / (N.c * x + N.d)) + M.b) /
        (M.c * ((N.a * x + N.b) / (N.c * x + N.d)) + M.d)) :=
    MoebiusDataAC.mapPoints_finite M hMy
  have hL : (M.comp N).mapPoints (P1Point.ofFinite x) =
      P1Point.ofFinite (((M.a * N.a + M.b * N.c) * x + (M.a * N.b + M.b * N.d)) /
        ((M.c * N.a + M.d * N.c) * x + (M.c * N.b + M.d * N.d))) :=
    MoebiusDataAC.mapPoints_finite (M.comp N) hMN
  rw [hL, hy, hR]
  congr 1
  rw [div_eq_div_iff hMN hMy]
  field_simp [hN']
  ring

/-- Composition law at infinity. -/
theorem MoebiusDataAC.mapPoints_comp_infty (M N : MoebiusDataAC) :
    (M.comp N).mapPoints P1Point.infty =
      M.mapPoints (N.mapPoints P1Point.infty) := by
  have hc : (M.comp N).c = M.c * N.a + M.d * N.c := rfl
  have ha : (M.comp N).a = M.a * N.a + M.b * N.c := rfl
  rw [MoebiusDataAC.mapPoints_infty (M.comp N), MoebiusDataAC.mapPoints_infty N, hc, ha]
  by_cases hN : N.c = 0
  · rw [if_pos hN, MoebiusDataAC.mapPoints_infty M]
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
      field_simp [hMc, hNa]; ring
  · rw [if_neg hN]
    by_cases hMc : M.c = 0
    · have hMd : M.d ≠ 0 := by
        intro h
        exact M.det (by rw [hMc, h]; ring)
      have hL : M.c * N.a + M.d * N.c ≠ 0 := by
        rw [hMc]
        simpa using (mul_ne_zero hMd hN)
      rw [if_neg hL, MoebiusDataAC.mapPoints_finite M (by rw [hMc]; simpa using hMd)]
      congr 1
      field_simp [hN, hMd]
    · by_cases hcc : M.c * N.a + M.d * N.c = 0
      · rw [if_pos hcc]
        have hpole : M.c * (N.a / N.c) + M.d = 0 := by
          have hid : M.c * (N.a / N.c) + M.d = (M.c * N.a + M.d * N.c) / N.c := by
            field_simp [hN]
          rw [hid, hcc]
          simp
        rw [MoebiusDataAC.mapPoints_pole M hpole]
      · rw [if_neg hcc]
        have hfin : M.c * (N.a / N.c) + M.d ≠ 0 := by
          have hid : M.c * (N.a / N.c) + M.d = (M.c * N.a + M.d * N.c) / N.c := by
            field_simp [hN]
          rw [hid]
          exact div_ne_zero hcc hN
        rw [MoebiusDataAC.mapPoints_finite M hfin]
        congr 1
        field_simp [hN, hMc]

/-! ### Formal derivative numerator, critical points and critical values -/

/-- The formal derivative numerator of the fractional linear map x ↦ (a x + b)/(c x + d)
is a (c z + d) - (a z + b) c = a d - b c (the Jacobian of the linear map). -/
theorem MoebiusDataAC.derivativeNumerator (M : MoebiusDataAC)
    (z : AlgebraicClosure ℚ) :
    M.a * (M.c * z + M.d) - (M.a * z + M.b) * M.c = M.a * M.d - M.b * M.c := by
  ring

/-- The formal derivative numerator is a d - b c ≠ 0: there is no finite critical point. -/
theorem MoebiusDataAC.derivativeNumerator_ne_zero (M : MoebiusDataAC)
    (z : AlgebraicClosure ℚ) :
    M.a * (M.c * z + M.d) - (M.a * z + M.b) * M.c ≠ 0 := by
  rw [MoebiusDataAC.derivativeNumerator]
  exact M.det

/-- The finite critical points of the ℚ̄-Möbius action: the finite z at which the formal
derivative numerator vanishes. -/
def MoebiusDataAC.finiteCriticalPoints (M : MoebiusDataAC) : Set (AlgebraicClosure ℚ) :=
  {z | M.a * (M.c * z + M.d) - (M.a * z + M.b) * M.c = 0}

/-- There is no finite critical point (the derivative numerator is a d - b c ≠ 0). -/
theorem MoebiusDataAC.finiteCriticalPoints_eq_empty (M : MoebiusDataAC) :
    M.finiteCriticalPoints = ∅ := by
  ext z
  simp [MoebiusDataAC.finiteCriticalPoints, M.derivativeNumerator_ne_zero z]

/-- The critical-value set of the ℚ̄-Möbius action: the image of the finite critical points
under mapPoints.  (The point at infinity is unramified as well: a degree-one map has no
critical points; here only the finite chart is formalised, as in the ℚ-typed source.) -/
def MoebiusDataAC.moebiusCriticalValues (M : MoebiusDataAC) :
    Set (P1Point (AlgebraicClosure ℚ)) :=
  M.mapPoints '' (P1Point.ofFinite '' M.finiteCriticalPoints)

/-- The critical-value set of a ℚ̄-Möbius action is empty. -/
theorem MoebiusDataAC.moebiusCriticalValues_eq_empty (M : MoebiusDataAC) :
    M.moebiusCriticalValues = ∅ := by
  simp [MoebiusDataAC.moebiusCriticalValues, M.finiteCriticalPoints_eq_empty]

/-! ### The Belyi special set {∞, 0, 1} in P¹(ℚ̄) -/

/-- The Belyi special set over ℚ̄: {0, 1, ∞} ⊂ P¹(ℚ̄). -/
def specialSet : Set (P1Point (AlgebraicClosure ℚ)) :=
  {p | p = P1Point.infty ∨ p = P1Point.ofFinite (0 : AlgebraicClosure ℚ) ∨
    p = P1Point.ofFinite (1 : AlgebraicClosure ℚ)}

/-- Membership criterion for the special set. -/
theorem mem_specialSet_iff {p : P1Point (AlgebraicClosure ℚ)} :
    p ∈ specialSet ↔
      p = P1Point.infty ∨ p = P1Point.ofFinite (0 : AlgebraicClosure ℚ) ∨
        p = P1Point.ofFinite (1 : AlgebraicClosure ℚ) :=
  Iff.rfl

/-- maps-to criterion for the special set {∞, 0, 1} over ℚ̄: a ℚ̄-Möbius map preserves the
special set if and only if it sends each of the three special points into it. -/
theorem mapsTo_specialSet_iff (M : MoebiusDataAC) :
    Set.MapsTo M.mapPoints specialSet specialSet ↔
      M.mapPoints (P1Point.ofFinite (0 : AlgebraicClosure ℚ)) ∈ specialSet ∧
      M.mapPoints (P1Point.ofFinite (1 : AlgebraicClosure ℚ)) ∈ specialSet ∧
      M.mapPoints P1Point.infty ∈ specialSet := by
  constructor
  · intro h
    exact ⟨h (by simp [specialSet]), h (by simp [specialSet]), h (by simp [specialSet])⟩
  · rintro ⟨h0, h1, hinf⟩ p hp
    rcases (mem_specialSet_iff.mp hp) with rfl | rfl | rfl
    · exact hinf
    · exact h0
    · exact h1

/-! ### Base change from ℚ to ℚ̄ -/

open LeanFormal.IUT.XiFPaper.Mzk1Thm25P1CompositeConsumerDesignActual in
/-- Coefficient extension of ℚ-Möbius data to ℚ̄ (base change ℚ → AlgebraicClosure ℚ):
mirrors mapToC in Mzk1MoebiusP1CActual. -/
def mapToQbar (M : MoebiusData) : MoebiusDataAC where
  a := algebraMap ℚ (AlgebraicClosure ℚ) M.a
  b := algebraMap ℚ (AlgebraicClosure ℚ) M.b
  c := algebraMap ℚ (AlgebraicClosure ℚ) M.c
  d := algebraMap ℚ (AlgebraicClosure ℚ) M.d
  det := by
    have h : algebraMap ℚ (AlgebraicClosure ℚ) (M.a * M.d - M.b * M.c) =
        algebraMap ℚ (AlgebraicClosure ℚ) M.a * algebraMap ℚ (AlgebraicClosure ℚ) M.d -
          algebraMap ℚ (AlgebraicClosure ℚ) M.b * algebraMap ℚ (AlgebraicClosure ℚ) M.c := by
      rw [map_sub, map_mul, map_mul]
    intro hzero
    apply M.det
    apply (algebraMap ℚ (AlgebraicClosure ℚ)).injective
    rw [h, hzero, map_zero]

/-! ### Example: the inversion preserves the special set -/

/-- The inversion z ↦ 1/z as ℚ̄-Möbius data. -/
def moebiusInversionAC : MoebiusDataAC where
  a := 0
  b := 1
  c := 1
  d := 0
  det := by norm_num

/-- The inversion permutes the Belyi special set: ψ({∞,0,1}) ⊆ {∞,0,1}. -/
theorem moebiusInversionAC_mapsTo_specialSet :
    Set.MapsTo moebiusInversionAC.mapPoints specialSet specialSet := by
  rw [mapsTo_specialSet_iff]
  refine ⟨?_, ?_, ?_⟩
  · have h : moebiusInversionAC.c * (0 : AlgebraicClosure ℚ) + moebiusInversionAC.d = 0 := by
      simp [moebiusInversionAC]
    rw [MoebiusDataAC.mapPoints_pole _ h, mem_specialSet_iff]
    exact Or.inl rfl
  · have h : moebiusInversionAC.c * (1 : AlgebraicClosure ℚ) + moebiusInversionAC.d ≠ 0 := by
      simp [moebiusInversionAC]
    rw [MoebiusDataAC.mapPoints_finite _ h, mem_specialSet_iff]
    right; right
    simp [moebiusInversionAC]
  · have hc : moebiusInversionAC.c ≠ 0 := by simp [moebiusInversionAC]
    rw [MoebiusDataAC.mapPoints_infty, if_neg hc, mem_specialSet_iff]
    right; left
    simp [moebiusInversionAC]

end LeanFormal.IUT.XiFPaper.Mzk1MoebiusP1QbarActual
