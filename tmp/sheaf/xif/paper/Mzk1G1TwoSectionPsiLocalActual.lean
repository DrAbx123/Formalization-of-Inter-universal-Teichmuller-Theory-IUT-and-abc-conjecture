import tmp.sheaf.xif.paper.Mzk1G1TwoSectionDataActual
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionPsiLocalActual
open AlgebraicGeometry Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionDataActual

variable {A : Type} [CommRing A] [Algebra ℚ A]

/-- The actual ratio s1/s0 in the localization A[s0^{-1}]. -/
noncomputable def ratio0 (D : TwoSectionData A) : Localization.Away D.s0 :=
  IsLocalization.mk' (Localization.Away D.s0) D.s1 ⟨D.s0, Submonoid.mem_powers D.s0⟩

/-- The actual ratio s0/s1 in the localization A[s1^{-1}]. -/
noncomputable def ratio1 (D : TwoSectionData A) : Localization.Away D.s1 :=
  IsLocalization.mk' (Localization.Away D.s1) D.s0 ⟨D.s1, Submonoid.mem_powers D.s1⟩

/-- First chart map of psi = [s0 : s1]: on D(s0) the target coordinate is s1/s0. -/
noncomputable def psiChart0 (D : TwoSectionData A) :
    Spec (CommRingCat.of (Localization.Away D.s0)) ⟶
      Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (algebraMap ℚ (Localization.Away D.s0)) (ratio0 D)))

/-- Second chart map of psi = [s0 : s1]: on D(s1) the target coordinate is s0/s1. -/
noncomputable def psiChart1 (D : TwoSectionData A) :
    Spec (CommRingCat.of (Localization.Away D.s1)) ⟶
      Spec (CommRingCat.of (Polynomial ℚ)) :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (algebraMap ℚ (Localization.Away D.s1)) (ratio1 D)))

/-- PSI IS DEFINED EVERYWHERE: no prime of A contains both sections, i.e. the two
chart opens D(s0), D(s1) cover the source. -/
theorem psi_no_common_zero (D : TwoSectionData A) (P : Ideal A) [P.IsPrime] :
    D.s0 ∉ P ∨ D.s1 ∉ P := by
  by_contra h
  push_neg at h
  exact not_both_mem_of_span_top D.span_top P h

/-- The overlap ring A[(s0 s1)^{-1}] of the two charts. -/
noncomputable abbrev overlapRing (D : TwoSectionData A) : Type _ :=
  Localization.Away (D.s0 * D.s1)

/-- s0 is a unit in the overlap (s0 s1 is inverted). -/
theorem isUnit_algebraMap_s0 (D : TwoSectionData A) :
    IsUnit (algebraMap A (overlapRing D) D.s0) :=
  (IsLocalization.Away.algebraMap_isUnit_iff (x := D.s0 * D.s1)).mpr
    ⟨1, by simpa using dvd_mul_right D.s0 D.s1⟩

/-- s1 is a unit in the overlap (s0 s1 is inverted). -/
theorem isUnit_algebraMap_s1 (D : TwoSectionData A) :
    IsUnit (algebraMap A (overlapRing D) D.s1) :=
  (IsLocalization.Away.algebraMap_isUnit_iff (x := D.s0 * D.s1)).mpr
    ⟨1, by simpa using dvd_mul_left D.s1 D.s0⟩

/-- The unit with value s0 in the overlap ring. -/
noncomputable def overlapUnit0 (D : TwoSectionData A) : (overlapRing D)ˣ :=
  (isUnit_algebraMap_s0 D).unit

/-- The unit with value s1 in the overlap ring. -/
noncomputable def overlapUnit1 (D : TwoSectionData A) : (overlapRing D)ˣ :=
  (isUnit_algebraMap_s1 D).unit

@[simp] theorem overlapUnit0_val (D : TwoSectionData A) :
    ((overlapUnit0 D : (overlapRing D)ˣ) : overlapRing D) = algebraMap A (overlapRing D) D.s0 :=
  IsUnit.unit_spec _

@[simp] theorem overlapUnit1_val (D : TwoSectionData A) :
    ((overlapUnit1 D : (overlapRing D)ˣ) : overlapRing D) = algebraMap A (overlapRing D) D.s1 :=
  IsUnit.unit_spec _

/-- First overlap coordinate: s1/s0 = s1 * s0^{-1} in the overlap ring. -/
noncomputable def overlapCoord0 (D : TwoSectionData A) : overlapRing D :=
  ((overlapUnit1 D * (overlapUnit0 D)⁻¹ : (overlapRing D)ˣ) : overlapRing D)

/-- Second overlap coordinate: s0/s1 = s0 * s1^{-1} in the overlap ring. -/
noncomputable def overlapCoord1 (D : TwoSectionData A) : overlapRing D :=
  ((overlapUnit0 D * (overlapUnit1 D)⁻¹ : (overlapRing D)ˣ) : overlapRing D)

/-- The first overlap coordinate really is s1/s0: coord0 * s0 = s1. -/
theorem overlapCoord0_spec (D : TwoSectionData A) :
    overlapCoord0 D * algebraMap A (overlapRing D) D.s0 = algebraMap A (overlapRing D) D.s1 := by
  unfold overlapCoord0
  rw [← overlapUnit0_val D, ← overlapUnit1_val D, ← Units.val_mul]
  rw [show overlapUnit1 D * (overlapUnit0 D)⁻¹ * overlapUnit0 D = overlapUnit1 D by group]

/-- The second overlap coordinate really is s0/s1: coord1 * s1 = s0. -/
theorem overlapCoord1_spec (D : TwoSectionData A) :
    overlapCoord1 D * algebraMap A (overlapRing D) D.s1 = algebraMap A (overlapRing D) D.s0 := by
  unfold overlapCoord1
  rw [← overlapUnit1_val D, ← overlapUnit0_val D, ← Units.val_mul]
  rw [show overlapUnit0 D * (overlapUnit1 D)⁻¹ * overlapUnit1 D = overlapUnit0 D by group]

/-- THE COCYCLE: on the overlap the two chart coordinates are reciprocal,
coord0 * coord1 = 1.  Hence the two local chart maps glue to a morphism to P1. -/
theorem overlapCoord_mul_cocycle (D : TwoSectionData A) :
    overlapCoord0 D * overlapCoord1 D = 1 := by
  unfold overlapCoord0 overlapCoord1
  rw [← Units.val_mul]
  rw [show overlapUnit1 D * (overlapUnit0 D)⁻¹ * (overlapUnit0 D * (overlapUnit1 D)⁻¹) = 1 by group]
  exact Units.val_one

/-- Actual local data for psi = [s0 : s1]: the two chart morphisms, together
with the reciprocal overlap coordinates (the gluing datum). -/
structure TwoSectionPsiData (D : TwoSectionData A) where
  chart0 : Spec (CommRingCat.of (Localization.Away D.s0)) ⟶
    Spec (CommRingCat.of (Polynomial ℚ))
  chart1 : Spec (CommRingCat.of (Localization.Away D.s1)) ⟶
    Spec (CommRingCat.of (Polynomial ℚ))
  chart0_eq : chart0 = psiChart0 D
  chart1_eq : chart1 = psiChart1 D
  overlap0 : overlapRing D
  overlap1 : overlapRing D
  overlap0_spec : overlap0 * algebraMap A (overlapRing D) D.s0 = algebraMap A (overlapRing D) D.s1
  overlap1_spec : overlap1 * algebraMap A (overlapRing D) D.s1 = algebraMap A (overlapRing D) D.s0
  cocycle : overlap0 * overlap1 = 1

/-- Inhabitant: every unit-ideal two-section datum produces actual psi chart data
with the reciprocal cocycle. -/
noncomputable def twoSectionPsiData (D : TwoSectionData A) : TwoSectionPsiData D where
  chart0 := psiChart0 D
  chart1 := psiChart1 D
  chart0_eq := rfl
  chart1_eq := rfl
  overlap0 := overlapCoord0 D
  overlap1 := overlapCoord1 D
  overlap0_spec := overlapCoord0_spec D
  overlap1_spec := overlapCoord1_spec D
  cocycle := overlapCoord_mul_cocycle D

#print axioms psi_no_common_zero
#print axioms overlapCoord_mul_cocycle
#print axioms twoSectionPsiData
end LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionPsiLocalActual
