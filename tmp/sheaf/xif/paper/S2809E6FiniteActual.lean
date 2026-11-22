import LeanFormal.IUT.ABCBridge.Galois.EllipticPrimeTorsionCardinality
import tmp.sheaf.xif.paper.S2803F6CompleteActual
import LeanFormal.IUT.ABCBridge.Galois.EllipticTorsionAlgebraicity
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

noncomputable section
open WeierstrassCurve
open Polynomial
open LeanFormal.IUT.XiFPaper.S2790F6Actual
open LeanFormal.IUT.XiFPaper.S2803F6CompleteActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2809E6FiniteActual

theorem s2809GaussianPoly_ne_zero :
    (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ) ≠ 0 := by
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ).natDegree = 2 := by
    compute_degree!
  intro h
  have hd := congrArg Polynomial.natDegree h
  rw [hdeg, Polynomial.natDegree_zero] at hd
  norm_num at hd

local instance s2809GaussianFiniteDim : FiniteDimensional ℚ GaussianField :=
  (AdjoinRoot.powerBasis s2809GaussianPoly_ne_zero).basis.finiteDimensional_of_finite

local instance s2809GaussianFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- Nonzero 3-torsion points have x-coordinate in the root set of prePsi_3. -/
theorem S2809_x_mem_prePsi_three_roots
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P : W.toAffine.Point) (hP : (3 : ℤ) • P = 0) (hPne : P ≠ 0) :
    P.xRep 0 ∈ (W.preΨ (3 : ℤ)).roots.toFinset := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact absurd rfl hPne
  · have hbridge : W.DivisionPolynomialDetectsTorsion 3 := W.divisionPolynomialDetectsTorsion_three
    have hzero : W.evalDivisionPolynomialAtPoint (3 : ℤ)
        (WeierstrassCurve.Affine.Point.some x y hns) = 0 := by
      apply hbridge
      simpa using hP
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      W.evalDivisionPolynomial_eq_eval_preΨ_of_odd hns.1
        (by decide : ¬ Even (3 : ℤ))] at hzero
    have hchar : ((3 : ℤ) : K) ≠ 0 := by norm_num
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (W.preΨ_ne_zero hchar),
      Polynomial.IsRoot.def]
    simpa [WeierstrassCurve.Affine.Point.xRep_some] using hzero

/-- The image of nonzero 3-torsion under xRep is finite. -/
theorem S2809_image_finite
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ((fun P : W.toAffine.Point => P.xRep 0) ''
      {P : W.toAffine.Point | (3 : ℤ) • P = 0 ∧ P ≠ 0}).Finite := by
  apply Set.Finite.subset ((W.preΨ (3 : ℤ)).roots.toFinset.finite_toSet)
  rintro a ⟨P, ⟨hP, hPne⟩, rfl⟩
  exact S2809_x_mem_prePsi_three_roots W P hP hPne

/-- Fibers of xRep on nonzero 3-torsion have at most two points. -/
theorem S2809_fiber_finite
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (x : K) (hx : x ∈ (fun P : W.toAffine.Point => P.xRep 0) ''
      {P : W.toAffine.Point | (3 : ℤ) • P = 0 ∧ P ≠ 0}) :
    ({P : W.toAffine.Point | (3 : ℤ) • P = 0 ∧ P ≠ 0} ∩
      (fun P : W.toAffine.Point => P.xRep 0) ⁻¹' {x}).Finite := by
  classical
  obtain ⟨R, hR, hRx⟩ := hx
  obtain ⟨hR3, hRne⟩ := hR
  rcases R with _ | ⟨xR, yR, hRns⟩
  · exact absurd rfl hRne
  let R0 : W.toAffine.Point := .some xR yR hRns
  apply Set.Finite.subset (Set.toFinite ({R0, -R0} : Set W.toAffine.Point))
  intro Q hQ
  rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hQ
  obtain ⟨⟨hQ3, hQne⟩, hQx⟩ := hQ
  rcases Q with _ | ⟨xQ, yQ, hQns⟩
  · exact absurd rfl hQne
  have hxeq : xQ = xR := by
    simpa [WeierstrassCurve.Affine.Point.xRep_some] using hQx.trans hRx.symm
  rcases WeierstrassCurve.Affine.Point.X_eq_iff.mp hxeq with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_iff.mpr (Or.inr h)

/-- The 3-torsion subgroup is finite. -/
theorem S2809_finite_torsionBy_three
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Finite (AddSubgroup.torsionBy W.toAffine.Point (3 : ℤ)) := by
  classical
  let s : Set W.toAffine.Point := {P | (3 : ℤ) • P = 0 ∧ P ≠ 0}
  have hs : s.Finite := by
    apply Set.Finite.of_finite_fibers (f := fun P : W.toAffine.Point => P.xRep 0)
    · simpa [s] using S2809_image_finite W
    · intro x hx
      simpa [s] using S2809_fiber_finite W x (by simpa [s] using hx)
  have hfull : ({P : W.toAffine.Point | (3 : ℤ) • P = 0} : Set W.toAffine.Point).Finite := by
    rw [show {P : W.toAffine.Point | (3 : ℤ) • P = 0} =
        insert 0 {P : W.toAffine.Point | (3 : ℤ) • P = 0 ∧ P ≠ 0} by
      ext P
      constructor
      · intro hP
        by_cases h0 : P = 0
        · exact Or.inl h0
        · exact Or.inr ⟨hP, h0⟩
      · rintro (rfl | ⟨hP, _⟩)
        · simp
        · exact hP]
    exact hs.insert _
  exact hfull.to_subtype



/-- Nonzero 2-torsion points have x-coordinate in the root set of Psi2Sq. -/
theorem S2809_x_mem_Psi2Sq_roots
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P : W.toAffine.Point) (hP : (2 : ℤ) • P = 0) (hPne : P ≠ 0) :
    P.xRep 0 ∈ (W.Ψ₂Sq).roots.toFinset := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact absurd rfl hPne
  ·
    have h2n : (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hns = 0 := by
      rw [← natCast_zsmul]
      exact hP
    have hψ : W.evalDivisionPolynomialAtPoint 2
        (WeierstrassCurve.Affine.Point.some x y hns) = 0 :=
      (W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero _).mp h2n
    rw [WeierstrassCurve.evalDivisionPolynomialAtPoint_some,
      WeierstrassCurve.evalDivisionPolynomial_two] at hψ
    have hchar4 : (4 : K) ≠ 0 := by norm_num
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (W.Ψ₂Sq_ne_zero hchar4),
      Polynomial.IsRoot.def, WeierstrassCurve.Affine.Point.xRep_some]
    change W.Ψ₂Sq.eval x = 0
    have hEq := hns.1
    simp only [WeierstrassCurve.Affine.Equation, WeierstrassCurve.Affine.evalEval_polynomial] at hEq
    rw [WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    linear_combination (-4 : K) * hEq +
      (2 * y + W.a₁ * x + W.a₃) * hψ

/-- The image of nonzero 2-torsion under xRep is finite. -/
theorem S2809_image_finite_two
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ((fun P : W.toAffine.Point => P.xRep 0) ''
      {P : W.toAffine.Point | (2 : ℤ) • P = 0 ∧ P ≠ 0}).Finite := by
  apply Set.Finite.subset ((W.Ψ₂Sq).roots.toFinset.finite_toSet)
  rintro a ⟨P, ⟨hP, hPne⟩, rfl⟩
  exact S2809_x_mem_Psi2Sq_roots W P hP hPne

/-- Fibers of xRep on nonzero 2-torsion have at most two points. -/
theorem S2809_fiber_finite_two
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (x : K) (hx : x ∈ (fun P : W.toAffine.Point => P.xRep 0) ''
      {P : W.toAffine.Point | (2 : ℤ) • P = 0 ∧ P ≠ 0}) :
    ({P : W.toAffine.Point | (2 : ℤ) • P = 0 ∧ P ≠ 0} ∩
      (fun P : W.toAffine.Point => P.xRep 0) ⁻¹' {x}).Finite := by
  classical
  obtain ⟨R, hR, hRx⟩ := hx
  obtain ⟨hR2, hRne⟩ := hR
  rcases R with _ | ⟨xR, yR, hRns⟩
  · exact absurd rfl hRne
  let R0 : W.toAffine.Point := .some xR yR hRns
  apply Set.Finite.subset (Set.toFinite ({R0, -R0} : Set W.toAffine.Point))
  intro Q hQ
  rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hQ
  obtain ⟨⟨hQ2, hQne⟩, hQx⟩ := hQ
  rcases Q with _ | ⟨xQ, yQ, hQns⟩
  · exact absurd rfl hQne
  have hxeq : xQ = xR := by
    simpa [WeierstrassCurve.Affine.Point.xRep_some] using hQx.trans hRx.symm
  rcases WeierstrassCurve.Affine.Point.X_eq_iff.mp hxeq with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_iff.mpr (Or.inr h)

/-- The 2-torsion subgroup is finite. -/
theorem S2809_finite_torsionBy_two
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Finite (AddSubgroup.torsionBy W.toAffine.Point (2 : ℤ)) := by
  classical
  let s : Set W.toAffine.Point := {P | (2 : ℤ) • P = 0 ∧ P ≠ 0}
  have hs : s.Finite := by
    apply Set.Finite.of_finite_fibers (f := fun P : W.toAffine.Point => P.xRep 0)
    · simpa [s] using S2809_image_finite_two W
    · intro x hx
      simpa [s] using S2809_fiber_finite_two W x (by simpa [s] using hx)
  have hfull : ({P : W.toAffine.Point | (2 : ℤ) • P = 0} : Set W.toAffine.Point).Finite := by
    rw [show {P : W.toAffine.Point | (2 : ℤ) • P = 0} =
        insert 0 {P : W.toAffine.Point | (2 : ℤ) • P = 0 ∧ P ≠ 0} by
      ext P
      constructor
      · intro hP
        by_cases h0 : P = 0
        · exact Or.inl h0
        · exact Or.inr ⟨hP, h0⟩
      · rintro (rfl | ⟨hP, _⟩)
        · simp
        · exact hP]
    exact hs.insert _
  exact hfull.to_subtype



/-- The 6-torsion subgroup is finite, via the injection P ↦ (3P, 2P) into
E[2] × E[3]. -/
theorem S2809_finite_torsionBy_six
    {K : Type*} [Field K] [DecidableEq K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] :
    Finite (AddSubgroup.torsionBy W.toAffine.Point (6 : ℤ)) := by
  classical
  haveI h2 : Finite (AddSubgroup.torsionBy W.toAffine.Point (2 : ℤ)) :=
    S2809_finite_torsionBy_two W
  haveI h3 : Finite (AddSubgroup.torsionBy W.toAffine.Point (3 : ℤ)) :=
    S2809_finite_torsionBy_three W
  let f : AddSubgroup.torsionBy W.toAffine.Point (6 : ℤ) →
      AddSubgroup.torsionBy W.toAffine.Point (2 : ℤ) ×
        AddSubgroup.torsionBy W.toAffine.Point (3 : ℤ) :=
    fun P =>
      let h2P : (2 : ℤ) • ((3 : ℤ) • P.1) = 0 := by
        rw [smul_smul]
        norm_num
      let h3P : (3 : ℤ) • ((2 : ℤ) • P.1) = 0 := by
        rw [smul_smul]
        norm_num
      (⟨(3 : ℤ) • P.1, h2P⟩, ⟨(2 : ℤ) • P.1, h3P⟩)
  apply Finite.of_injective f
  intro P Q hPQ
  have h2eq : (2 : ℤ) • P.1 = (2 : ℤ) • Q.1 := by
    have h := congrArg (fun x => x.2.1) hPQ
    simpa [f] using h
  have h3eq : (3 : ℤ) • P.1 = (3 : ℤ) • Q.1 := by
    have h := congrArg (fun x => x.1.1) hPQ
    simpa [f] using h
  apply Subtype.ext
  calc P.1 = ((-2 : ℤ) + 3) • P.1 := by norm_num
    _ = (-2 : ℤ) • P.1 + (3 : ℤ) • P.1 := add_zsmul _ _ _
    _ = -((2 : ℤ) • P.1) + (3 : ℤ) • P.1 := by rw [neg_zsmul]
    _ = -((2 : ℤ) • Q.1) + (3 : ℤ) • Q.1 := by rw [h2eq, h3eq]
    _ = (-2 : ℤ) • Q.1 + (3 : ℤ) • Q.1 := by rw [neg_zsmul]
    _ = ((-2 : ℤ) + 3) • Q.1 := (add_zsmul _ _ _).symm
    _ = Q.1 := by norm_num



/-- The E[6] coordinate set generating F6 is finite. -/
theorem S2809_coordSet_finite : S2790CoordSet.Finite := by
  classical
  letI : S2790EL.curve.IsElliptic := inferInstance
  haveI h6 : Finite (AddSubgroup.torsionBy S2790EL.curve.toAffine.Point (6 : ℤ)) :=
    S2809_finite_torsionBy_six S2790EL.curve
  haveI h6' : Finite {P : S2790EL.curve.toAffine.Point // (6 : ℤ) • P = 0} := by
    change Finite (AddSubgroup.torsionBy S2790EL.curve.toAffine.Point (6 : ℤ))
    exact h6
  have hcoords : ∀ P : S2790EL.curve.toAffine.Point,
      (S2790PointCoords P).Finite := by
    intro P
    rcases P with _ | ⟨x, y, h⟩
    · simp [S2790PointCoords]
    · simp [S2790PointCoords]
  simpa [S2790CoordSet] using
    (Set.finite_iUnion
      (f := fun P : {P : S2790EL.curve.toAffine.Point // (6 : ℤ) • P = 0} =>
        S2790PointCoords P.1) (fun P => hcoords P.1))

/-- F6 is finite-dimensional over Q(i). -/
theorem S2809_finiteDimensional : FiniteDimensional GaussianField S2790F6 := by
  haveI : Finite S2790CoordSet := S2809_coordSet_finite.to_subtype
  exact IntermediateField.finiteDimensional_adjoin
    (K := GaussianField) (L := S2790L) (S := S2790CoordSet) (by
      intro x _
      exact (Algebra.IsAlgebraic.isAlgebraic (R := GaussianField) (A := S2790L) x).isIntegral)

/-- F6 is finite-dimensional over Q. -/
theorem S2809_finiteDimensional_Q : FiniteDimensional ℚ S2790F6 := by
  letI : FiniteDimensional ℚ GaussianField :=
    (AdjoinRoot.powerBasis s2809GaussianPoly_ne_zero).basis.finiteDimensional_of_finite
  letI : FiniteDimensional GaussianField S2790F6 := S2809_finiteDimensional
  exact FiniteDimensional.trans ℚ GaussianField S2790F6

/-- F6 is a number field. -/
theorem S2809_numberField : NumberField S2790F6 := by
  haveI : FiniteDimensional ℚ S2790F6 := S2809_finiteDimensional_Q
  exact NumberField.mk

#check S2809_coordSet_finite
#check S2809_finiteDimensional
#check S2809_numberField

#check S2809_finite_torsionBy_six

#check S2809_finite_torsionBy_two

#check S2809_finite_torsionBy_three

end LeanFormal.IUT.XiFPaper.S2809E6FiniteActual
end