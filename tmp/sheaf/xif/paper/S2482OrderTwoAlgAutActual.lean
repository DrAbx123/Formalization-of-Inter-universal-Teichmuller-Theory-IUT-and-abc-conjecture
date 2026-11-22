import tmp.sheaf.xif.paper.S2482QiNontrivialActual
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiNontrivialActual
open CategoryTheory
open Polynomial

/-! ## 1. Coordinates and the Weierstrass relation in the coordinate ring

The coordinate ring is R = F[x,y]/(y^2 - x^3 + x).  We first fix the two
coordinate functions and record the defining relation. -/

/-- The image of the x-coordinate in the coordinate ring. -/
abbrev S2482cx : S2482CoordinateRing :=
  Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0)

/-- The image of the y-coordinate in the coordinate ring. -/
abbrev S2482cy : S2482CoordinateRing :=
  Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 1)

theorem S2482_affine_polynomial_eq :
    S2482AffinePolynomial =
      MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0 := by
  simp [S2482AffinePolynomial,
    LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial, S2482Curve]
  ring

theorem S2482_relation : S2482cy ^ 2 = S2482cx ^ 3 - S2482cx := by
  have hmem : MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0
      ∈ Ideal.span {S2482AffinePolynomial} := by
    rw [← S2482_affine_polynomial_eq]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hzero : Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
      (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simp only [map_add, map_sub, map_pow] at hzero
  have h : S2482cy ^ 2 - S2482cx ^ 3 + S2482cx = 0 := hzero
  linear_combination h

/-! ## 2. The model ring F[X][T]/(T^2 - (X^3 - X))

To control the coordinate ring we use the quotient of F[X][T] by the monic
polynomial T^2 - (X^3 - X); the map x -> X, y -> T is an F-algebra map from
R to the model ring, and in the model ring normal forms are unique because the
defining polynomial is monic of degree two. -/

/-- The polynomial X^3 - X. -/
abbrev S2482P : Polynomial F := X ^ 3 - X

theorem S2482P_natDegree : S2482P.natDegree = 3 := by
  rw [S2482P,
    natDegree_sub_eq_left_of_natDegree_lt (p := X ^ 3) (q := X) (by
      rw [natDegree_X_pow, natDegree_X]
      norm_num),
    natDegree_X_pow]

theorem S2482P_ne_zero : S2482P ≠ 0 := by
  intro h
  have hd := S2482P_natDegree
  rw [h] at hd
  simp at hd

theorem S2482P_derivative : derivative S2482P = 3 * X ^ 2 - 1 := by
  rw [S2482P, derivative_sub, derivative_X_pow, derivative_X]
  norm_num
  exact map_natCast Polynomial.C 3

/-- The monic defining polynomial of the model ring. -/
abbrev S2482G : Polynomial (Polynomial F) := X ^ 2 - C S2482P

theorem S2482G_monic : S2482G.Monic := by
  have h := monic_X_pow_sub_C S2482P (n := 2) (by norm_num)
  simpa [S2482G] using h

theorem S2482G_natDegree : S2482G.natDegree = 2 := by
  have h := natDegree_X_pow_sub_C (R := Polynomial F) (n := 2) (r := S2482P)
  simpa [S2482G] using h

/-- The model ring F[X][T]/(T^2 - (X^3 - X)). -/
abbrev S2482Model : Type := AdjoinRoot S2482G

theorem S2482Model_root_sq :
    AdjoinRoot.root S2482G ^ 2 = algebraMap (Polynomial F) S2482Model S2482P := by
  have hroot : AdjoinRoot.root S2482G
      = AdjoinRoot.mk S2482G (X : Polynomial (Polynomial F)) := rfl
  rw [hroot, ← map_pow]
  have hdvd : S2482G ∣ ((X : Polynomial (Polynomial F)) ^ 2 - C S2482P) :=
    ⟨1, by simp [S2482G]⟩
  rw [AdjoinRoot.mk_eq_mk.mpr hdvd, AdjoinRoot.mk_C]
  rfl

theorem S2482Model_algebraMap_eq (a : Polynomial F) :
    algebraMap (Polynomial F) S2482Model a
      = AdjoinRoot.mk S2482G (C a) := by
  rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C]

/-- The two variable assignment into the model ring. -/
def S2482ModelVar : Fin 2 → S2482Model :=
  fun i => if i = 0 then (algebraMap (Polynomial F) S2482Model) X
    else AdjoinRoot.root S2482G

theorem S2482ModelVar_zero :
    S2482ModelVar 0 = (algebraMap (Polynomial F) S2482Model) X := by
  simp [S2482ModelVar]

theorem S2482ModelVar_one : S2482ModelVar 1 = AdjoinRoot.root S2482G := by
  simp [S2482ModelVar]

theorem S2482Model_aeval_affine :
    MvPolynomial.aeval S2482ModelVar S2482AffinePolynomial = 0 := by
  rw [S2482_affine_polynomial_eq]
  simp only [map_add, map_sub, map_pow, MvPolynomial.aeval_X,
    S2482ModelVar_zero, S2482ModelVar_one]
  rw [S2482Model_root_sq, ← map_pow, ← map_sub, ← map_add]
  have hz : S2482P - X ^ 3 + X = 0 := by
    simp only [S2482P]
    ring
  rw [hz, map_zero]

/-- The F-algebra map from the coordinate ring to the model ring. -/
def S2482ModelMap : S2482CoordinateRing →ₐ[F] S2482Model :=
  Ideal.Quotient.liftₐ (Ideal.span {S2482AffinePolynomial})
    (MvPolynomial.aeval S2482ModelVar) (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨q, rfl⟩ := ha
      rw [map_mul, S2482Model_aeval_affine, zero_mul])

theorem S2482ModelMap_cx :
    S2482ModelMap S2482cx = (algebraMap (Polynomial F) S2482Model) X := by
  simp [S2482ModelMap, S2482cx, S2482ModelVar]

theorem S2482ModelMap_cy :
    S2482ModelMap S2482cy = AdjoinRoot.root S2482G := by
  simp [S2482ModelMap, S2482cy, S2482ModelVar]

/-! ## 3. Normal-form uniqueness in the model ring -/

theorem S2482Model_eq_zero {A B : Polynomial F}
    (h : (algebraMap (Polynomial F) S2482Model) A
        + (algebraMap (Polynomial F) S2482Model) B * AdjoinRoot.root S2482G = 0) :
    A = 0 ∧ B = 0 := by
  have hroot : AdjoinRoot.root S2482G
      = AdjoinRoot.mk S2482G (X : Polynomial (Polynomial F)) := rfl
  have h0 : AdjoinRoot.mk S2482G (C A + C B * X) = 0 := by
    have hrw : AdjoinRoot.mk S2482G (C A + C B * X)
        = (algebraMap (Polynomial F) S2482Model) A
          + (algebraMap (Polynomial F) S2482Model) B * AdjoinRoot.root S2482G := by
      rw [S2482Model_algebraMap_eq, S2482Model_algebraMap_eq, hroot,
        ← map_mul, ← map_add]
    rw [hrw, h]
  rw [AdjoinRoot.mk_eq_zero] at h0
  have hdeg : (C A + C B * X : Polynomial (Polynomial F)).natDegree ≤ 1 := by
    have h1 : (C A : Polynomial (Polynomial F)).natDegree ≤ 0 := by
      rw [natDegree_C]
    have h2 : (C B * X : Polynomial (Polynomial F)).natDegree ≤ 1 := by
      calc (C B * X : Polynomial (Polynomial F)).natDegree
          ≤ (C B : Polynomial (Polynomial F)).natDegree + X.natDegree := natDegree_mul_le
        _ ≤ 0 + 1 := by rw [natDegree_C, natDegree_X]
    exact le_trans (natDegree_add_le _ _) (by omega)
  have hf0 : (C A + C B * X : Polynomial (Polynomial F)) = 0 := by
    by_contra hf
    have hle := Polynomial.natDegree_le_of_dvd h0 hf
    rw [S2482G_natDegree] at hle
    omega
  constructor
  · have hc := congrArg (fun p : Polynomial (Polynomial F) => p.coeff 0) hf0
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_zero] at hc
    simpa using hc
  · have hc := congrArg (fun p : Polynomial (Polynomial F) => p.coeff 1) hf0
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_zero] at hc
    simpa using hc

theorem S2482ModelMap_aeval (A : Polynomial F) :
    S2482ModelMap (Polynomial.aeval S2482cx A)
      = (algebraMap (Polynomial F) S2482Model) A := by
  induction A using Polynomial.induction_on with
  | C a =>
      rw [Polynomial.aeval_C, AlgHom.commutes, Polynomial.C_eq_algebraMap]
      rfl
  | add p q hp hq =>
      rw [map_add, map_add, hp, hq, map_add]
  | monomial n a h =>
      have h1 : (Polynomial.C a * X ^ (n + 1) : Polynomial F)
          = (Polynomial.C a * X ^ n) * X := by ring
      have h2 : Polynomial.aeval S2482cx (Polynomial.C a * X ^ (n + 1))
          = Polynomial.aeval S2482cx (Polynomial.C a * X ^ n) * S2482cx := by
        rw [h1, map_mul, Polynomial.aeval_X]
      have h3 : (algebraMap (Polynomial F) S2482Model) (Polynomial.C a * X ^ (n + 1))
          = (algebraMap (Polynomial F) S2482Model) (Polynomial.C a * X ^ n)
            * (algebraMap (Polynomial F) S2482Model) X := by
        rw [h1, map_mul]
      rw [h2, h3, map_mul, h, S2482ModelMap_cx]

/-! ## 4. Normal forms in the coordinate ring -/

theorem S2482_normal_form_surj (u : S2482CoordinateRing) :
    ∃ A B : Polynomial F,
      u = Polynomial.aeval S2482cx A + Polynomial.aeval S2482cx B * S2482cy := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Ideal.span {S2482AffinePolynomial}) u
  induction f using MvPolynomial.induction_on with
  | C a =>
      refine ⟨Polynomial.C a, 0, ?_⟩
      rw [Polynomial.aeval_C, Polynomial.aeval_zero, zero_mul, add_zero]
      simpa using Ideal.Quotient.mk_algebraMap (R₁ := F)
        (I := Ideal.span {S2482AffinePolynomial}) a
  | add p q hp hq =>
      obtain ⟨A, B, hAB⟩ := hp
      obtain ⟨C, E, hCE⟩ := hq
      refine ⟨A + C, B + E, ?_⟩
      rw [map_add, hAB, hCE, map_add, map_add]
      ring
  | mul_X p n hp =>
      obtain ⟨A, B, hAB⟩ := hp
      have hmul : Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
            (p * MvPolynomial.X n)
          = Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) p
            * Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X n) := by
        rw [map_mul]
      rw [hmul, hAB]
      fin_cases n
      · refine ⟨A * X, B * X, ?_⟩
        show (Polynomial.aeval S2482cx A + Polynomial.aeval S2482cx B * S2482cy) * S2482cx
          = Polynomial.aeval S2482cx (A * X) + Polynomial.aeval S2482cx (B * X) * S2482cy
        rw [map_mul, map_mul, Polynomial.aeval_X]
        ring
      · refine ⟨B * S2482P, A, ?_⟩
        show (Polynomial.aeval S2482cx A + Polynomial.aeval S2482cx B * S2482cy) * S2482cy
          = Polynomial.aeval S2482cx (B * S2482P) + Polynomial.aeval S2482cx A * S2482cy
        have hP : Polynomial.aeval S2482cx S2482P = S2482cx ^ 3 - S2482cx := by
          rw [S2482P, map_sub, map_pow, Polynomial.aeval_X]
        have hsq : S2482cy * S2482cy = S2482cx ^ 3 - S2482cx := by
          have hh := S2482_relation
          rw [pow_two] at hh
          exact hh
        calc (Polynomial.aeval S2482cx A + Polynomial.aeval S2482cx B * S2482cy) * S2482cy
            = Polynomial.aeval S2482cx A * S2482cy
              + Polynomial.aeval S2482cx B * (S2482cy * S2482cy) := by ring
          _ = Polynomial.aeval S2482cx A * S2482cy
              + Polynomial.aeval S2482cx B * (S2482cx ^ 3 - S2482cx) := by rw [hsq]
          _ = Polynomial.aeval S2482cx (B * S2482P) + Polynomial.aeval S2482cx A * S2482cy := by
              rw [map_mul, hP]
              ring

theorem S2482_normal_form_unique {A B : Polynomial F}
    (h : Polynomial.aeval S2482cx A + Polynomial.aeval S2482cx B * S2482cy = 0) :
    A = 0 ∧ B = 0 := by
  have hmap : S2482ModelMap
      (Polynomial.aeval S2482cx A + Polynomial.aeval S2482cx B * S2482cy) = 0 := by
    rw [h, map_zero]
  rw [map_add, map_mul, S2482ModelMap_aeval, S2482ModelMap_aeval, S2482ModelMap_cy] at hmap
  exact S2482Model_eq_zero hmap

theorem S2482_aeval_injective :
    Function.Injective (Polynomial.aeval S2482cx : Polynomial F →ₐ[F] S2482CoordinateRing) := by
  intro A B hAB
  have h : Polynomial.aeval S2482cx (A - B) = 0 := by
    rw [map_sub, hAB, sub_self]
  have hz := (S2482_normal_form_unique (A := A - B) (B := 0) (by simpa using h)).1
  exact sub_eq_zero.mp hz

theorem S2482cy_ne_zero : S2482cy ≠ 0 := by
  intro h
  have huniq := S2482_normal_form_unique (A := 0) (B := 1) (by simpa using h)
  exact one_ne_zero huniq.2

theorem S2482cy_mul_eq_zero {u : S2482CoordinateRing} (h : S2482cy * u = 0) : u = 0 := by
  obtain ⟨A, B, hAB⟩ := S2482_normal_form_surj u
  have hP : Polynomial.aeval S2482cx S2482P = S2482cx ^ 3 - S2482cx := by
    rw [S2482P, map_sub, map_pow, Polynomial.aeval_X]
  have hsq : S2482cy * S2482cy = S2482cx ^ 3 - S2482cx := by
    have hh := S2482_relation
    rw [pow_two] at hh
    exact hh
  have h0 : S2482cy * (Polynomial.aeval S2482cx A + Polynomial.aeval S2482cx B * S2482cy)
      = 0 := by
    rw [hAB] at h
    exact h
  have h' : Polynomial.aeval S2482cx (B * S2482P) + Polynomial.aeval S2482cx A * S2482cy = 0 := by
    have hexp : S2482cy * (Polynomial.aeval S2482cx A + Polynomial.aeval S2482cx B * S2482cy)
        = Polynomial.aeval S2482cx (B * S2482P) + Polynomial.aeval S2482cx A * S2482cy := by
      rw [map_mul, hP, ← hsq]
      ring
    rw [hexp] at h0
    exact h0
  obtain ⟨hBP, hA⟩ := S2482_normal_form_unique h'
  have hB : B = 0 := by
    rcases mul_eq_zero.mp hBP with hB | hB
    · exact hB
    · exact absurd hB S2482P_ne_zero
  rw [hAB, hA, hB]
  simp

/-! ## 5. Evaluation at the coordinates and the basic derivation -/

/-- Evaluation of a two-variable polynomial at the two coordinate functions. -/
def S2482ev : MvPolynomial (Fin 2) F →ₐ[F] S2482CoordinateRing :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then S2482cx else S2482cy)

theorem S2482ev_eq_mk :
    S2482ev = Ideal.Quotient.mkₐ F (Ideal.span {S2482AffinePolynomial}) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · show MvPolynomial.aeval
        (fun i : Fin 2 => if i = 0 then S2482cx else S2482cy) (MvPolynomial.X 0)
      = Ideal.Quotient.mkₐ F (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 0)
    rw [MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    rfl
  · show MvPolynomial.aeval
        (fun i : Fin 2 => if i = 0 then S2482cx else S2482cy) (MvPolynomial.X 1)
      = Ideal.Quotient.mkₐ F (Ideal.span {S2482AffinePolynomial}) (MvPolynomial.X 1)
    rw [MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    rfl

theorem S2482ev_apply (f : MvPolynomial (Fin 2) F) :
    S2482ev f = Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) f := by
  rw [S2482ev_eq_mk, Ideal.Quotient.mkₐ_eq_mk]

theorem S2482ev_p : S2482ev S2482AffinePolynomial = 0 := by
  rw [S2482ev_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The two-variable representative of the derivative 3X^2-1 of X^3-X. -/
def S2482Q : MvPolynomial (Fin 2) F := 3 * MvPolynomial.X 0 ^ 2 - 1

theorem S2482ev_X0 : S2482ev (MvPolynomial.X 0) = S2482cx := by
  simp [S2482ev, S2482cx]

theorem S2482ev_X1 : S2482ev (MvPolynomial.X 1) = S2482cy := by
  simp [S2482ev, S2482cy]

theorem S2482ev_Q : S2482ev S2482Q = 3 * S2482cx ^ 2 - 1 := by
  simp [S2482ev, S2482Q, S2482cx]

theorem S2482ev_X0_sq : S2482ev (MvPolynomial.X 0 ^ 2) = S2482cx ^ 2 := by
  rw [S2482ev_apply, map_pow]

/-- The formal derivative map, written on two-variable polynomials. -/
def S2482psi (f : MvPolynomial (Fin 2) F) : S2482CoordinateRing :=
  S2482ev (MvPolynomial.pderiv 0 f) * (2 * S2482cy)
    + S2482ev (MvPolynomial.pderiv 1 f) * S2482ev S2482Q

theorem S2482psi_zero : S2482psi 0 = 0 := by
  simp [S2482psi]

theorem S2482psi_add (f g : MvPolynomial (Fin 2) F) :
    S2482psi (f + g) = S2482psi f + S2482psi g := by
  simp only [S2482psi, map_add]
  ring

theorem S2482psi_neg (f : MvPolynomial (Fin 2) F) :
    S2482psi (-f) = - S2482psi f := by
  simp only [S2482psi, map_neg]
  ring

/-- The linear map underlying the formal derivative, assembled from linear pieces. -/
def S2482psiLin : MvPolynomial (Fin 2) F →ₗ[F] S2482CoordinateRing :=
  (LinearMap.mulLeft F (2 * S2482cy)).comp
      ((S2482ev : MvPolynomial (Fin 2) F →ₐ[F] S2482CoordinateRing).toLinearMap.comp
        (MvPolynomial.pderiv 0).toLinearMap)
    + (LinearMap.mulLeft F (S2482ev S2482Q)).comp
      ((S2482ev : MvPolynomial (Fin 2) F →ₐ[F] S2482CoordinateRing).toLinearMap.comp
        (MvPolynomial.pderiv 1).toLinearMap)

theorem S2482psiLin_apply (f : MvPolynomial (Fin 2) F) :
    S2482psiLin f = S2482psi f := by
  show (2 * S2482cy) * S2482ev (MvPolynomial.pderiv 0 f)
      + S2482ev S2482Q * S2482ev (MvPolynomial.pderiv 1 f)
      = S2482ev (MvPolynomial.pderiv 0 f) * (2 * S2482cy)
        + S2482ev (MvPolynomial.pderiv 1 f) * S2482ev S2482Q
  ring

theorem S2482psi_smul (c : F) (f : MvPolynomial (Fin 2) F) :
    S2482psi (c • f) = c • S2482psi f := by
  rw [← S2482psiLin_apply, ← S2482psiLin_apply]
  exact S2482psiLin.map_smul c f

theorem S2482psi_mul (f g : MvPolynomial (Fin 2) F) :
    S2482psi (f * g) = S2482ev f * S2482psi g + S2482ev g * S2482psi f := by
  simp only [S2482psi, MvPolynomial.pderiv_mul, map_add, map_mul]
  ring

theorem S2482psi_X0 : S2482psi (MvPolynomial.X 0) = 2 * S2482cy := by
  simp [S2482psi, MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne]

theorem S2482psi_X1 : S2482psi (MvPolynomial.X 1) = S2482ev S2482Q := by
  simp [S2482psi, MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne]

theorem S2482psi_X0_sq :
    S2482psi (MvPolynomial.X 0 ^ 2) = 4 * S2482cx * S2482cy := by
  rw [pow_two, S2482psi_mul, S2482psi_X0, S2482ev_X0]
  ring

theorem S2482psi_X0_cube :
    S2482psi (MvPolynomial.X 0 ^ 3) = 6 * S2482cx ^ 2 * S2482cy := by
  rw [show (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 2) F)
      = MvPolynomial.X 0 ^ 2 * MvPolynomial.X 0 by ring]
  rw [S2482psi_mul, S2482psi_X0_sq, S2482psi_X0, S2482ev_X0, S2482ev_X0_sq]
  ring

theorem S2482psi_X1_sq :
    S2482psi (MvPolynomial.X 1 ^ 2) = 2 * S2482cy * S2482ev S2482Q := by
  rw [pow_two, S2482psi_mul, S2482psi_X1, S2482ev_X1]
  ring

theorem S2482psi_affine_eq :
    S2482psi (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0) = 0 := by
  rw [show (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0
      : MvPolynomial (Fin 2) F)
      = MvPolynomial.X 1 ^ 2 + (-(MvPolynomial.X 0 ^ 3)) + MvPolynomial.X 0 by ring]
  rw [S2482psi_add, S2482psi_add, S2482psi_neg, S2482psi_X1_sq, S2482psi_X0_cube,
    S2482psi_X0, S2482ev_Q]
  ring

theorem S2482psi_p : S2482psi S2482AffinePolynomial = 0 := by
  have hp : S2482psi S2482AffinePolynomial
      = S2482psi (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 + MvPolynomial.X 0) := by
    rw [S2482_affine_polynomial_eq]
  rw [hp, S2482psi_affine_eq]

theorem S2482psi_vanishes_of (q : MvPolynomial (Fin 2) F)
    (hq : S2482psi q = 0) (hqe : S2482ev q = 0) (g : MvPolynomial (Fin 2) F) :
    S2482psi (q * g) = 0 := by
  rw [S2482psi_mul, hq, hqe, zero_mul, mul_zero, add_zero]

theorem S2482psi_span {f : MvPolynomial (Fin 2) F}
    (hf : f ∈ Ideal.span {S2482AffinePolynomial}) : S2482psi f = 0 := by
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hf
  rw [hg]
  exact S2482psi_vanishes_of S2482AffinePolynomial S2482psi_p S2482ev_p g

theorem S2482psiKer :
    ((Ideal.span {S2482AffinePolynomial}).restrictScalars F) ≤ S2482psiLin.ker := by
  intro x hx
  rw [LinearMap.mem_ker, S2482psiLin_apply]
  exact S2482psi_span (by simpa using hx)

/-- The basic derivation, descended to the coordinate ring. -/
def S2482Dlin : S2482CoordinateRing →ₗ[F] S2482CoordinateRing :=
  Submodule.liftQ ((Ideal.span {S2482AffinePolynomial}).restrictScalars F) S2482psiLin
    S2482psiKer

theorem S2482Dlin_mk (f : MvPolynomial (Fin 2) F) :
    S2482Dlin (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) f) = S2482psi f := by
  have h : (Submodule.liftQ ((Ideal.span {S2482AffinePolynomial}).restrictScalars F)
      S2482psiLin S2482psiKer) (Submodule.Quotient.mk f) = S2482psi f := by
    rw [Submodule.liftQ_apply, S2482psiLin_apply]
  exact h

theorem S2482Dlin_leibniz (u v : S2482CoordinateRing) :
    S2482Dlin (u * v) = u • S2482Dlin v + v • S2482Dlin u := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Ideal.span {S2482AffinePolynomial}) u
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Ideal.span {S2482AffinePolynomial}) v
  rw [← map_mul, S2482Dlin_mk, S2482Dlin_mk, S2482Dlin_mk, S2482psi_mul,
    S2482ev_apply, S2482ev_apply, smul_eq_mul, smul_eq_mul]

/-- The basic derivation of the coordinate ring. -/
def S2482D : Derivation F S2482CoordinateRing S2482CoordinateRing where
  toLinearMap := S2482Dlin
  map_one_eq_zero' := by
    have h1 : (1 : S2482CoordinateRing)
        = Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial}) 1 := (map_one _).symm
    rw [h1, S2482Dlin_mk]
    simp [S2482psi]
  leibniz' := S2482Dlin_leibniz

theorem S2482D_x : S2482D S2482cx = 2 * S2482cy := by
  change S2482Dlin (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
    (MvPolynomial.X 0)) = 2 * S2482cy
  rw [S2482Dlin_mk]
  simp [S2482psi, MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne]

theorem S2482D_y : S2482D S2482cy = 3 * S2482cx ^ 2 - 1 := by
  change S2482Dlin (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
    (MvPolynomial.X 1)) = 3 * S2482cx ^ 2 - 1
  rw [S2482Dlin_mk, S2482psi_X1, S2482ev_Q]

end LeanFormal.IUT.XiFPaper.S2482OrderTwoAlgAutActual
