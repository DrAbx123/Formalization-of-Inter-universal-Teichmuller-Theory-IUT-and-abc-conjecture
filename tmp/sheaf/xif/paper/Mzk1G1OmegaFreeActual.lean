/- G1-B Fermat Omega freeness actual (rev 2): the explicit derivation D0 of the affine chart
(A0): D0(x) = n y^(n-1), D0(y) = -n x^(n-1), and the associated dual map Omega -> A0.
This is the key input for Omega_{A0/k} ~ O (route §3.1, (A4) local triviality). -/
import tmp.sheaf.xif.paper.Mzk1G1OmegaActual
import tmp.sheaf.xif.paper.Mzk1G1OmegaBasisActual
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaFreeActual

open MvPolynomial

/-- The polynomial derivation with D(X0) = n X1^(n-1) and D(X1) = -n X0^(n-1). -/
noncomputable def dPoly (n : ℕ) : Derivation ℚ Poly Poly :=
  MvPolynomial.mkDerivation ℚ (fun i : Fin 2 =>
    if i = 0 then (n : Poly) * MvPolynomial.X 1 ^ (n - 1) else -((n : Poly) * MvPolynomial.X 0 ^ (n - 1)))

theorem dPoly_X0 (n : ℕ) :
    dPoly n (MvPolynomial.X 0) = (n : Poly) * MvPolynomial.X 1 ^ (n - 1) := by
  rw [dPoly, MvPolynomial.mkDerivation_X]
  rfl

theorem dPoly_X1 (n : ℕ) :
    dPoly n (MvPolynomial.X 1) = -((n : Poly) * MvPolynomial.X 0 ^ (n - 1)) := by
  rw [dPoly, MvPolynomial.mkDerivation_X]
  rfl

/-- The derivation kills the Fermat equation. -/
theorem dPoly_fermat (n : ℕ) : dPoly n (fermatEquation n) = 0 := by
  have h0 : dPoly n (MvPolynomial.X 0 ^ n) =
      (n : Poly) * ((n : Poly) * MvPolynomial.X 0 ^ (n - 1) * MvPolynomial.X 1 ^ (n - 1)) := by
    rw [Derivation.leibniz_pow, dPoly_X0]
    ring
  have h1 : dPoly n (MvPolynomial.X 1 ^ n) =
      -((n : Poly) * ((n : Poly) * MvPolynomial.X 0 ^ (n - 1) * MvPolynomial.X 1 ^ (n - 1))) := by
    rw [Derivation.leibniz_pow, dPoly_X1]
    ring
  rw [fermatEquation, map_sub, map_add, h0, h1, Derivation.map_one_eq_zero]
  ring

/-- The quotient ideal of the affine chart. -/
abbrev I (n : ℕ) : Ideal Poly := Ideal.span ({fermatEquation n} : Set Poly)

/-- The polynomial derivation kills the quotient ideal. -/
theorem dPoly_kills_ideal (n : ℕ) :
    ∀ x : Poly, Ideal.Quotient.mk (I n) x = 0 → Ideal.Quotient.mk (I n) (dPoly n x) = 0 := by
  intro x hx
  rw [Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
  have hmem : fermatEquation n ∈ I n := Ideal.subset_span (by simp)
  have hleib : dPoly n (fermatEquation n * c) =
      fermatEquation n * dPoly n c + c * dPoly n (fermatEquation n) := by
    rw [Derivation.leibniz]
    rfl
  rw [hleib, dPoly_fermat, mul_zero, add_zero]
  exact Ideal.mul_mem_right (dPoly n c) (I n) hmem

/-- The structure map Poly -> B, as an algebra homomorphism over Q. -/
def chartHom (n : ℕ) : Poly →ₐ[ℚ] B n :=
  IsScalarTower.toAlgHom ℚ Poly (B n)

theorem chartHom_apply (n : ℕ) (x : Poly) : chartHom n x = Ideal.Quotient.mk (I n) x := by
  rw [chartHom, IsScalarTower.toAlgHom_apply]
  rfl

theorem chartHom_surjective (n : ℕ) : Function.Surjective (chartHom n) := by
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I n) b
  exact ⟨a, chartHom_apply n a⟩

theorem chartHom_kills (n : ℕ) :
    ∀ x : Poly, chartHom n x = 0 → chartHom n (dPoly n x) = 0 := by
  intro x hx
  rw [chartHom_apply] at hx ⊢
  exact dPoly_kills_ideal n x hx

/-- The explicit derivation of the affine chart ring with D0(x)=n y^(n-1), D0(y)=-n x^(n-1). -/
noncomputable def D0 (n : ℕ) : Derivation ℚ (B n) (B n) :=
  Derivation.liftOfSurjective (f := chartHom n) (chartHom_surjective n) (chartHom_kills n)

theorem D0_chartHom (n : ℕ) (a : Poly) :
    D0 n (chartHom n a) = chartHom n (dPoly n a) :=
  Derivation.liftOfSurjective_apply (f := chartHom n) (d := dPoly n)
    (chartHom_surjective n) (chartHom_kills n) a

theorem D0_x0 (n : ℕ) : D0 n (coordX n) = (n : B n) * coordY n ^ (n - 1) := by
  have hx : coordX n = chartHom n (MvPolynomial.X 0) := (chartHom_apply n _).symm
  have hy : coordY n = chartHom n (MvPolynomial.X 1) := (chartHom_apply n _).symm
  rw [hx, hy, D0_chartHom, dPoly_X0]
  simp [map_mul, map_pow, map_natCast]

theorem D0_x1 (n : ℕ) : D0 n (coordY n) = -((n : B n) * coordX n ^ (n - 1)) := by
  have hx : coordX n = chartHom n (MvPolynomial.X 0) := (chartHom_apply n _).symm
  have hy : coordY n = chartHom n (MvPolynomial.X 1) := (chartHom_apply n _).symm
  rw [hy, hx, D0_chartHom, dPoly_X1]
  simp [map_mul, map_pow, map_natCast]

/-- The dual linear map Omega -> A0 associated with D0. -/
noncomputable def Psi (n : ℕ) : Omega n →ₗ[B n] B n :=
  (D0 n).liftKaehlerDifferential

theorem Psi_dX (n : ℕ) : Psi n (dX n) = (n : B n) * coordY n ^ (n - 1) := by
  rw [Psi, dX, Derivation.liftKaehlerDifferential_comp_D, D0_x0]

theorem Psi_dY (n : ℕ) : Psi n (dY n) = -((n : B n) * coordX n ^ (n - 1)) := by
  rw [Psi, dY, Derivation.liftKaehlerDifferential_comp_D, D0_x1]

#print axioms dPoly_fermat
#print axioms dPoly_kills_ideal
#print axioms D0_x0
#print axioms Psi_dX

open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaBasisActual

/-- The Euler form is dual to n under D0: Psi(omegaForm) = n. -/
theorem Psi_omegaForm (n : ℕ) (hn : 1 ≤ n) : Psi n (omegaForm n) = (n : B n) := by
  have hsum : coordY n ^ n + coordX n ^ n = (1 : B n) := by
    have h : coordX n ^ n + coordY n ^ n = 1 := sub_eq_zero.mp (relation n)
    rw [add_comm]; exact h
  have hy : coordY n * ((n : B n) * coordY n ^ (n - 1)) = (n : B n) * coordY n ^ n := by
    rw [show coordY n ^ n = coordY n * coordY n ^ (n - 1) from by
      rw [← pow_succ', Nat.sub_add_cancel hn]]
    ring
  have hx : coordX n * ((n : B n) * coordX n ^ (n - 1)) = (n : B n) * coordX n ^ n := by
    rw [show coordX n ^ n = coordX n * coordX n ^ (n - 1) from by
      rw [← pow_succ', Nat.sub_add_cancel hn]]
    ring
  rw [omegaForm, map_sub, map_smul, map_smul, Psi_dX, Psi_dY, smul_neg, smul_eq_mul,
    smul_eq_mul, hy, hx, sub_neg_eq_add, ← mul_add, hsum, mul_one]

/-- The candidate isomorphism A0 -> Omega, a |-> a omega. -/
noncomputable def Phi (n : ℕ) : B n →ₗ[B n] Omega n :=
  LinearMap.toSpanSingleton (B n) (Omega n) (omegaForm n)

theorem Phi_apply (n : ℕ) (a : B n) : Phi n a = a • omegaForm n := rfl

/-- The composite Psi o Phi is multiplication by n. -/
theorem Psi_comp_Phi (n : ℕ) (hn : 1 ≤ n) (a : B n) :
    Psi n (Phi n a) = a * (n : B n) := by
  rw [Phi_apply, map_smul, Psi_omegaForm n hn, smul_eq_mul]

theorem Phi_injective (n : ℕ) (hn : 1 ≤ n) : Function.Injective (Phi n) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hu : IsUnit (n : B n) := natCast_isUnit n hn
  have h : a * (n : B n) = 0 := by
    rw [← Psi_comp_Phi n hn a, ha, map_zero]
  have huval : ((↑((natCast_isUnit n hn).unit)) : B n) = (n : B n) :=
    (natCast_isUnit n hn).unit_spec
  have hinv : ((↑((natCast_isUnit n hn).unit)⁻¹) : B n) *
      ((↑((natCast_isUnit n hn).unit)) : B n) = 1 := (natCast_isUnit n hn).val_inv_mul
  calc a = a * 1 := (mul_one a).symm
    _ = a * (((↑((natCast_isUnit n hn).unit)⁻¹) : B n) *
          ((↑((natCast_isUnit n hn).unit)) : B n)) := by rw [hinv]
    _ = (a * (n : B n)) * ((↑((natCast_isUnit n hn).unit)⁻¹) : B n) := by
          rw [huval]; ring
    _ = 0 := by rw [h, zero_mul]

theorem dX_mem_range_Phi (n : ℕ) (hn : 1 ≤ n) : dX n ∈ LinearMap.range (Phi n) := by
  refine ⟨coordY n ^ (n - 1), ?_⟩
  rw [Phi_apply]
  exact y_pow_smul_omegaForm n hn

theorem dY_mem_range_Phi (n : ℕ) (hn : 1 ≤ n) : dY n ∈ LinearMap.range (Phi n) := by
  refine ⟨-((coordX n ^ (n - 1))), ?_⟩
  rw [Phi_apply, neg_smul, x_pow_smul_omegaForm n hn, neg_neg]

/-- Omega_{A0/k} is generated by dx and dy. -/
theorem span_dX_dY (n : ℕ) : Submodule.span (B n) ({dX n, dY n} : Set (Omega n)) = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation]
  rw [Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span ({fermatEquation n} : Set Poly)) b
  have hmap : KaehlerDifferential.D ℚ (B n)
        (Ideal.Quotient.mk (Ideal.span ({fermatEquation n} : Set Poly)) a) =
      KaehlerDifferential.map ℚ ℚ Poly (B n) (KaehlerDifferential.D ℚ Poly a) := by
    rw [KaehlerDifferential.map_D]; rfl
  rw [hmap]
  have hb : KaehlerDifferential.D ℚ Poly a ∈
      Submodule.span Poly (Set.range (KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2))) := by
    rw [Module.Basis.span_eq]; exact Submodule.mem_top
  have hmem := Submodule.mem_map_of_mem (f := KaehlerDifferential.map ℚ ℚ Poly (B n)) hb
  rw [Submodule.map_span] at hmem
  have h0 : (KaehlerDifferential.map ℚ ℚ Poly (B n))
        (KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2) 0) ∈
      Submodule.span (B n) ({dX n, dY n} : Set (Omega n)) := by
    rw [KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
    have hx : (KaehlerDifferential.D ℚ (B n)) (algebraMap Poly (B n) (MvPolynomial.X 0)) = dX n := by
      rw [dX, coordX]
      rfl
    rw [hx]
    exact Submodule.subset_span (by simp)
  have h1 : (KaehlerDifferential.map ℚ ℚ Poly (B n))
        (KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2) 1) ∈
      Submodule.span (B n) ({dX n, dY n} : Set (Omega n)) := by
    rw [KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
    have hy : (KaehlerDifferential.D ℚ (B n)) (algebraMap Poly (B n) (MvPolynomial.X 1)) = dY n := by
      rw [dY, coordY]
      rfl
    rw [hy]
    exact Submodule.subset_span (by simp)
  have hle : Submodule.span Poly
        ((KaehlerDifferential.map ℚ ℚ Poly (B n)) ''
          Set.range (KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2))) ≤
      (Submodule.span (B n) ({dX n, dY n} : Set (Omega n))).restrictScalars Poly := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j, hj⟩ := hi
    rw [← hj]
    fin_cases j
    · exact h0
    · exact h1
  exact hle hmem

theorem Phi_surjective (n : ℕ) (hn : 1 ≤ n) : Function.Surjective (Phi n) := by
  have hle : Submodule.span (B n) ({dX n, dY n} : Set (Omega n)) ≤ LinearMap.range (Phi n) := by
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact dX_mem_range_Phi n hn
    · exact dY_mem_range_Phi n hn
  intro z
  have hz : z ∈ Submodule.span (B n) ({dX n, dY n} : Set (Omega n)) := by
    rw [span_dX_dY n]; exact Submodule.mem_top
  exact hle hz

/-- Omega_{A0/k} is free of rank one, generated by omegaForm = y dx - x dy. -/
noncomputable def phiEquiv (n : ℕ) (hn : 1 ≤ n) : B n ≃ₗ[B n] Omega n :=
  LinearEquiv.ofBijective (Phi n) ⟨Phi_injective n hn, Phi_surjective n hn⟩

noncomputable def omegaEquivO (n : ℕ) (hn : 1 ≤ n) : Omega n ≃ₗ[B n] B n :=
  (phiEquiv n hn).symm

theorem omegaEquivO_omegaForm (n : ℕ) (hn : 1 ≤ n) : omegaEquivO n hn (omegaForm n) = 1 := by
  have hPhi : phiEquiv n hn 1 = omegaForm n := by
    rw [phiEquiv, LinearEquiv.ofBijective_apply, Phi_apply, one_smul]
  rw [omegaEquivO, ← hPhi, LinearEquiv.symm_apply_apply]

theorem omegaForm_is_basis (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : Omega n ≃ₗ[B n] B n, e (omegaForm n) = 1 :=
  ⟨omegaEquivO n hn, omegaEquivO_omegaForm n hn⟩

#print axioms Psi_omegaForm
#print axioms Psi_comp_Phi
#print axioms Phi_injective
#print axioms span_dX_dY
#print axioms omegaForm_is_basis

end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaFreeActual
