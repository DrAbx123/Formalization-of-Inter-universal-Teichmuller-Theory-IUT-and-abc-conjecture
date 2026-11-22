/- G1-B Fermat Omega freeness on the infinity chart (mirror of OmegaFree for A1 = R2 n). -/
import tmp.sheaf.xif.paper.Mzk1G1OmegaInfinityActual
import tmp.sheaf.xif.paper.Mzk1G1FermatTransitionActual
import tmp.sheaf.xif.paper.Mzk1G1FermatSecondChartActual
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaInfinityActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaInfFreeActual

open MvPolynomial

/-- The polynomial ring in the two variables of the infinity chart. -/
abbrev Poly : Type := MvPolynomial (Fin 2) ℚ


open MvPolynomial

/-- The polynomial derivation with D(X0) = n X1^(n-1) and D(X1) = -n X0^(n-1). -/
noncomputable def dPolyInf (n : ℕ) : Derivation ℚ Poly Poly :=
  MvPolynomial.mkDerivation ℚ (fun i : Fin 2 =>
    if i = 0 then -((n : Poly) * MvPolynomial.X 1 ^ (n - 1))
    else -((n : Poly) * MvPolynomial.X 0 ^ (n - 1)))

theorem dPolyInf_X0 (n : ℕ) :
    dPolyInf n (MvPolynomial.X 0) = -((n : Poly) * MvPolynomial.X 1 ^ (n - 1)) := by
  rw [dPolyInf, MvPolynomial.mkDerivation_X]
  rfl

theorem dPolyInf_X1 (n : ℕ) :
    dPolyInf n (MvPolynomial.X 1) = -((n : Poly) * MvPolynomial.X 0 ^ (n - 1)) := by
  rw [dPolyInf, MvPolynomial.mkDerivation_X]
  rfl

/-- The derivation kills the Fermat equation. -/
theorem dPolyInf_second (n : ℕ) : dPolyInf n (secondEquation n) = 0 := by
  have h0 : dPolyInf n (MvPolynomial.X 0 ^ n) =
      -((n : Poly) * ((n : Poly) * MvPolynomial.X 0 ^ (n - 1) * MvPolynomial.X 1 ^ (n - 1))) := by
    rw [Derivation.leibniz_pow, dPolyInf_X0]
    ring
  have h1 : dPolyInf n (MvPolynomial.X 1 ^ n) =
      -((n : Poly) * ((n : Poly) * MvPolynomial.X 0 ^ (n - 1) * MvPolynomial.X 1 ^ (n - 1))) := by
    rw [Derivation.leibniz_pow, dPolyInf_X1]
    ring
  rw [secondEquation, map_sub, map_add, h0, h1, Derivation.map_one_eq_zero]
  ring

/-- The quotient ideal of the affine chart. -/
abbrev I2 (n : ℕ) : Ideal Poly := Ideal.span ({secondEquation n} : Set Poly)

/-- The polynomial derivation kills the quotient ideal. -/
theorem dPolyInf_kills_ideal (n : ℕ) :
    ∀ x : Poly, Ideal.Quotient.mk (I2 n) x = 0 → Ideal.Quotient.mk (I2 n) (dPolyInf n x) = 0 := by
  intro x hx
  rw [Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hx
  have hmem : secondEquation n ∈ I2 n := Ideal.subset_span (by simp)
  have hleib : dPolyInf n (secondEquation n * c) =
      secondEquation n * dPolyInf n c + c * dPolyInf n (secondEquation n) := by
    rw [Derivation.leibniz]
    rfl
  rw [hleib, dPolyInf_second, mul_zero, add_zero]
  exact Ideal.mul_mem_right (dPolyInf n c) (I2 n) hmem

/-- The structure map Poly -> B, as an algebra homomorphism over Q. -/
def chartHomInf (n : ℕ) : Poly →ₐ[ℚ] R2 n :=
  IsScalarTower.toAlgHom ℚ Poly (R2 n)

theorem chartHomInf_apply (n : ℕ) (x : Poly) : chartHomInf n x = Ideal.Quotient.mk (I2 n) x := by
  rw [chartHomInf, IsScalarTower.toAlgHom_apply]
  rfl

theorem chartHomInf_surjective (n : ℕ) : Function.Surjective (chartHomInf n) := by
  intro b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := I2 n) b
  exact ⟨a, chartHomInf_apply n a⟩

theorem chartHomInf_kills (n : ℕ) :
    ∀ x : Poly, chartHomInf n x = 0 → chartHomInf n (dPolyInf n x) = 0 := by
  intro x hx
  rw [chartHomInf_apply] at hx ⊢
  exact dPolyInf_kills_ideal n x hx

/-- The explicit derivation of the affine chart ring with DInf(x)=n y^(n-1), DInf(y)=-n x^(n-1). -/
noncomputable def DInf (n : ℕ) : Derivation ℚ (R2 n) (R2 n) :=
  Derivation.liftOfSurjective (f := chartHomInf n) (chartHomInf_surjective n) (chartHomInf_kills n)

theorem DInf_chartHomInf (n : ℕ) (a : Poly) :
    DInf n (chartHomInf n a) = chartHomInf n (dPolyInf n a) :=
  Derivation.liftOfSurjective_apply (f := chartHomInf n) (d := dPolyInf n)
    (chartHomInf_surjective n) (chartHomInf_kills n) a

theorem DInf_s (n : ℕ) : DInf n (infinityS n) = -((n : R2 n) * infinityR n ^ (n - 1)) := by
  have hx : infinityS n = chartHomInf n (MvPolynomial.X 0) := (chartHomInf_apply n _).symm
  have hy : infinityR n = chartHomInf n (MvPolynomial.X 1) := (chartHomInf_apply n _).symm
  rw [hx, hy, DInf_chartHomInf, dPolyInf_X0]
  simp [map_mul, map_pow, map_natCast, map_neg]

theorem DInf_r (n : ℕ) : DInf n (infinityR n) = -((n : R2 n) * infinityS n ^ (n - 1)) := by
  have hx : infinityS n = chartHomInf n (MvPolynomial.X 0) := (chartHomInf_apply n _).symm
  have hy : infinityR n = chartHomInf n (MvPolynomial.X 1) := (chartHomInf_apply n _).symm
  rw [hy, hx, DInf_chartHomInf, dPolyInf_X1]
  simp [map_mul, map_pow, map_natCast]

/-- The dual linear map Omega -> A0 associated with DInf. -/
noncomputable def PsiInf (n : ℕ) : OmegaInf n →ₗ[R2 n] R2 n :=
  (DInf n).liftKaehlerDifferential

theorem PsiInf_dS (n : ℕ) : PsiInf n (dS n) = -((n : R2 n) * infinityR n ^ (n - 1)) := by
  rw [PsiInf, dS, Derivation.liftKaehlerDifferential_comp_D, DInf_s]

theorem PsiInf_dR (n : ℕ) : PsiInf n (dR n) = -((n : R2 n) * infinityS n ^ (n - 1)) := by
  rw [PsiInf, dR, Derivation.liftKaehlerDifferential_comp_D, DInf_r]

#print axioms dPolyInf_second
#print axioms dPolyInf_kills_ideal
#print axioms DInf_s
#print axioms PsiInf_dS

/-- The Euler form is dual to n under DInf: PsiInf(omegaInfForm) = n. -/
theorem PsiInf_omegaInfForm (n : ℕ) (hn : 1 ≤ n) : PsiInf n (omegaInfForm n) = (n : R2 n) := by
  have hsum := sum_eq_one_inf n
  have hs : infinityS n * (-((n : R2 n) * infinityS n ^ (n - 1))) =
      -((n : R2 n) * infinityS n ^ n) := by
    have hp : infinityS n * infinityS n ^ (n - 1) = infinityS n ^ n := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    rw [show infinityS n * (-((n : R2 n) * infinityS n ^ (n - 1))) =
        -((n : R2 n) * (infinityS n * infinityS n ^ (n - 1))) by ring, hp]
  have hr : infinityR n * (-((n : R2 n) * infinityR n ^ (n - 1))) =
      -((n : R2 n) * infinityR n ^ n) := by
    have hp : infinityR n * infinityR n ^ (n - 1) = infinityR n ^ n := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    rw [show infinityR n * (-((n : R2 n) * infinityR n ^ (n - 1))) =
        -((n : R2 n) * (infinityR n * infinityR n ^ (n - 1))) by ring, hp]
  rw [omegaInfForm, map_sub, map_smul, map_smul, PsiInf_dR, PsiInf_dS,
    smul_eq_mul, smul_eq_mul, hs, hr]
  rw [show -((n : R2 n) * infinityS n ^ n) - -((n : R2 n) * infinityR n ^ n) =
      (n : R2 n) * (infinityR n ^ n - infinityS n ^ n) by ring]
  rw [hsum, mul_one]

/-- The candidate isomorphism A0 -> Omega, a |-> a omega. -/
noncomputable def PhiInf (n : ℕ) : R2 n →ₗ[R2 n] OmegaInf n :=
  LinearMap.toSpanSingleton (R2 n) (OmegaInf n) (omegaInfForm n)

theorem PhiInf_apply (n : ℕ) (a : R2 n) : PhiInf n a = a • omegaInfForm n := rfl

/-- The composite PsiInf o PhiInf is multiplication by n. -/
theorem PsiInf_comp_PhiInf (n : ℕ) (hn : 1 ≤ n) (a : R2 n) :
    PsiInf n (PhiInf n a) = a * (n : R2 n) := by
  rw [PhiInf_apply, map_smul, PsiInf_omegaInfForm n hn, smul_eq_mul]

theorem PhiInf_injective (n : ℕ) (hn : 1 ≤ n) : Function.Injective (PhiInf n) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hu : IsUnit (n : R2 n) := natCast_isUnit_inf n hn
  have h : a * (n : R2 n) = 0 := by
    rw [← PsiInf_comp_PhiInf n hn a, ha, map_zero]
  have huval : ((↑((natCast_isUnit_inf n hn).unit)) : R2 n) = (n : R2 n) :=
    (natCast_isUnit_inf n hn).unit_spec
  have hinv : ((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) *
      ((↑((natCast_isUnit_inf n hn).unit)) : R2 n) = 1 := (natCast_isUnit_inf n hn).val_inv_mul
  calc a = a * 1 := (mul_one a).symm
    _ = a * (((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) *
          ((↑((natCast_isUnit_inf n hn).unit)) : R2 n)) := by rw [hinv]
    _ = (a * (n : R2 n)) * ((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) := by
          rw [huval]; ring
    _ = 0 := by rw [h, zero_mul]

/-- Omega_{A0/k} is generated by dx and dy. -/
theorem span_dS_dR (n : ℕ) : Submodule.span (R2 n) ({dS n, dR n} : Set (OmegaInf n)) = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation]
  rw [Submodule.span_le]
  rintro _ ⟨b, rfl⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span ({secondEquation n} : Set Poly)) b
  have hmap : KaehlerDifferential.D ℚ (R2 n)
        (Ideal.Quotient.mk (Ideal.span ({secondEquation n} : Set Poly)) a) =
      KaehlerDifferential.map ℚ ℚ Poly (R2 n) (KaehlerDifferential.D ℚ Poly a) := by
    rw [KaehlerDifferential.map_D]; rfl
  rw [hmap]
  have hb : KaehlerDifferential.D ℚ Poly a ∈
      Submodule.span Poly (Set.range (KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2))) := by
    rw [Module.Basis.span_eq]; exact Submodule.mem_top
  have hmem := Submodule.mem_map_of_mem (f := KaehlerDifferential.map ℚ ℚ Poly (R2 n)) hb
  rw [Submodule.map_span] at hmem
  have h0 : (KaehlerDifferential.map ℚ ℚ Poly (R2 n))
        (KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2) 0) ∈
      Submodule.span (R2 n) ({dS n, dR n} : Set (OmegaInf n)) := by
    rw [KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
    have hx : (KaehlerDifferential.D ℚ (R2 n)) (algebraMap Poly (R2 n) (MvPolynomial.X 0)) = dS n := by
      rw [dS, infinityS]
      rfl
    rw [hx]
    exact Submodule.subset_span (by simp)
  have h1 : (KaehlerDifferential.map ℚ ℚ Poly (R2 n))
        (KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2) 1) ∈
      Submodule.span (R2 n) ({dS n, dR n} : Set (OmegaInf n)) := by
    rw [KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
    have hy : (KaehlerDifferential.D ℚ (R2 n)) (algebraMap Poly (R2 n) (MvPolynomial.X 1)) = dR n := by
      rw [dR, infinityR]
      rfl
    rw [hy]
    exact Submodule.subset_span (by simp)
  have hle : Submodule.span Poly
        ((KaehlerDifferential.map ℚ ℚ Poly (R2 n)) ''
          Set.range (KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2))) ≤
      (Submodule.span (R2 n) ({dS n, dR n} : Set (OmegaInf n))).restrictScalars Poly := by
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j, hj⟩ := hi
    rw [← hj]
    fin_cases j
    · exact h0
    · exact h1
  exact hle hmem

/-- PhiInf o PsiInf is multiplication by n on OmegaInf (checked on the two generators). -/
theorem PhiInf_comp_PsiInf (n : ℕ) (hn : 1 ≤ n) :
    ∀ z : OmegaInf n, PhiInf n (PsiInf n z) = (n : R2 n) • z := by
  intro z
  have h : ∀ y ∈ Submodule.span (R2 n) ({dS n, dR n} : Set (OmegaInf n)),
      PhiInf n (PsiInf n y) = (n : R2 n) • y := by
    intro y hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rw [PsiInf_dS, PhiInf_apply, neg_smul, n_r_pow_smul_omegaInf n hn, neg_neg]
      · rw [PsiInf_dR, PhiInf_apply, neg_smul, n_s_pow_smul_omegaInf n hn, neg_neg]
    · rw [map_zero, map_zero, smul_zero]
    · intro x y hx hy hx' hy'
      rw [map_add, map_add, hx', hy', smul_add]
    · intro a x hx hx'
      rw [map_smul, map_smul, hx']
      exact smul_comm a (n : R2 n) x
  have hz : z ∈ Submodule.span (R2 n) ({dS n, dR n} : Set (OmegaInf n)) := by
    rw [span_dS_dR n]; exact Submodule.mem_top
  exact h z hz

theorem PhiInf_surjective (n : ℕ) (hn : 1 ≤ n) : Function.Surjective (PhiInf n) := by
  intro z
  have hinv : ((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) * (n : R2 n) = 1 := by
    simpa [((natCast_isUnit_inf n hn).unit_spec)] using (natCast_isUnit_inf n hn).val_inv_mul
  refine ⟨((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) • PsiInf n z, ?_⟩
  rw [map_smul, PhiInf_comp_PsiInf n hn]
  calc ((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) • ((n : R2 n) • z)
      = (((↑((natCast_isUnit_inf n hn).unit)⁻¹) : R2 n) * (n : R2 n)) • z := by rw [smul_smul]
    _ = (1 : R2 n) • z := by rw [hinv]
    _ = z := one_smul _ _

/-- Omega_{A0/k} is free of rank one, generated by omegaInfForm = y dx - x dy. -/
noncomputable def phiInfEquiv (n : ℕ) (hn : 1 ≤ n) : R2 n ≃ₗ[R2 n] OmegaInf n :=
  LinearEquiv.ofBijective (PhiInf n) ⟨PhiInf_injective n hn, PhiInf_surjective n hn⟩

noncomputable def omegaInfEquivO (n : ℕ) (hn : 1 ≤ n) : OmegaInf n ≃ₗ[R2 n] R2 n :=
  (phiInfEquiv n hn).symm

theorem omegaInfEquivO_omegaInfForm (n : ℕ) (hn : 1 ≤ n) : omegaInfEquivO n hn (omegaInfForm n) = 1 := by
  have hPhiInf : phiInfEquiv n hn 1 = omegaInfForm n := by
    rw [phiInfEquiv, LinearEquiv.ofBijective_apply, PhiInf_apply, one_smul]
  rw [omegaInfEquivO, ← hPhiInf, LinearEquiv.symm_apply_apply]

theorem omegaInfForm_is_basis (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : OmegaInf n ≃ₗ[R2 n] R2 n, e (omegaInfForm n) = 1 :=
  ⟨omegaInfEquivO n hn, omegaInfEquivO_omegaInfForm n hn⟩

#print axioms PsiInf_omegaInfForm
#print axioms PsiInf_comp_PhiInf
#print axioms PhiInf_injective
#print axioms span_dS_dR
#print axioms omegaInfForm_is_basis

end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaInfFreeActual
