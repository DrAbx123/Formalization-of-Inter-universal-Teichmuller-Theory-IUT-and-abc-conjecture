/- G1-B Fermat Omega presentation actual: quotient-ring presentation (rev 2)
Omega_{A0/k} = B^2 / (n x^(n-1) dx + n y^(n-1) dy) (route §3.1, (A4) input). -/
import tmp.sheaf.xif.paper.Mzk1G1OmegaActual
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1OmegaActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1OmegaPresentationActual

open TensorProduct
open Module
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual

/-- The multivar polynomial ring basis of Omega_{k[X0,X1]/k}. -/
noncomputable def omBasis : Basis (Fin 2) Poly (KaehlerDifferential ℚ Poly) :=
  KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2)

/-- Base change of the multivar differential basis to the chart ring B. -/
noncomputable def omEquiv (n : ℕ) :
    B n ⊗[Poly] KaehlerDifferential ℚ Poly ≃ₗ[B n] (Fin 2 →₀ B n) :=
  (omBasis.baseChange (B n)).equivFun

/-- The single differential relation vector n x^(n-1) dx + n y^(n-1) dy in B^2. -/
def relVec (n : ℕ) : Fin 2 →₀ B n :=
  Finsupp.single 0 ((n : B n) * coordX n ^ (n - 1)) +
    Finsupp.single 1 ((n : B n) * coordY n ^ (n - 1))

/-- The same relation in the base-changed polynomial differentials. -/
noncomputable def relTensor (n : ℕ) : B n ⊗[Poly] KaehlerDifferential ℚ Poly :=
  (1 : B n) ⊗ₜ[Poly] KaehlerDifferential.D ℚ Poly (fermatEquation n)

/-- The quotient-ring presentation of Omega_{A0/k}. -/
def Pres (n : ℕ) : Type :=
  (Fin 2 →₀ B n) ⧸ Submodule.span (B n) ({relVec n} : Set (Fin 2 →₀ B n))

theorem pderiv_fermat_zero (n : ℕ) :
    MvPolynomial.pderiv 0 (fermatEquation n) = (n : Poly) * MvPolynomial.X 0 ^ (n - 1) := by
  simp [fermatEquation, MvPolynomial.pderiv_pow]

theorem pderiv_fermat_one (n : ℕ) :
    MvPolynomial.pderiv 1 (fermatEquation n) = (n : Poly) * MvPolynomial.X 1 ^ (n - 1) := by
  simp [fermatEquation, MvPolynomial.pderiv_pow]

theorem omEquiv_tmul_basis (n : ℕ) (i : Fin 2) :
    omEquiv n ((1 : B n) ⊗ₜ[Poly] omBasis i) = Finsupp.single i (1 : B n) := by
  rw [omEquiv, Basis.equivFun_apply, ← Basis.baseChange_apply, Basis.repr_self]

theorem omEquiv_relTensor (n : ℕ) : omEquiv n (relTensor n) = relVec n := by
  ext i
  rw [omEquiv, Basis.equivFun_apply, relTensor, Basis.baseChange_repr_tmul,
    KaehlerDifferential.mvPolynomialBasis_repr_apply]
  fin_cases i
  · simp [relVec, pderiv_fermat_zero, coordX, Algebra.smul_def, map_mul, map_pow, map_natCast]
  · simp [relVec, pderiv_fermat_one, coordY, Algebra.smul_def, map_mul, map_pow, map_natCast]

/-- The image of the conormal map as a B-submodule. -/
noncomputable def conormalRange (n : ℕ) :
    Submodule (B n) (B n ⊗[Poly] KaehlerDifferential ℚ Poly) where
  carrier := Set.range (KaehlerDifferential.kerCotangentToTensor ℚ Poly (B n))
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ x y⟩
  smul_mem' := by
    rintro b _ ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨a • x, ?_⟩
    rw [map_smul, IsScalarTower.algebraMap_smul]

theorem conormalRange_eq_span (n : ℕ) :
    conormalRange n =
      Submodule.span (B n) ({relTensor n} : Set (B n ⊗[Poly] KaehlerDifferential ℚ Poly)) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective (Ideal.span ({fermatEquation n} : Set Poly)) x
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp a.2
    have ha : a = c • (⟨fermatEquation n, Ideal.subset_span (by simp)⟩ :
        Ideal.span ({fermatEquation n} : Set Poly)) := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, smul_eq_mul]
      rw [mul_comm c (fermatEquation n)]
      exact hc
    rw [ha, map_smul]
    rw [show KaehlerDifferential.kerCotangentToTensor ℚ Poly (B n)
        (Ideal.toCotangent _ ⟨fermatEquation n, Ideal.subset_span (by simp)⟩) = relTensor n by
      rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]; rfl]
    rw [← IsScalarTower.algebraMap_smul c (relTensor n)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le]
    rintro _ rfl
    exact ⟨Ideal.toCotangent _ ⟨fermatEquation n, Ideal.subset_span (by simp)⟩, by
      rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]; rfl⟩

/-- Kernel of the base-changed differential map: the conormal relation. -/
theorem ker_mapBaseChange_eq (n : ℕ) :
    LinearMap.ker (KaehlerDifferential.mapBaseChange ℚ Poly (B n)) =
      Submodule.span (B n) ({relTensor n} : Set (B n ⊗[Poly] KaehlerDifferential ℚ Poly)) := by
  have hsurj : Function.Surjective (algebraMap Poly (B n)) := Ideal.Quotient.mk_surjective
  have hexact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
    (R := ℚ) (A := Poly) (B := B n) hsurj
  apply SetLike.ext
  intro y
  rw [LinearMap.mem_ker, hexact y, ← conormalRange_eq_span n]
  rfl

/-- The presentation map through the base-changed differential basis. -/
noncomputable def presMapB (n : ℕ) : (Fin 2 →₀ B n) →ₗ[B n] Omega n :=
  (KaehlerDifferential.mapBaseChange ℚ Poly (B n)).comp (omEquiv n).symm.toLinearMap

theorem presMapB_single (n : ℕ) (i : Fin 2) (a : B n) :
    presMapB n (Finsupp.single i a) = a • (if i = 0 then dX n else dY n) := by
  have hsingle : Finsupp.single i a = a • Finsupp.single i (1 : B n) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [presMapB, LinearMap.comp_apply, hsingle, map_smul]
  congr 1
  have h : (omEquiv n).symm (Finsupp.single i (1 : B n)) = (1 : B n) ⊗ₜ[Poly] omBasis i := by
    rw [← omEquiv_tmul_basis n i]
    exact (omEquiv n).symm_apply_apply _
  rw [h, KaehlerDifferential.mapBaseChange_tmul, one_smul, omBasis,
    KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]
  fin_cases i
  · simp [dX, dY, coordX, coordY]
  · simp [dX, dY, coordX, coordY]

theorem presMap_eq_presMapB (n : ℕ) : presMap n = presMapB n := by
  apply Finsupp.lhom_ext
  intro i a
  rw [presMapB_single, presMap, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

theorem presMapB_surjective (n : ℕ) : Function.Surjective (presMapB n) :=
  (KaehlerDifferential.mapBaseChange_surjective (Ideal.Quotient.mk_surjective)).comp
    (omEquiv n).symm.surjective

theorem presMapB_relVec (n : ℕ) : presMapB n (relVec n) = 0 := by
  rw [relVec, map_add, presMapB_single, presMapB_single]
  rw [if_pos rfl, if_neg (by decide : ¬((1 : Fin 2) = 0))]
  exact derivation_relation n

/-- Kernel of the presentation map is exactly the single quotient-ring relation. -/
theorem ker_presMapB (n : ℕ) :
    LinearMap.ker (presMapB n) = Submodule.span (B n) ({relVec n} : Set (Fin 2 →₀ B n)) := by
  rw [presMapB, LinearMap.ker_comp, ker_mapBaseChange_eq]
  ext x
  rw [Submodule.mem_comap]
  constructor
  · intro hx
    have hmap : omEquiv n ((omEquiv n).symm x) ∈ Submodule.map (omEquiv n).toLinearMap
        (Submodule.span (B n) ({relTensor n} : Set (B n ⊗[Poly] KaehlerDifferential ℚ Poly))) :=
      Submodule.mem_map.mpr ⟨(omEquiv n).symm x, hx, rfl⟩
    rw [Submodule.map_span, Set.image_singleton, omEquiv_relTensor n,
      (omEquiv n).apply_symm_apply x] at hmap
    exact hmap
  · intro hx
    have hmap : (omEquiv n).symm x ∈ Submodule.map (omEquiv n).symm.toLinearMap
        (Submodule.span (B n) ({relVec n} : Set (Fin 2 →₀ B n))) :=
      Submodule.mem_map.mpr ⟨x, hx, rfl⟩
    rw [Submodule.map_span, Set.image_singleton] at hmap
    rw [omEquiv_relTensor n, (omEquiv n).symm_apply_apply] at hmap
    exact hmap

/-- The presentation map from the quotient-ring presentation to Omega. -/
noncomputable def presToOmega (n : ℕ) : Pres n →ₗ[B n] Omega n :=
  (Submodule.span (B n) ({relVec n} : Set (Fin 2 →₀ B n))).liftQ (presMapB n) (by
    rw [Submodule.span_le]
    rintro _ rfl
    rw [LinearMap.mem_ker]
    exact presMapB_relVec n)

theorem presToOmega_mk (n : ℕ) (x : Fin 2 →₀ B n) :
    presToOmega n (Submodule.Quotient.mk x) = presMapB n x :=
  Submodule.liftQ_apply _ x

theorem presToOmega_injective (n : ℕ) : Function.Injective (presToOmega n) := by
  rw [← LinearMap.ker_eq_bot]
  rw [presToOmega]
  exact Submodule.ker_liftQ_eq_bot (presMapB n) _ (by rw [ker_presMapB n])

theorem presToOmega_surjective (n : ℕ) : Function.Surjective (presToOmega n) := by
  intro z
  obtain ⟨x, rfl⟩ := presMapB_surjective n z
  exact ⟨Submodule.Quotient.mk x, presToOmega_mk n x⟩

/-- The quotient-ring presentation of Omega_{A0/k}. -/
noncomputable def omegaEquivPres (n : ℕ) : Omega n ≃ₗ[B n] Pres n :=
  (LinearEquiv.ofBijective (presToOmega n)
    ⟨presToOmega_injective n, presToOmega_surjective n⟩).symm

end LeanFormal.IUT.XiFPaper.Mzk1G1OmegaPresentationActual
