/-
# λ-chart (chartInf, the D(q) piece): finite fibres of the psi chart coordinate

This file completes the chartInf (second Fermat chart U1 = Spec (R2 n) cut out by the
principal open D(q), q = psiChartInfDenom n T = prod over t in T of (1 - t * r)) part of the
fibre-finiteness statement for the two-section map psi.

Main results:

* chartRing_finite_r : Module.Finite ℚ[t] (R2 n) for the ℚ[t]-algebra structure t ↦ r =
  chartR n (rAlgebra).  On R2 n = ℚ[s,r]/(1 + s^n - r^n) we have s^n = r^n - 1 = t^n - 1,
  so s is integral over ℚ[t]; {s, r} generates R2 n (r is the image of t), so
  Algebra.IsIntegral.finite applies.  This mirrors
  Mzk1G1FermatChartFinite2Actual.chartRing_finite2, which uses the structure t ↦ r^n.
* infPoly, infPoly_ne_zero : the polynomial prod (1 - t X) - c in ℚ[X], whose value at r
  is q - c, is nonzero when T is nonempty and 0 is not in T: it factors as C L times
  (prod (X - 1/t) - C (c/L)) with L = prod (-t) ≠ 0 and the second factor monic.
* quot_finiteDim_inf : for nonzero f in ℚ[X], R2 n modulo (f(r)) is finite-dimensional
  over ℚ (via the tower ℚ → ℚ[t] → R2 n and Polynomial.Monic.finite_quotient).
* quot_finiteDim_psiInf : the specialized statement for f = infPoly T c, i.e.
  Module.Finite ℚ (R2 n ⧸ (q - c)).
* finite_primes_of_psiChartInf : only finitely many primes of R2 n contain q - c, i.e.
  the D(q)-piece of the psi-chart has finitely many points over the value c (via the
  general finite_primes_of_finite_quotient).

Hypotheses: 0 < n (for n = 0 the second chart equation degenerates), T.Nonempty and
0 not in T.  The last hypothesis is necessary: for T = {0}, c = 1 we have q - 1 = 0, so
the quotient is R2 n itself, which is infinite-dimensional over ℚ (r is transcendental).
In the geometric application T is a set of nonzero critical values, so this is the
intended range.

No placeholders, new postulates, or toy carriers.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiFiberFiniteActual
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberFiniteInfActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiQuotientFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberFiniteActual

/-! ## 0. The ℚ[t]-algebra structure t ↦ r = chartR n on R2 n -/

/-- The λ-chart structure map ℚ[t] →+* R2 n, t ↦ r = chartR n. -/
noncomputable def rHom (n : Nat) : Polynomial ℚ →+* R2 n :=
  Polynomial.eval₂RingHom (algebraMap ℚ (R2 n)) (chartR n)

/-- The ℚ[t]-algebra structure on R2 n with t ↦ r = chartR n.
Declared as a definition (not a global instance, which would clash with the t ↦ r^n
structure used elsewhere); proofs that need it set the local instance rAlgebra n. -/
noncomputable def rAlgebra (n : Nat) : Algebra (Polynomial ℚ) (R2 n) :=
  (rHom n).toAlgebra

theorem rHom_X (n : Nat) : rHom n Polynomial.X = chartR n := by
  simp [rHom]

theorem rHom_C (n : Nat) (a : ℚ) : rHom n (Polynomial.C a) = algebraMap ℚ (R2 n) a := by
  simp [rHom]

theorem algebraMap_C_eq_inf (n : Nat) (a : ℚ) :
    letI := rAlgebra n
    algebraMap (Polynomial ℚ) (R2 n) (Polynomial.C a) = algebraMap ℚ (R2 n) a := by
  letI := rAlgebra n
  show rHom n (Polynomial.C a) = algebraMap ℚ (R2 n) a
  exact rHom_C n a

/-- Quotient representatives of rational constants. -/
theorem mk_C_eq_algebraMap_inf (n : Nat) (a : ℚ) :
    (Ideal.Quotient.mk (Ideal.span {secondEquation n}) (MvPolynomial.C a) : R2 n)
      = algebraMap ℚ (R2 n) a := by
  rw [IsScalarTower.algebraMap_apply ℚ (MvPolynomial (Fin 2) ℚ) (R2 n)]
  rw [Ideal.Quotient.algebraMap_eq]
  rw [show (algebraMap ℚ (MvPolynomial (Fin 2) ℚ) a) = MvPolynomial.C a from rfl]

#print axioms rHom_X
#print axioms rHom_C
#print axioms algebraMap_C_eq_inf
#print axioms mk_C_eq_algebraMap_inf

/-! ## 1. R2 n is finite over ℚ[t] (t ↦ r) -/

/-- s^n = r^n - 1 = t^n - 1. -/
theorem chartS_pow_eq (n : Nat) :
    letI := rAlgebra n
    chartS n ^ n = algebraMap (Polynomial ℚ) (R2 n) (Polynomial.X ^ n) - 1 := by
  letI := rAlgebra n
  have h := one_add_chartS_pow_eq_chartR_pow n
  have hr : chartR n = algebraMap (Polynomial ℚ) (R2 n) Polynomial.X := (rHom_X n).symm
  rw [hr, ← map_pow] at h
  linear_combination h

/-- s is integral over ℚ[t]: s^n = t^n - 1. -/
theorem chartS_isIntegral_r (n : Nat) (hn : 0 < n) :
    letI := rAlgebra n
    IsIntegral (Polynomial ℚ) (chartS n) := by
  letI := rAlgebra n
  have hsp := chartS_pow_eq n
  have h : IsIntegral (Polynomial ℚ) (chartS n ^ n) := by
    rw [hsp]
    exact (isIntegral_algebraMap (R := Polynomial ℚ) (A := R2 n)
      (x := Polynomial.X ^ n)).sub isIntegral_one
  exact IsIntegral.of_pow hn h

/-- r is integral over ℚ[t]: it is the image of t. -/
theorem chartR_isIntegral_r (n : Nat) :
    letI := rAlgebra n
    IsIntegral (Polynomial ℚ) (chartR n) := by
  letI := rAlgebra n
  have h : (algebraMap (Polynomial ℚ) (R2 n)) Polynomial.X = chartR n := rHom_X n
  rw [← h]
  exact isIntegral_algebraMap

/-- {s, r} generates R2 n as a ℚ[t]-algebra. -/
theorem adjoin_eq_top_r (n : Nat) :
    letI := rAlgebra n
    Algebra.adjoin (Polynomial ℚ) ({chartS n, chartR n} : Set (R2 n)) = ⊤ := by
  letI := rAlgebra n
  rw [eq_top_iff]
  intro a _
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Ideal.span {secondEquation n}) a
  have key : ∀ p : MvPolynomial (Fin 2) ℚ,
      Ideal.Quotient.mk (Ideal.span {secondEquation n}) p
        ∈ Algebra.adjoin (Polynomial ℚ) ({chartS n, chartR n} : Set (R2 n)) := by
    intro p
    refine MvPolynomial.induction_on
      (motive := fun q => Ideal.Quotient.mk (Ideal.span {secondEquation n}) q
        ∈ Algebra.adjoin (Polynomial ℚ) ({chartS n, chartR n} : Set (R2 n))) p ?_ ?_ ?_
    · intro r
      rw [mk_C_eq_algebraMap_inf, ← algebraMap_C_eq_inf n r]
      exact Subalgebra.algebraMap_mem _ _
    · intro p q hp hq
      rw [map_add]
      exact Subalgebra.add_mem _ hp hq
    · intro p i hp
      rw [map_mul]
      refine Subalgebra.mul_mem _ hp ?_
      fin_cases i
      · exact Algebra.subset_adjoin (by simp [chartS])
      · exact Algebra.subset_adjoin (by simp [chartR])
  exact key p

/-- R2 n is a finitely generated ℚ[t]-algebra (t ↦ r). -/
theorem chart_finiteType_r (n : Nat) :
    letI := rAlgebra n
    Algebra.FiniteType (Polynomial ℚ) (R2 n) := by
  letI := rAlgebra n
  classical
  refine ⟨?fg⟩
  rw [Subalgebra.fg_def]
  exact ⟨({chartS n, chartR n} : Set (R2 n)), Set.toFinite _, adjoin_eq_top_r n⟩

/-- R2 n is integral over ℚ[t] (t ↦ r). -/
theorem chart_isIntegral_r (n : Nat) (hn : 0 < n) :
    letI := rAlgebra n
    Algebra.IsIntegral (Polynomial ℚ) (R2 n) := by
  letI := rAlgebra n
  refine { isIntegral := ?_ }
  intro x
  have hmem : x ∈ Algebra.adjoin (Polynomial ℚ) ({chartS n, chartR n} : Set (R2 n)) := by
    rw [adjoin_eq_top_r n]; trivial
  exact Algebra.adjoin_induction (p := fun y _ => IsIntegral (Polynomial ℚ) y)
    (fun y hy => by
      rcases hy with rfl | rfl
      · exact chartS_isIntegral_r n hn
      · exact chartR_isIntegral_r n)
    (fun r => isIntegral_algebraMap)
    (fun y z _ _ hy hz => hy.add hz)
    (fun y z _ _ hy hz => hy.mul hz) hmem

/-- **R2 n is a finite ℚ[t]-module (t ↦ r = chartR n)**: the λ-chart version of the
finiteness of the chart map. -/
theorem chartRing_finite_r (n : Nat) (hn : 0 < n) :
    letI := rAlgebra n
    Module.Finite (Polynomial ℚ) (R2 n) := by
  letI := rAlgebra n
  haveI := chart_isIntegral_r n hn
  exact Algebra.IsIntegral.finite (R := Polynomial ℚ) (A := R2 n)
    (h' := chart_finiteType_r n)

/-- ℚ → ℚ[t] → R2 n is a scalar tower. -/
theorem isScalarTower_r (n : Nat) :
    letI := rAlgebra n
    IsScalarTower ℚ (Polynomial ℚ) (R2 n) := by
  letI := rAlgebra n
  refine IsScalarTower.of_algebraMap_eq fun q => ?_
  rw [show algebraMap (Polynomial ℚ) (R2 n) = rHom n from rfl]
  change algebraMap ℚ (R2 n) q = rHom n (Polynomial.C q)
  exact (algebraMap_C_eq_inf n q).symm

#print axioms chartS_pow_eq
#print axioms chartS_isIntegral_r
#print axioms chartR_isIntegral_r
#print axioms adjoin_eq_top_r
#print axioms chart_finiteType_r
#print axioms chart_isIntegral_r
#print axioms chartRing_finite_r
#print axioms isScalarTower_r

/-! ## 2. The polynomial prod (1 - t X) - c and its value at r -/

/-- The monic product prod (X - 1/t) in ℚ[X]. -/
noncomputable def infProdM (T : Finset ℚ) : Polynomial ℚ :=
  ∏ t ∈ T, (Polynomial.X - Polynomial.C t⁻¹)

/-- L = prod (-t), the leading coefficient of prod (1 - t X). -/
noncomputable def infScalarL (T : Finset ℚ) : ℚ := ∏ t ∈ T, (-t)

/-- prod (1 - t X) - c in ℚ[X]; its value at r is psiChartInfDenom n T - c. -/
noncomputable def infPoly (T : Finset ℚ) (c : ℚ) : Polynomial ℚ :=
  (∏ t ∈ T, (1 - Polynomial.C t * Polynomial.X)) - Polynomial.C c

theorem infProdM_monic (T : Finset ℚ) : (infProdM T).Monic := by
  rw [infProdM]
  exact Polynomial.monic_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _

theorem infProdM_natDegree (T : Finset ℚ) : (infProdM T).natDegree = T.card := by
  rw [infProdM, Polynomial.natDegree_prod_of_monic _ _
    fun t _ => Polynomial.monic_X_sub_C _]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]

/-- C L = prod C (-t). -/
theorem C_infScalarL_eq_prod (T : Finset ℚ) :
    Polynomial.C (infScalarL T) = ∏ t ∈ T, (Polynomial.C (-t) : Polynomial ℚ) := by
  rw [infScalarL]
  exact map_prod (Polynomial.C : ℚ →+* Polynomial ℚ) (fun t => -t) T

/-- 1 - t X = (-t) * (X - 1/t) for t ≠ 0. -/
theorem one_sub_C_mul_X_eq (t : ℚ) (ht : t ≠ 0) :
    (1 - Polynomial.C t * Polynomial.X : Polynomial ℚ)
      = Polynomial.C (-t) * (Polynomial.X - Polynomial.C t⁻¹) := by
  have h2 : (-t) * t⁻¹ = (-1 : ℚ) := by
    rw [neg_mul, mul_inv_cancel₀ ht]
  have h1 : (Polynomial.C (-t) : Polynomial ℚ) * Polynomial.C t⁻¹ = -1 := by
    rw [← Polynomial.C_mul, h2, Polynomial.C_neg, Polynomial.C_1]
  have hsplit : Polynomial.C (-t) * (Polynomial.X - Polynomial.C t⁻¹)
      = Polynomial.C (-t) * Polynomial.X - Polynomial.C (-t) * Polynomial.C t⁻¹ := by
    ring
  rw [hsplit, h1, Polynomial.C_neg]
  ring

/-- L * prod (X - 1/t) = prod (1 - t X). -/
theorem infPoly_factor (T : Finset ℚ) (h0 : 0 ∉ T) :
    Polynomial.C (infScalarL T) * infProdM T
      = ∏ t ∈ T, (1 - Polynomial.C t * Polynomial.X) := by
  rw [C_infScalarL_eq_prod, infProdM, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun t ht =>
    (one_sub_C_mul_X_eq t (by rintro rfl; exact h0 ht)).symm

theorem infScalarL_ne_zero (T : Finset ℚ) (h0 : 0 ∉ T) : infScalarL T ≠ 0 := by
  rw [infScalarL, Finset.prod_ne_zero_iff]
  intro t ht
  exact neg_ne_zero.mpr (by rintro rfl; exact h0 ht)

/-- **The polynomial prod (1 - t X) - c is nonzero** for T nonempty and 0 not in T:
it is C L times the monic polynomial prod (X - 1/t) - C (c/L). -/
theorem infPoly_ne_zero (T : Finset ℚ) (hT : T.Nonempty) (h0 : 0 ∉ T) (c : ℚ) :
    infPoly T c ≠ 0 := by
  have hL : infScalarL T ≠ 0 := infScalarL_ne_zero T h0
  have hMdeg : (infProdM T).degree = (T.card : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (infProdM_monic T).ne_zero, infProdM_natDegree]
  have hcard : (0 : WithBot ℕ) < (T.card : WithBot ℕ) := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hlt : (Polynomial.C (c * (infScalarL T)⁻¹) : Polynomial ℚ).degree
      < (infProdM T).degree := by
    rw [hMdeg]
    exact lt_of_le_of_lt Polynomial.degree_C_le hcard
  have hN : (infProdM T - Polynomial.C (c * (infScalarL T)⁻¹)).Monic :=
    (infProdM_monic T).sub_of_left hlt
  have hfac : infPoly T c
      = Polynomial.C (infScalarL T) *
        (infProdM T - Polynomial.C (c * (infScalarL T)⁻¹)) := by
    rw [infPoly, mul_sub, ← infPoly_factor T h0, ← Polynomial.C_mul]
    congr 1
    rw [show (infScalarL T) * (c * (infScalarL T)⁻¹) = c from by
      rw [← mul_assoc, mul_comm (infScalarL T) c, mul_assoc,
        mul_inv_cancel₀ hL, mul_one]]
  rw [hfac]
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr hL) hN.ne_zero

/-- The value at r of infPoly T c is psiChartInfDenom n T - c. -/
theorem rHom_infPoly (n : Nat) (T : Finset ℚ) (c : ℚ) :
    rHom n (infPoly T c) = psiChartInfDenom n T - algebraMap ℚ (R2 n) c := by
  have hprod : (∏ t ∈ T, (1 - Polynomial.C t * Polynomial.X)).eval₂
        (algebraMap ℚ (R2 n)) (chartR n)
      = ∏ t ∈ T, (1 - algebraMap ℚ (R2 n) t * chartR n) := by
    rw [Polynomial.eval₂_finsetProd]
    exact Finset.prod_congr rfl fun t _ => by
      simp [Polynomial.eval₂_sub, Polynomial.eval₂_mul]
  show (infPoly T c).eval₂ (algebraMap ℚ (R2 n)) (chartR n)
    = psiChartInfDenom n T - algebraMap ℚ (R2 n) c
  rw [infPoly, Polynomial.eval₂_sub, Polynomial.eval₂_C, hprod]
  rfl

/-- The same in the ℚ[t]-algebra language. -/
theorem algebraMap_infPoly (n : Nat) (T : Finset ℚ) (c : ℚ) :
    letI := rAlgebra n
    algebraMap (Polynomial ℚ) (R2 n) (infPoly T c)
      = psiChartInfDenom n T - algebraMap ℚ (R2 n) c := by
  letI := rAlgebra n
  exact rHom_infPoly n T c

#print axioms infProdM_monic
#print axioms infProdM_natDegree
#print axioms one_sub_C_mul_X_eq
#print axioms infPoly_factor
#print axioms infScalarL_ne_zero
#print axioms infPoly_ne_zero
#print axioms rHom_infPoly
#print axioms algebraMap_infPoly

/-! ## 3. Finite dimension of R2 n modulo (f(r)) over ℚ -/

/-- Finiteness of R2 n modulo the ideal generated by f(r), in map form (the ideal is
rewritten as (span f).map so that the quotient-algebra instances apply).  The argument
is Mzk1G1PsiQuotientFiniteActual.quot_finiteDim_map, transported to the λ-chart. -/
theorem quot_finiteDim_inf_map (n : Nat) (hn : 0 < n) (f : Polynomial ℚ) (hf : f ≠ 0) :
    letI := rAlgebra n
    Module.Finite ℚ
      (R2 n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map
        (algebraMap (Polynomial ℚ) (R2 n))) := by
  letI := rAlgebra n
  haveI hfin : Module.Finite (Polynomial ℚ) (R2 n) := chartRing_finite_r n hn
  haveI h0 : IsScalarTower ℚ (Polynomial ℚ) (R2 n) := isScalarTower_r n
  have hg' : RingHom.Finite
      (algebraMap (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
        (R2 n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map
          (algebraMap (Polynomial ℚ) (R2 n)))) := by
    letI hAlg : Algebra (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
        (R2 n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map
          (algebraMap (Polynomial ℚ) (R2 n))) :=
      Ideal.Quotient.algebraQuotientMapQuotient
    letI hMod : Module (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
        (R2 n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map
          (algebraMap (Polynomial ℚ) (R2 n))) :=
      hAlg.toModule
    haveI hST1 : IsScalarTower (Polynomial ℚ)
        (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
        (R2 n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map
          (algebraMap (Polynomial ℚ) (R2 n))) :=
      inferInstance
    haveI hB : Module.Finite (Polynomial ℚ)
        (R2 n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map
          (algebraMap (Polynomial ℚ) (R2 n))) :=
      inferInstance
    rw [RingHom.finite_algebraMap]
    exact Module.Finite.of_restrictScalars_finite (Polynomial ℚ)
      (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
      (R2 n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map
        (algebraMap (Polynomial ℚ) (R2 n)))
  have hf' : RingHom.Finite
      (algebraMap ℚ (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))) := by
    rw [RingHom.finite_algebraMap]
    exact quotient_poly_finite f hf
  have hcomp : (algebraMap (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
        (R2 n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map
          (algebraMap (Polynomial ℚ) (R2 n)))).comp
      (algebraMap ℚ (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ))))
      = (Ideal.Quotient.mk ((Ideal.span ({f} : Set (Polynomial ℚ))).map
            (algebraMap (Polynomial ℚ) (R2 n)))).comp (algebraMap ℚ (R2 n)) := by
    ext q
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have h1 : algebraMap ℚ (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ))) q
        = Ideal.Quotient.mk (Ideal.span ({f} : Set (Polynomial ℚ)))
            (algebraMap ℚ (Polynomial ℚ) q) := rfl
    rw [h1, Ideal.Quotient.algebraMap_quotient_map_quotient,
      IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (R2 n) q]
  have hcompfin := RingHom.Finite.comp hg' hf'
  rw [hcomp, Ideal.Quotient.mk_comp_algebraMap] at hcompfin
  exact RingHom.finite_algebraMap.mp hcompfin

/-- For nonzero f in ℚ[X], the quotient of R2 n by f(r) is a finite-dimensional
ℚ-vector space. -/
theorem quot_finiteDim_inf (n : Nat) (hn : 0 < n) (f : Polynomial ℚ) (hf : f ≠ 0) :
    letI := rAlgebra n
    Module.Finite ℚ
      (R2 n ⧸ Ideal.span ({algebraMap (Polynomial ℚ) (R2 n) f} : Set (R2 n))) := by
  letI := rAlgebra n
  have hmap : Ideal.span ({algebraMap (Polynomial ℚ) (R2 n) f} : Set (R2 n))
      = (Ideal.span ({f} : Set (Polynomial ℚ))).map
        (algebraMap (Polynomial ℚ) (R2 n)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have haux : Module.Finite ℚ
      (R2 n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map
        (algebraMap (Polynomial ℚ) (R2 n))) :=
    quot_finiteDim_inf_map n hn f hf
  haveI := haux
  exact Module.Finite.equiv
    (Ideal.quotientEquivAlgOfEq (R₁ := ℚ) hmap).toLinearEquiv.symm

#print axioms quot_finiteDim_inf_map
#print axioms quot_finiteDim_inf

/-! ## 4. The fibre of the λ-chart coordinate over a value -/

/-- **Finite dimension of R2 n modulo (q - c) over ℚ** where q = psiChartInfDenom n T is the
denominator of the λ-chart coordinate. -/
theorem quot_finiteDim_psiInf (n : Nat) (hn : 0 < n) (T : Finset ℚ) (hT : T.Nonempty)
    (h0 : 0 ∉ T) (c : ℚ) :
    Module.Finite ℚ
      (R2 n ⧸ Ideal.span
        ({psiChartInfDenom n T - algebraMap ℚ (R2 n) c} : Set (R2 n))) := by
  letI := rAlgebra n
  have hev : algebraMap (Polynomial ℚ) (R2 n) (infPoly T c)
      = psiChartInfDenom n T - algebraMap ℚ (R2 n) c := algebraMap_infPoly n T c
  have haux : Module.Finite ℚ
      (R2 n ⧸ Ideal.span
        ({algebraMap (Polynomial ℚ) (R2 n) (infPoly T c)} : Set (R2 n))) :=
    quot_finiteDim_inf n hn (infPoly T c) (infPoly_ne_zero T hT h0 c)
  rw [show Ideal.span ({psiChartInfDenom n T - algebraMap ℚ (R2 n) c} : Set (R2 n))
      = Ideal.span ({algebraMap (Polynomial ℚ) (R2 n) (infPoly T c)} : Set (R2 n))
      from by rw [hev]]
  exact haux

/-- **Finite fibres of the λ-chart coordinate**: only finitely many primes of the second
Fermat chart ring R2 n contain the value q - c, q = psiChartInfDenom n T. -/
theorem finite_primes_of_psiChartInf (n : Nat) (hn : 0 < n) (T : Finset ℚ) (hT : T.Nonempty)
    (h0 : 0 ∉ T) (c : ℚ) :
    {p : PrimeSpectrum (R2 n) |
      (psiChartInfDenom n T - algebraMap ℚ (R2 n) c) ∈ p.asIdeal}.Finite :=
  finite_primes_of_finite_quotient (f := psiChartInfDenom n T - algebraMap ℚ (R2 n) c)
    (quot_finiteDim_psiInf n hn T hT h0 c)

#print axioms quot_finiteDim_psiInf
#print axioms finite_primes_of_psiChartInf


/-! ## 5. The D(q) piece: primes of the localization -/

/-- **Finite fibres of the λ-chart coordinate on the localization `D(q)`**.

Primes of `Localization.Away q` correspond, via the injective comap map, to primes of `R2 n`
which do not contain `q` (`PrimeSpectrum.localization_comap_range`,
`PrimeSpectrum.localization_away_comap_range`, `IsLocalization.isPrime_iff_isPrime_disjoint`).
A prime `P` of the localization contains the image of `q - c` iff its comap contains
`q - c`, so `finite_primes_of_psiChartInf` transfers along the injection
`PrimeSpectrum.localization_comap_injective`. -/
theorem finite_primes_of_psiChartInf_localized (n : Nat) (hn : 0 < n) (T : Finset ℚ)
    (hT : T.Nonempty) (h0 : 0 ∉ T) (c : ℚ) :
    {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
      algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))
        (psiChartInfDenom n T - algebraMap ℚ (R2 n) c) ∈ P.asIdeal}.Finite := by
  classical
  have hinj : Function.Injective
      (PrimeSpectrum.comap (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T)))) :=
    PrimeSpectrum.localization_comap_injective (Localization.Away (psiChartInfDenom n T))
      (Submonoid.powers (psiChartInfDenom n T))
  have hfin : ({p : PrimeSpectrum (R2 n) |
      (psiChartInfDenom n T - algebraMap ℚ (R2 n) c) ∈ p.asIdeal} : Set (PrimeSpectrum (R2 n))).Finite :=
    finite_primes_of_psiChartInf n hn T hT h0 c
  have hset : {P : PrimeSpectrum (Localization.Away (psiChartInfDenom n T)) |
        algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))
          (psiChartInfDenom n T - algebraMap ℚ (R2 n) c) ∈ P.asIdeal}
      = PrimeSpectrum.comap (algebraMap (R2 n) (Localization.Away (psiChartInfDenom n T))) ⁻¹'
        {p : PrimeSpectrum (R2 n) |
          (psiChartInfDenom n T - algebraMap ℚ (R2 n) c) ∈ p.asIdeal} := by
    ext P
    simp [PrimeSpectrum.comap_asIdeal]
  rw [hset]
  exact Set.Finite.preimage (hinj.injOn.mono (Set.subset_univ _)) hfin

#print axioms finite_primes_of_psiChartInf_localized

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberFiniteInfActual
