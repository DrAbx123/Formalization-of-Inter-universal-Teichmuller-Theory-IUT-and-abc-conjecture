/-
# R n finite over Q[t] (t |-> g = psiChart0Coord), and finite-dimensional quotients

Route (mirroring grace's Mzk1G1FermatChartFiniteActual, where t |-> lambda = x0^n):
* x0 is integral over Q[t]: it is a root of the monic polynomial
    prod_{t in T} (X - C t) - C X
  (of degree |T| >= 1 when T is nonempty).
* y1 is integral over Q[t]: y1^n = 1 - x0^n, x0^n is integral, so of_pow.
* {x0, y1} generates R n over Q[t] (adjoin_eq_top_g), giving Algebra.FiniteType,
  hence Algebra.IsIntegral, hence Module.Finite by Algebra.IsIntegral.finite.

Quotient:
* for nonzero f, Q[t]/(f) is finite over Q because f is associated to the monic
  polynomial f * C f.leadingCoeff^-1 (Polynomial.Monic.finite_quotient).
* R n / (f) is finite over Q[t] (Module.Finite.quotient) and hence over Q[t]/(f)
  (Module.Finite.of_restrictScalars_finite).
* RingHom.Finite.comp composes the two finite homs, avoiding an explicit
  IsScalarTower over Q on the quotient; the ring-hom composition is identified
  with algebraMap Q (R n / (f)) by extensionality.

No placeholders, new postulates, or toy carriers.
-/
import tmp.sheaf.xif.paper.Mzk1G1PsiChartFiniteGActual
import tmp.sheaf.xif.paper.Mzk1G1PsiArtinianSpectrumActual
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiQuotientFiniteActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatChartFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartFiniteGActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual

variable (n : Nat) (T : Finset ℚ)

/-- local short name for the Fermat equation. -/
abbrev fermatEq (n : Nat) : MvPolynomial (Fin 2) ℚ :=
  LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual.fermatEquation n

/-- gHom sends the constant C r to the base scalar r. -/
theorem gHom_C_eq (r : ℚ) : gHom n T (Polynomial.C r) = algebraMap ℚ (R n) r := by
  simp [gHom]

/-- Q -> Q[t] -> R n is a scalar tower (g-structure). -/
theorem isScalarTower_g :
    letI := gAlgebra n T
    IsScalarTower ℚ (Polynomial ℚ) (R n) := by
  letI := gAlgebra n T
  refine IsScalarTower.of_algebraMap_eq fun q => ?_
  rw [show algebraMap (Polynomial ℚ) (R n) = gHom n T from rfl]
  change algebraMap ℚ (R n) q = gHom n T (Polynomial.C q)
  exact (gHom_C_eq n T q).symm

#print axioms gHom_C_eq
#print axioms isScalarTower_g

/-- 1. x0 is integral over Q[t] (g-structure), a root of the monic
prod (X - t_i) - T. -/
theorem x0_isIntegral_g (hT : T.Nonempty) :
    letI := gAlgebra n T
    IsIntegral (Polynomial ℚ) (x0 n) := by
  letI := gAlgebra n T
  refine ⟨gMonicPoly T, gMonicPoly_monic T hT, ?_⟩
  rw [show algebraMap (Polynomial ℚ) (R n) = gHom n T from rfl]
  rw [gMonicPoly, Polynomial.eval₂_sub, Polynomial.eval₂_finsetProd]
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
    gHom_C_eq n T, gHom_X n T]
  have hprod : (∏ t ∈ T, (x0 n - algebraMap ℚ (R n) t)) = psiChart0Coord n T := by
    simp [psiChart0Coord, chartX, x0]
  rw [hprod, sub_self]

#print axioms x0_isIntegral_g

/-- 2. y1 is integral over Q[t] (g-structure), via y1^n = 1 - x0^n. -/
theorem y1_isIntegral_g (hT : T.Nonempty) :
    letI := gAlgebra n T
    IsIntegral (Polynomial ℚ) (y1 n) := by
  letI := gAlgebra n T
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    -- n = 0: the Fermat equation is 1 = 0, so the ring is trivial and y1 = 0.
    have h1 : (1 : R 0) = 0 := by
      have h := x0_pow_add_y1_pow 0
      simpa using h
    have hy1 : y1 0 = 0 := by
      rw [← mul_one (y1 0), h1, mul_zero]
    rw [hy1]
    exact isIntegral_zero
  · have hx : IsIntegral (Polynomial ℚ) (x0 n ^ n) := (x0_isIntegral_g n T hT).pow n
    have hy : IsIntegral (Polynomial ℚ) (y1 n ^ n) := by
      have h : y1 n ^ n = 1 - x0 n ^ n := by
        have h := x0_pow_add_y1_pow n
        linear_combination h
      rw [h]
      exact isIntegral_one.sub hx
    exact IsIntegral.of_pow hn hy

#print axioms y1_isIntegral_g

/-- Under the g-algebra structure the constants C r map to the base scalars. -/
theorem algebraMap_C_eq_g (r : ℚ) :
    letI := gAlgebra n T
    algebraMap (Polynomial ℚ) (R n) (Polynomial.C r) = algebraMap ℚ (R n) r := by
  letI := gAlgebra n T
  rw [show algebraMap (Polynomial ℚ) (R n) = gHom n T from rfl]
  exact gHom_C_eq n T r

#print axioms algebraMap_C_eq_g

/-- 3. {x0, y1} generates R n as a Q[t]-algebra (g-structure). -/
theorem adjoin_eq_top_g :
    letI := gAlgebra n T
    Algebra.adjoin (Polynomial ℚ) ({x0 n, y1 n} : Set (R n)) = ⊤ := by
  letI := gAlgebra n T
  rw [eq_top_iff]
  intro a _
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := Ideal.span {fermatEq n}) a
  have key : ∀ p : MvPolynomial (Fin 2) ℚ,
      Ideal.Quotient.mk (Ideal.span {fermatEq n}) p
        ∈ Algebra.adjoin (Polynomial ℚ) ({x0 n, y1 n} : Set (R n)) := by
    intro p
    refine MvPolynomial.induction_on
      (motive := fun q => Ideal.Quotient.mk (Ideal.span {fermatEq n}) q
        ∈ Algebra.adjoin (Polynomial ℚ) ({x0 n, y1 n} : Set (R n))) p ?_ ?_ ?_
    · intro r
      rw [mk_C_eq_algebraMap, ← algebraMap_C_eq_g n T r]
      exact Subalgebra.algebraMap_mem _ _
    · intro p q hp hq
      rw [map_add]
      exact Subalgebra.add_mem _ hp hq
    · intro p i hp
      rw [map_mul]
      refine Subalgebra.mul_mem _ hp ?_
      fin_cases i
      · exact Algebra.subset_adjoin (by simp [x0])
      · exact Algebra.subset_adjoin (by simp [y1])
  exact key p

#print axioms adjoin_eq_top_g

/-- 4. R n is a finitely generated Q[t]-algebra (g-structure). -/
theorem chart_finiteType_g :
    letI := gAlgebra n T
    Algebra.FiniteType (Polynomial ℚ) (R n) := by
  letI := gAlgebra n T
  classical
  refine ⟨?fg⟩
  rw [Subalgebra.fg_def]
  exact ⟨({x0 n, y1 n} : Set (R n)), Set.toFinite _, adjoin_eq_top_g n T⟩

#print axioms chart_finiteType_g

/-- 5. R n is integral over Q[t] (g-structure). -/
theorem chart_isIntegral_g (hT : T.Nonempty) :
    letI := gAlgebra n T
    Algebra.IsIntegral (Polynomial ℚ) (R n) := by
  letI := gAlgebra n T
  refine { isIntegral := ?_ }
  intro x
  have hmem : x ∈ Algebra.adjoin (Polynomial ℚ) ({x0 n, y1 n} : Set (R n)) := by
    rw [adjoin_eq_top_g n T]; trivial
  exact Algebra.adjoin_induction (p := fun y _ => IsIntegral (Polynomial ℚ) y)
    (fun y hy => by
      rcases hy with rfl | rfl
      · exact x0_isIntegral_g n T hT
      · exact y1_isIntegral_g n T hT)
    (fun r => isIntegral_algebraMap)
    (fun y z _ _ hy hz => hy.add hz)
    (fun y z _ _ hy hz => hy.mul hz) hmem

#print axioms chart_isIntegral_g

/-- 6. R n is a finite Q[t]-module (g-structure). -/
theorem chartRing_finite_g (hT : T.Nonempty) :
    letI := gAlgebra n T
    Module.Finite (Polynomial ℚ) (R n) := by
  letI := gAlgebra n T
  haveI := chart_isIntegral_g n T hT
  exact Algebra.IsIntegral.finite (R := Polynomial ℚ) (A := R n) (h' := chart_finiteType_g n T)

#print axioms chartRing_finite_g

/-- The monic associate of a nonzero polynomial spans the same ideal. -/
theorem span_monic_associate (f : Polynomial ℚ) (hf : f ≠ 0) :
    Ideal.span ({f * Polynomial.C f.leadingCoeff⁻¹} : Set (Polynomial ℚ))
      = Ideal.span ({f} : Set (Polynomial ℚ)) := by
  have hf' : f.leadingCoeff ≠ 0 := fun h => hf (Polynomial.leadingCoeff_eq_zero.mp h)
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact ⟨Polynomial.C f.leadingCoeff⁻¹, rfl⟩
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    refine ⟨Polynomial.C f.leadingCoeff, ?_⟩
    rw [mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hf', Polynomial.C_1, mul_one]

#print axioms span_monic_associate

/-- Q[t]/(f) is finite-dimensional over Q for nonzero f. -/
theorem quotient_poly_finite (f : Polynomial ℚ) (hf : f ≠ 0) :
    Module.Finite ℚ (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ))) := by
  have hg : (f * Polynomial.C f.leadingCoeff⁻¹).Monic :=
    Polynomial.monic_mul_leadingCoeff_inv hf
  rw [← span_monic_associate f hf]
  exact hg.finite_quotient

#print axioms quotient_poly_finite

/-- 7a. Finiteness of R n modulo the ideal generated by f, in the map form
(the ideal is rewritten as (span f).map so that the quotient-algebra instances apply). -/
theorem quot_finiteDim_map (hT : T.Nonempty) (f : Polynomial ℚ) (hf : f ≠ 0) :
    letI := gAlgebra n T
    Module.Finite ℚ
      (R n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map (algebraMap (Polynomial ℚ) (R n))) := by
  letI := gAlgebra n T
  haveI hfin : Module.Finite (Polynomial ℚ) (R n) := chartRing_finite_g n T hT
  haveI h0 : IsScalarTower ℚ (Polynomial ℚ) (R n) := isScalarTower_g n T
  -- The quotient algebra instance exists, but the generic Algebra.toModule instance
  -- is not found by synthInstance for this quotient (instance diamond), so the
  -- quotient Module structure is provided explicitly, locally inside this proof.
  have hg' : RingHom.Finite
      (algebraMap (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
        (R n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map (algebraMap (Polynomial ℚ) (R n)))) := by
    letI hAlg : Algebra (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
        (R n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map (algebraMap (Polynomial ℚ) (R n))) :=
      Ideal.Quotient.algebraQuotientMapQuotient
    letI hMod : Module (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
        (R n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map (algebraMap (Polynomial ℚ) (R n))) :=
      hAlg.toModule
    haveI hST1 : IsScalarTower (Polynomial ℚ) (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
        (R n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map (algebraMap (Polynomial ℚ) (R n))) :=
      inferInstance
    haveI hB : Module.Finite (Polynomial ℚ)
        (R n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map (algebraMap (Polynomial ℚ) (R n))) :=
      inferInstance
    rw [RingHom.finite_algebraMap]
    exact Module.Finite.of_restrictScalars_finite (Polynomial ℚ)
      (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
      (R n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map (algebraMap (Polynomial ℚ) (R n)))
  -- the quotient Q -> Q[t]/(f) is a finite ring hom
  have hf' : RingHom.Finite
      (algebraMap ℚ (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))) := by
    rw [RingHom.finite_algebraMap]
    exact quotient_poly_finite f hf
  -- identify the composite with the explicit map (mk (f) : R n -> R n/(f)) . (Q -> R n)
  have hcomp : (algebraMap (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ)))
        (R n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map (algebraMap (Polynomial ℚ) (R n)))).comp
      (algebraMap ℚ (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ))))
      = (Ideal.Quotient.mk ((Ideal.span ({f} : Set (Polynomial ℚ))).map
            (algebraMap (Polynomial ℚ) (R n)))).comp (algebraMap ℚ (R n)) := by
    ext q
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have h1 : algebraMap ℚ (Polynomial ℚ ⧸ Ideal.span ({f} : Set (Polynomial ℚ))) q
        = Ideal.Quotient.mk (Ideal.span ({f} : Set (Polynomial ℚ)))
            (algebraMap ℚ (Polynomial ℚ) q) := rfl
    rw [h1, Ideal.Quotient.algebraMap_quotient_map_quotient,
      IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (R n) q]
  have hcompfin := RingHom.Finite.comp hg' hf'
  rw [hcomp, Ideal.Quotient.mk_comp_algebraMap] at hcompfin
  exact RingHom.finite_algebraMap.mp hcompfin

#print axioms quot_finiteDim_map

/-- 7. For nonzero f, the quotient of R n by the ideal generated by f is a
finite-dimensional Q-vector space (g-structure). -/
theorem quot_finiteDim (hT : T.Nonempty) (f : Polynomial ℚ) (hf : f ≠ 0) :
    letI := gAlgebra n T
    Module.Finite ℚ
      (R n ⧸ Ideal.span ({algebraMap (Polynomial ℚ) (R n) f} : Set (R n))) := by
  letI := gAlgebra n T
  have hmap : Ideal.span ({algebraMap (Polynomial ℚ) (R n) f} : Set (R n))
      = (Ideal.span ({f} : Set (Polynomial ℚ))).map (algebraMap (Polynomial ℚ) (R n)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have haux : Module.Finite ℚ
      (R n ⧸ (Ideal.span ({f} : Set (Polynomial ℚ))).map (algebraMap (Polynomial ℚ) (R n))) :=
    quot_finiteDim_map n T hT f hf
  haveI := haux
  exact Module.Finite.equiv
    (Ideal.quotientEquivAlgOfEq (R₁ := ℚ) hmap).toLinearEquiv.symm

#print axioms quot_finiteDim

end LeanFormal.IUT.XiFPaper.Mzk1G1PsiQuotientFiniteActual