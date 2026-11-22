/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1912

# S1912: the equal-rank inclusion via the trace-dual retraction

S1849 isolated the trace-form input of the S1848 route as

  S1849EqualRankInclusion:
    an injective map of finite etale R'-algebras whose ranks at every prime agree
    is surjective.

S1860 proved trace duality for finite projective etale algebras.  This file gives the
route requested for S1912, which avoids the normal-domain integral-closedness step:

  A --i--> B, equal rank
    => after K = Frac(R'), i_K : A_K --> B_K is an injective map of equidimensional
       finite-dimensional K-vector spaces, hence bijective;
    => Tr_B(i a) = Tr_A(a) for all a : A, by base change to K and invariance of the
       trace under the resulting algebra equivalence A_K = B_K;
    => trace duality on A produces a linear retraction psi : B --> A with
       psi (i a) = a;
    => B = A + ker psi, and ker psi is a direct summand of B, hence finite flat;
    => rank additivity at every prime, together with the equal-rank hypothesis, gives
       rank (ker psi) = 0 at every prime;
    => a finite flat module of rank zero at every prime is subsingleton, so
       ker psi = 0;
    => psi is injective, and psi (i a) = a makes i surjective.

No normal-domain integral closedness is used.

## Honest boundary

No sorry, admit, new axiom, Shrink, ULift or PUnit occurs in this file.  Everything
asserted as a theorem is proved.  The only external mathematical input is trace duality
S1859ProjectiveTraceDuality_proof, proved in S1860.
-/

import tmp.sheaf.xif.paper.S1860TraceDualityActual
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Flat.Basic

noncomputable section
set_option profiler true
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
open scoped TensorProduct
open LinearMap

namespace LeanFormal.IUT.XiFPaper.S1912EqualRankTraceRetractionActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1849RPrimeReflectCompleteActual
open LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual
open LeanFormal.IUT.XiFPaper.S1860TraceDualityActual

set_option autoImplicit false

/-! ## 1. The generic point and its residue field -/

/-- The localisation of R' at the generic point of Spec R'. -/
abbrev S1912K : Type := Localization.AtPrime (⊥ : Ideal S1779R)

instance S1912K_isFractionRing : IsFractionRing S1779R S1912K := by
  simpa [Ideal.primeCompl_bot] using
    (Localization.isLocalization (M := (⊥ : Ideal S1779R).primeCompl))

instance S1912K_field : Field S1912K := by
  haveI : IsDomain S1779R := S1849_isDomain
  exact IsFractionRing.toField S1779R

theorem S1912K_algebraMap_injective : Function.Injective (algebraMap S1779R S1912K) :=
  IsFractionRing.injective S1779R S1912K

theorem S1912K_flat : Module.Flat S1779R S1912K :=
  IsLocalization.flat S1912K (⊥ : Ideal S1779R).primeCompl

/-! ## 2. Trace duality as a linear equivalence -/

/-- Trace duality, bundled as a linear equivalence A ~= A^*. -/
noncomputable def traceDualEquiv (A : CommAlgCat.FiniteEtale.{0} S1779R)
    [Module.Projective S1779R (A : Type)] :
    (A : Type) ≃ₗ[S1779R] ((A : Type) →ₗ[S1779R] S1779R) := by
  refine LinearEquiv.ofBijective
    (projectiveTraceForm (R := S1779R) (A := (A : Type))) ?_
  constructor
  · intro a1 a2 h
    obtain ⟨a, -, huniq⟩ :=
      S1859ProjectiveTraceDuality_proof A inferInstance
        (projectiveTraceForm (R := S1779R) (A := (A : Type)) a1)
    have ha1 : ∀ b : (A : Type),
        projectiveTraceForm (R := S1779R) (A := (A : Type)) a1 b =
          projectiveTraceForm (R := S1779R) (A := (A : Type)) a1 b :=
      fun _ => rfl
    have ha2 : ∀ b : (A : Type),
        projectiveTraceForm (R := S1779R) (A := (A : Type)) a2 b =
          projectiveTraceForm (R := S1779R) (A := (A : Type)) a1 b := by
      intro b
      exact (congrArg (fun φ : (A : Type) →ₗ[S1779R] S1779R => φ b) h).symm
    exact (huniq a1 ha1).trans (huniq a2 ha2).symm
  · intro φ
    obtain ⟨a, ha, -⟩ := S1859ProjectiveTraceDuality_proof A inferInstance φ
    refine ⟨a, ?_⟩
    ext b
    exact ha b

/-! ## 3. The trace functional and the retraction -/

section Retraction

variable {A B : CommAlgCat.FiniteEtale.{0} S1779R}
variable [Module.Projective S1779R (A : Type)] [Module.Projective S1779R (B : Type)]

/-- The functional on A induced by an element of B and an algebra map A -> B. -/
noncomputable def traceFunctional (f : A ⟶ B) :
    (B : Type) →ₗ[S1779R] ((A : Type) →ₗ[S1779R] S1779R) :=
  (LinearMap.lcomp S1779R S1779R f.hom.hom.toLinearMap).comp
    (projectiveTraceForm (R := S1779R) (A := (B : Type)))

@[simp]
lemma traceFunctional_apply (f : A ⟶ B) (b : (B : Type)) (a : (A : Type)) :
    traceFunctional f b a =
      projectiveTraceForm (R := S1779R) (A := (B : Type)) b (f.hom.hom a) := by
  simp [traceFunctional, LinearMap.lcomp_apply]

/-- The trace-dual retraction B -> A. -/
noncomputable def retraction (f : A ⟶ B) : (B : Type) →ₗ[S1779R] (A : Type) :=
  (traceDualEquiv A).symm.toLinearMap.comp (traceFunctional f)

/-- The defining property of the retraction: it represents the functional
a |-> Tr_B (b * f a) with respect to the trace form of A. -/
lemma retraction_spec (f : A ⟶ B) (b : (B : Type)) (a : (A : Type)) :
    projectiveTraceForm (R := S1779R) (A := (A : Type)) (retraction f b) a =
      projectiveTraceForm (R := S1779R) (A := (B : Type)) b (f.hom.hom a) := by
  change projectiveTraceForm (R := S1779R) (A := (A : Type))
      ((traceDualEquiv A).symm (traceFunctional f b)) a =
    projectiveTraceForm (R := S1779R) (A := (B : Type)) b (f.hom.hom a)
  have h := LinearEquiv.apply_symm_apply (traceDualEquiv A) (traceFunctional f b)
  have h2 := congrArg (fun φ : (A : Type) →ₗ[S1779R] S1779R => φ a) h
  rw [traceFunctional_apply] at h2
  exact h2

/-! ## 4. The trace of an element of A, computed in B -/

/-- **Trace comparison.**  If i : A -> B is injective and the ranks agree at every
prime, then Tr_B(i a) = Tr_A(a).  This is the place where the generic fibre is used:
after base change to K the map i becomes an algebra equivalence, and the trace is
invariant under algebra equivalences. -/
theorem trace_eq_of_image (f : A ⟶ B)
    (hinj : Function.Injective f.hom.hom)
    (hrank : ∀ p : PrimeSpectrum S1779R,
      Module.rankAtStalk (A : Type) p = Module.rankAtStalk (B : Type) p)
    (y : (A : Type)) :
    algebraTrace (R := S1779R) (A := (B : Type)) (f.hom.hom y) =
      algebraTrace (R := S1779R) (A := (A : Type)) y := by
  haveI : Module.Flat S1779R S1912K := S1912K_flat
  let Φ := Algebra.TensorProduct.map (AlgHom.id S1912K S1912K) f.hom.hom
  have hΦ_tmul : ∀ (s : S1912K) (a : (A : Type)),
      Φ (s ⊗ₜ[S1779R] a) = s ⊗ₜ[S1779R] f.hom.hom a := by
    intro s a
    simpa [Φ] using
      (Algebra.TensorProduct.map_tmul (f := AlgHom.id S1912K S1912K)
        (g := f.hom.hom) s a)
  have hlin : Φ.toLinearMap =
      TensorProduct.map (LinearMap.id : S1912K →ₗ[S1779R] S1912K)
        f.hom.hom.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp [Φ]
    | add z₁ z₂ h₁ h₂ => simp [map_add, h₁, h₂]
  have hΦ_inj : Function.Injective Φ := by
    have hinj_lin : Function.Injective
        (TensorProduct.map (LinearMap.id : S1912K →ₗ[S1779R] S1912K)
          f.hom.hom.toLinearMap) := by
      have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S1912K)
        (f := f.hom.hom.toLinearMap) (by simpa using hinj)
      simpa [LinearMap.lTensor_def] using h
    intro x y hxy
    apply hinj_lin
    rw [← hlin]
    exact hxy
  have hfin : Module.finrank S1912K (S1912K ⊗[S1779R] (A : Type)) =
      Module.finrank S1912K (S1912K ⊗[S1779R] (B : Type)) := by
    rw [← Module.rankAtStalk_eq_finrank_tensorProduct
        (M := (A : Type)) (p := (⊥ : PrimeSpectrum S1779R)),
      ← Module.rankAtStalk_eq_finrank_tensorProduct
        (M := (B : Type)) (p := (⊥ : PrimeSpectrum S1779R))]
    exact hrank ⊥
  haveI : FiniteDimensional S1912K (S1912K ⊗[S1779R] (A : Type)) :=
    Module.Finite.base_change S1779R S1912K (A : Type)
  haveI : FiniteDimensional S1912K (S1912K ⊗[S1779R] (B : Type)) :=
    Module.Finite.base_change S1779R S1912K (B : Type)
  have hΦ_surj : Function.Surjective Φ := by
    have hsurj : Function.Surjective Φ.toLinearMap :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp
        (by simpa using hΦ_inj)
    exact hsurj
  let e : S1912K ⊗[S1779R] (A : Type) ≃ₐ[S1912K]
      S1912K ⊗[S1779R] (B : Type) :=
    AlgEquiv.ofBijective Φ ⟨hΦ_inj, hΦ_surj⟩
  have he_tmul : e ((1 : S1912K) ⊗ₜ[S1779R] y) =
      (1 : S1912K) ⊗ₜ[S1779R] f.hom.hom y := by
    change Φ ((1 : S1912K) ⊗ₜ[S1779R] y) = _
    exact hΦ_tmul 1 y
  have htrace :
      algebraTrace (R := S1912K) (A := S1912K ⊗[S1779R] (B : Type))
          ((1 : S1912K) ⊗ₜ[S1779R] f.hom.hom y) =
        algebraTrace (R := S1912K) (A := S1912K ⊗[S1779R] (A : Type))
          ((1 : S1912K) ⊗ₜ[S1779R] y) := by
    rw [algebraTrace_eq_trace, algebraTrace_eq_trace]
    rw [← he_tmul]
    exact Algebra.trace_eq_of_algEquiv e ((1 : S1912K) ⊗ₜ[S1779R] y)
  apply S1912K_algebraMap_injective
  rw [← BaseChange.algebraTrace_baseChange (R := S1779R) (A := (B : Type))
        (S := S1912K) (x := f.hom.hom y),
      ← BaseChange.algebraTrace_baseChange (R := S1779R) (A := (A : Type))
        (S := S1912K) (x := y)]
  exact htrace

/-- The retraction fixes the image of the inclusion. -/
lemma retraction_comp (f : A ⟶ B)
    (hinj : Function.Injective f.hom.hom)
    (hrank : ∀ p : PrimeSpectrum S1779R,
      Module.rankAtStalk (A : Type) p = Module.rankAtStalk (B : Type) p)
    (a : (A : Type)) : retraction f (f.hom.hom a) = a := by
  apply (traceDualEquiv A).injective
  apply LinearMap.ext
  intro x
  change projectiveTraceForm (R := S1779R) (A := (A : Type))
      (retraction f (f.hom.hom a)) x =
    projectiveTraceForm (R := S1779R) (A := (A : Type)) a x
  rw [retraction_spec]
  rw [projectiveTraceForm_apply, projectiveTraceForm_apply]
  rw [← map_mul]
  exact trace_eq_of_image f hinj hrank (a * x)

end Retraction

/-! ## 5. The equal-rank inclusion -/

/-- **S1849EqualRankInclusion is proved** by the trace-dual retraction route. -/
theorem S1912_EqualRankInclusion : S1849EqualRankInclusion := by
  intro A B f hinj hrank
  haveI hFA : Module.Finite S1779R (A : Type) := A.property.left
  haveI hFB : Module.Finite S1779R (B : Type) := B.property.left
  haveI hEA : Algebra.Etale S1779R (A : Type) := A.property.right
  haveI hEB : Algebra.Etale S1779R (B : Type) := B.property.right
  haveI hFlatA : Module.Flat S1779R (A : Type) := inferInstance
  haveI hFlatB : Module.Flat S1779R (B : Type) := inferInstance
  haveI hProjA : Module.Projective S1779R (A : Type) := by
    haveI : Module.FinitePresentation S1779R (A : Type) :=
      Module.finitePresentation_of_finite S1779R (A : Type)
    exact Module.Flat.projective_of_finitePresentation
  haveI hProjB : Module.Projective S1779R (B : Type) := by
    haveI : Module.FinitePresentation S1779R (B : Type) :=
      Module.finitePresentation_of_finite S1779R (B : Type)
    exact Module.Flat.projective_of_finitePresentation
  let ψ : (B : Type) →ₗ[S1779R] (A : Type) := retraction f
  have hψcomp : ∀ a : (A : Type), ψ (f.hom.hom a) = a :=
    fun a => retraction_comp f hinj hrank a
  -- The image of f and the kernel of psi are complementary.
  have hcompl : IsCompl (LinearMap.ker ψ)
      (LinearMap.range f.hom.hom.toLinearMap) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxker hxrange
      obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hxrange
      have h0 : ψ (f.hom.hom a) = 0 := hxker
      rw [hψcomp a] at h0
      rw [h0]
      exact map_zero _
    · change LinearMap.ker ψ ⊔ LinearMap.range f.hom.hom.toLinearMap = ⊤
      rw [Submodule.eq_top_iff']
      intro b
      have hb : b = (b - f.hom.hom (ψ b)) + f.hom.hom (ψ b) := by abel
      rw [hb]
      exact Submodule.add_mem_sup (by
        rw [LinearMap.mem_ker]
        change ψ b - ψ (f.hom.hom (ψ b)) = 0
        rw [hψcomp, sub_self]) (LinearMap.mem_range.mpr ⟨ψ b, rfl⟩)
  -- The kernel of psi is a direct summand of B, hence finite flat.
  have hkerProj : (B : Type) →ₗ[S1779R] LinearMap.ker ψ :=
    LinearMap.codRestrict _ (LinearMap.id - f.hom.hom.toLinearMap.comp ψ) (by
      intro b
      rw [LinearMap.mem_ker]
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
      change ψ b - ψ (f.hom.hom (ψ b)) = 0
      rw [hψcomp, sub_self])
  haveI hkerFlat : Module.Flat S1779R (LinearMap.ker ψ) :=
    Module.Flat.of_retract (Submodule.subtype _) hkerProj (by
      apply LinearMap.ext
      intro k
      apply Subtype.ext
      simp only [hkerProj, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply,
        LinearMap.codRestrict_apply, LinearMap.sub_apply]
      change ((k : B) - f.hom.hom (ψ (k : B))) = (k : B)
      rw [LinearMap.mem_ker.mp k.property, map_zero, sub_zero])
  haveI : IsNoetherianRing S1779R := S1849_isNoetherian
  haveI : IsNoetherian S1779R (B : Type) :=
    isNoetherian_of_isNoetherianRing_of_finite S1779R (B : Type)
  haveI hkerFinite : Module.Finite S1779R (LinearMap.ker ψ) := inferInstance
  -- Rank additivity along B = A + ker psi.
  let eB : (B : Type) ≃ₗ[S1779R]
      (LinearMap.ker ψ × LinearMap.range f.hom.hom.toLinearMap) :=
    (Submodule.prodEquivOfIsCompl (LinearMap.ker ψ)
      (LinearMap.range f.hom.hom.toLinearMap) hcompl).symm
  let eR : LinearMap.range f.hom.hom.toLinearMap ≃ₗ[S1779R] (A : Type) :=
    (LinearEquiv.ofInjective (f.hom.hom.toLinearMap) hinj).symm
  let e : (B : Type) ≃ₗ[S1779R] (LinearMap.ker ψ × (A : Type)) :=
    eB.trans (LinearEquiv.prodCongr (LinearEquiv.refl S1779R (LinearMap.ker ψ)) eR)
  have hrankK : ∀ p : PrimeSpectrum S1779R,
      Module.rankAtStalk (LinearMap.ker ψ) p = 0 := by
    intro p
    have h1 : Module.rankAtStalk (B : Type) p =
        Module.rankAtStalk (LinearMap.ker ψ × (A : Type)) p :=
      congrFun (Module.rankAtStalk_eq_of_equiv e) p
    have h2 : Module.rankAtStalk (LinearMap.ker ψ × (A : Type)) p =
        Module.rankAtStalk (LinearMap.ker ψ) p +
          Module.rankAtStalk (A : Type) p := by
      simpa using congrFun
        (Module.rankAtStalk_prod (R := S1779R) (LinearMap.ker ψ) (A : Type)) p
    have hA : Module.rankAtStalk (A : Type) p = Module.rankAtStalk (B : Type) p :=
      hrank p
    omega
  have hKzero : Module.rankAtStalk (LinearMap.ker ψ) = 0 := funext hrankK
  haveI hsub : Subsingleton (LinearMap.ker ψ) :=
    (Module.rankAtStalk_eq_zero_iff_subsingleton
      (R := S1779R) (M := LinearMap.ker ψ)).mp hKzero
  have hker_bot : LinearMap.ker ψ = ⊥ :=
    Submodule.subsingleton_iff_eq_bot.mp hsub
  have hinjψ : Function.Injective ψ := LinearMap.ker_eq_bot.mp hker_bot
  intro b
  refine ⟨ψ b, ?_⟩
  exact hinjψ (retraction_comp f hinj hrank (ψ b))

/-! ## 6. Formal checks and axiom audit -/

#check S1912K
#check traceDualEquiv
#check traceFunctional
#check retraction
#check retraction_spec
#check trace_eq_of_image
#check retraction_comp
#check S1912_EqualRankInclusion

#print axioms traceDualEquiv
#print axioms retraction_spec
#print axioms trace_eq_of_image
#print axioms retraction_comp
#print axioms S1912_EqualRankInclusion

end LeanFormal.IUT.XiFPaper.S1912EqualRankTraceRetractionActual