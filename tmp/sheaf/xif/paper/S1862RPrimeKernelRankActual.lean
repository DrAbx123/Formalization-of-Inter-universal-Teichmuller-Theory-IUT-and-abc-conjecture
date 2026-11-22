/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1862

# S1862: the residue-fibre kernel-vanishing and the closed-fibre rank equality at R'

S1849 split the residue-fibre reflection statement `S1848FReflectsIsoMaps` exactly into

* `S1849KernelVanishes` (the injectivity half), and
* `S1849SurjectiveOnInjective` (the surjectivity half),

and recorded its route theorem `S1848FReflectsIsoMaps_of_route` taking three inputs:
`S1849KernelVanishes`, the *closed-fibre rank equality* (hii), and the trace-form
`S1849EqualRankInclusion`.

This file discharges the rank equality unconditionally, and proves the kernel-vanishing
half from the precise remaining commutative-algebra input, which is isolated here as
`S1862FiberPurity` and is not available in Mathlib 4.32.2.

## What is proved unconditionally here

1. **The rank at the closed point is the fibre dimension** (`S1862_rankAtStalk_m_eq_finrank`):
   for every finite flat `R'`-module `M`,
   `rankAtStalk M m = finrank F' (F' (x)_{R'} M)`.
   The point is that `m = ker (R' -> F')` is the kernel of the `R'`-algebra structure of `F'`
   (`S1862_comap_bot_eq_m`), so `Module.rankAtStalk_baseChange` applies.

2. **The closed-fibre rank equality** (`S1862_rankAtStalk_eq`): for every map
   `f : A --> B` of finite etale `R'`-algebras with `F' (x)_{R'} f` an isomorphism and
   every prime `p` of `R'`,

     `rankAtStalk A p = rankAtStalk B p`.

   This is precisely the hypothesis `hii` of `S1848FReflectsIsoMaps_of_route`.
   The proof uses the domain `R'` (S1849) and the `F'`-fibre isomorphism to compute
   the (constant) rank of `A` and `B` at the closed point.

3. **The kernel is killed by the closed point** (`S1862_ker_le_smul`): for `f : A --> B`
   with `F' (x)_{R'} f` injective, the `R'`-linear kernel `J` of `f` satisfies
   `J <= m * A`.  (No flatness is used.)

4. **The precise remaining input** (`S1862FiberPurity`): `J (x)_{R'} F' = 0`, equivalently
   `J = m * J`.  This is the Tor/purity step which `S1848`'s header describes as
   "J (x)_{R'} F' = 0 (flatness of B)".  It is *not* a formal consequence of flatness of
   the codomain alone; what is needed is that the kernel is a pure ideal of `A`.
   The reduction `S1849KernelVanishes_of_fiberPurity` proves `S1849KernelVanishes`
   from it, using Nakayama's trick at `m` and torsion-freeness of `A`
   (`S1862_eq_bot_of_smul_eq`).

## Consumers

* `S1848FReflectsIsoMaps_of_route'`: the S1849 route theorem with the rank-equality
  input `hii` *eliminated* --- it takes only kernel vanishing and trace-form duality.
* `S1848FReflectsIsoMaps_of_purity`: the full residue-fibre statement from the single
  remaining input `S1862FiberPurity` plus trace-form duality.

## Honest boundary

No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit` occurs in this file.
Everything asserted as a theorem is proved.  `S1862FiberPurity` is a plain `Prop` with
no inhabitant and is used only as the explicit hypothesis of
`S1849KernelVanishes_of_fiberPurity` and `S1848FReflectsIsoMaps_of_purity`.

The reason `S1862FiberPurity` cannot be derived from `Module.Flat R' B` alone is that
`0 -> J -> A -> B` is only exact at `A`: `f` is not assumed surjective, so `B` is not
the cokernel of `J -> A` and `Tor_1(B, F')` does not control `J (x) F'`.  What the
argument needs is purity of the ideal `J` in `A` (equivalently flatness of the image
`A/J` over `A`), which in this finite-etale situation is the statement that the image of
a finite etale algebra map is clopen.  Mathlib 4.32.2 has neither this statement nor the
general Tor input that would derive it from flatness of `B`.
-/

import tmp.sheaf.xif.paper.S1849RPrimeReflectCompleteActual
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Pure

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false

namespace LeanFormal.IUT.XiFPaper.S1862RPrimeKernelRankActual

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1848RPrimeReflectActual
open LeanFormal.IUT.XiFPaper.S1849RPrimeReflectCompleteActual
open LeanFormal.IUT.XiFPaper.S1842RPrimeMonoActual
open LeanFormal.IUT.XiFPaper.S1846MonoFFActual

attribute [local instance] S1848PointAlgebra

set_option autoImplicit false

/-! ## 1. The closed point as the kernel of `R' -> F'` -/

/-- The closed point `(0,0)` of `Spec R'`, as a prime spectrum element. -/
def S1862ClosedPoint : PrimeSpectrum S1779R := ⟨S1849m, inferInstance⟩

theorem S1862ClosedPoint_asIdeal : S1862ClosedPoint.asIdeal = S1849m := rfl

/-- The closed point `(0,0)` is the prime of `R'` cut out by the structure map to `F'`. -/
theorem S1862_comap_bot_eq_m :
    (⊥ : PrimeSpectrum S1779K).comap (algebraMap S1779R S1779K) = S1862ClosedPoint := by
  ext x
  show (algebraMap S1779R S1779K) x = 0 ↔ S1779Point x = 0
  rfl

/-! ## 2. The rank at the closed point is the fibre dimension -/

/-- For a finite flat `R'`-module `M`, the rank at the closed point equals the
dimension of the residue fibre `F' (x)_{R'} M`. -/
theorem S1862_rankAtStalk_m_eq_finrank (M : Type) [AddCommGroup M] [Module S1779R M]
    [Module.Finite S1779R M] [Module.Flat S1779R M] :
    Module.rankAtStalk M S1862ClosedPoint = Module.finrank S1779K (S1779K ⊗[S1779R] M) := by
  rw [← S1862_comap_bot_eq_m]
  rw [← Module.rankAtStalk_baseChange (M := M) (S := S1779K)
    (p := (⊥ : PrimeSpectrum S1779K))]
  simp

/-! ## 3. The closed-fibre rank equality (S1849's hii) -/

/-- **The closed-fibre rank equality.**  If `F' (x)_{R'} f` is an isomorphism, then `A` and
`B` have the same rank at every prime of `R'`.  This is exactly the hypothesis `hii`
of `S1848FReflectsIsoMaps_of_route`. -/
theorem S1862_rankAtStalk_eq {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B)
    (hf : IsIso ((S1848BCF).map f)) (p : PrimeSpectrum S1779R) :
    Module.rankAtStalk (A : Type) p = Module.rankAtStalk (B : Type) p := by
  haveI hFA : Module.Finite S1779R (A : Type) := A.property.left
  haveI hFB : Module.Finite S1779R (B : Type) := B.property.left
  haveI hEA : Algebra.Etale S1779R (A : Type) := A.property.right
  haveI hEB : Algebra.Etale S1779R (B : Type) := B.property.right
  haveI hFlatA : Module.Flat S1779R (A : Type) := inferInstance
  haveI hFlatB : Module.Flat S1779R (B : Type) := inferInstance
  -- The fibre map is bijective.
  have hbij : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id S1779K S1779K) f.hom.hom) := by
    have hb := S1848bijective_of_isIso ((S1848BCF).map f) hf
    simpa [S1848BCF, CommAlgCat.FiniteEtale.baseChange, CommAlgCat.FiniteEtale.ofHom] using hb
  -- Hence the two fibres have the same dimension.
  have hfin : Module.finrank S1779K (S1779K ⊗[S1779R] (A : Type)) =
      Module.finrank S1779K (S1779K ⊗[S1779R] (B : Type)) :=
    (AlgEquiv.ofBijective _ hbij).toLinearEquiv.finrank_eq
  have hAp : Module.rankAtStalk (A : Type) p = Module.finrank S1779R (A : Type) := by
    rw [Module.rankAtStalk_eq (M := (A : Type)) p]
    exact Ideal.finrank_fiber_eq_finrank (R := S1779R) (M := (A : Type)) p.asIdeal
  have hAm : Module.rankAtStalk (A : Type) S1862ClosedPoint = Module.finrank S1779R (A : Type) := by
    rw [Module.rankAtStalk_eq (M := (A : Type)) S1862ClosedPoint]
    exact Ideal.finrank_fiber_eq_finrank (R := S1779R) (M := (A : Type)) S1849m
  have hAfib : Module.rankAtStalk (A : Type) S1862ClosedPoint =
      Module.finrank S1779K (S1779K ⊗[S1779R] (A : Type)) :=
    S1862_rankAtStalk_m_eq_finrank (M := (A : Type))
  have hBp : Module.rankAtStalk (B : Type) p = Module.finrank S1779R (B : Type) := by
    rw [Module.rankAtStalk_eq (M := (B : Type)) p]
    exact Ideal.finrank_fiber_eq_finrank (R := S1779R) (M := (B : Type)) p.asIdeal
  have hBm : Module.rankAtStalk (B : Type) S1862ClosedPoint = Module.finrank S1779R (B : Type) := by
    rw [Module.rankAtStalk_eq (M := (B : Type)) S1862ClosedPoint]
    exact Ideal.finrank_fiber_eq_finrank (R := S1779R) (M := (B : Type)) S1849m
  have hBfib : Module.rankAtStalk (B : Type) S1862ClosedPoint =
      Module.finrank S1779K (S1779K ⊗[S1779R] (B : Type)) :=
    S1862_rankAtStalk_m_eq_finrank (M := (B : Type))
  calc Module.rankAtStalk (A : Type) p
      = Module.finrank S1779R (A : Type) := hAp
    _ = Module.rankAtStalk (A : Type) S1862ClosedPoint := hAm.symm
    _ = Module.finrank S1779K (S1779K ⊗[S1779R] (A : Type)) := hAfib
    _ = Module.finrank S1779K (S1779K ⊗[S1779R] (B : Type)) := hfin
    _ = Module.rankAtStalk (B : Type) S1862ClosedPoint := hBfib.symm
    _ = Module.finrank S1779R (B : Type) := hBm
    _ = Module.rankAtStalk (B : Type) p := hBp.symm

/-! ## 4. The kernel is killed by the closed point -/

/-- The `R'`-linear kernel of the algebra map underlying `f`. -/
def S1862Ker {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B) :
    Submodule S1779R (A : Type) :=
  LinearMap.ker (f.hom.hom.toLinearMap)

theorem S1862_mem_ker_iff {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B)
    (x : (A : Type)) : x ∈ S1862Ker f ↔ f.hom.hom x = 0 := Iff.rfl

/-- **The kernel of the residue-fibre map is contained in `m A`.** -/
theorem S1862_ker_le_smul {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B)
    (hf : IsIso ((S1848BCF).map f)) :
    S1862Ker f ≤ S1849m • (⊤ : Submodule S1779R (A : Type)) := by
  haveI hFA : Module.Finite S1779R (A : Type) := A.property.left
  haveI hFB : Module.Finite S1779R (B : Type) := B.property.left
  haveI hEA : Algebra.Etale S1779R (A : Type) := A.property.right
  haveI hEB : Algebra.Etale S1779R (B : Type) := B.property.right
  have hbij : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id S1779K S1779K) f.hom.hom) := by
    have hb := S1848bijective_of_isIso ((S1848BCF).map f) hf
    simpa [S1848BCF, CommAlgCat.FiniteEtale.baseChange, CommAlgCat.FiniteEtale.ofHom] using hb
  intro x hx
  have hx0 : f.hom.hom x = 0 := hx
  -- The element `1 (x) x` dies in `F' (x)_{R'} A`.
  have hA : (1 : S1779K) ⊗ₜ[S1779R] x = 0 := by
    apply hbij.1
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hx0, TensorProduct.tmul_zero,
      map_zero]
  -- Transport it to `(R' / m) (x)_{R'} A`.
  have hB : (1 : S1779R ⧸ S1849m) ⊗ₜ[S1779R] x = 0 := by
    have he1 : S1849FEquivQuot.toLinearEquiv (1 : S1779K) = 1 :=
      map_one S1849FEquivQuot
    have hcongr : (TensorProduct.congr S1849FEquivQuot.toLinearEquiv
          (LinearEquiv.refl S1779R (A : Type)))
        ((1 : S1779K) ⊗ₜ[S1779R] x) = 0 := by
      rw [hA, map_zero]
    rwa [TensorProduct.congr_tmul, LinearEquiv.refl_apply, he1] at hcongr
  -- Hence `x` is zero modulo `m A`.
  have hC : (Submodule.Quotient.mk x :
      (A : Type) ⧸ (S1849m • (⊤ : Submodule S1779R (A : Type)))) = 0 := by
    have h := congrArg (TensorProduct.quotTensorEquivQuotSMul (A : Type) S1849m) hB
    simpa using h
  exact (Submodule.Quotient.mk_eq_zero
    (S1849m • (⊤ : Submodule S1779R (A : Type)))).mp hC

/-- **Nakayama's trick plus torsion-freeness.**  A finitely generated torsion-free
`R'`-module `N` with `N = m N` is zero.  This is the step which turns the fibre
purity of the kernel into the vanishing of the kernel. -/
theorem S1862_eq_bot_of_smul_eq {M : Type} [AddCommGroup M] [Module S1779R M]
    [Module.IsTorsionFree S1779R M]
    (N : Submodule S1779R M) (hNfg : N.FG) (hN : N = S1849m • N) : N = ⊥ := by
  obtain ⟨r, hr1, hrN⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul S1849m N hNfg hN.le
  have hr_ne : r ≠ 0 := by
    intro h
    have h1 : (1 : S1779R) ∈ S1849m := by
      have h2 : r - 1 ∈ S1849m := hr1
      rw [h] at h2
      simpa using S1849m.neg_mem h2
    exact S1849m_isMaximal.ne_top (Ideal.eq_top_iff_one S1849m |>.mpr h1)
  have hrreg : IsRegular r :=
    isRegular_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero hr_ne)
  have hsmul : IsSMulRegular M r := hrreg.isSMulRegular
  rw [eq_bot_iff]
  intro x hx
  have h0 : r • x = 0 := hrN x hx
  have h' : r • x = r • (0 : M) := by rw [h0, smul_zero]
  exact hsmul h'

/-- **The precise remaining commutative-algebra input** (isolated from the S1848/S1849
route).  For a map of finite etale `R'`-algebras whose residue fibre is an isomorphism,
the kernel `J` of the underlying algebra map is `m`-divisible, `J = m J`;
equivalently `J (x)_{R'} F' = 0`.  This is the Tor/purity step which is *not* a formal
consequence of flatness of the codomain alone and is not available in Mathlib 4.32.2. -/
def S1862FiberPurity : Prop :=
  ∀ {A B : CommAlgCat.FiniteEtale.{0} S1779R} (f : A ⟶ B),
    IsIso ((S1848BCF).map f) → S1862Ker f = S1849m • S1862Ker f

/-- **The kernel-vanishing half** (S1849's `S1849KernelVanishes`) from the fibre-purity
input. -/
theorem S1849KernelVanishes_of_fiberPurity (h : S1862FiberPurity) : S1849KernelVanishes := by
  intro A B f hf
  haveI hFA : Module.Finite S1779R (A : Type) := A.property.left
  haveI hEA : Algebra.Etale S1779R (A : Type) := A.property.right
  haveI hFlatA : Module.Flat S1779R (A : Type) := inferInstance
  have hNfg : (S1862Ker f).FG := by
    haveI : IsNoetherianRing S1779R := S1849_isNoetherian
    exact Module.Finite.iff_fg.mp inferInstance
  have hJ : S1862Ker f = ⊥ := S1862_eq_bot_of_smul_eq (S1862Ker f) hNfg (h f hf)
  rw [S1862Ker, LinearMap.ker_eq_bot] at hJ
  intro x y hxy
  exact hJ hxy

/-! ## 5. The route theorem with the rank equality eliminated -/

/-- `S1848FReflectsIsoMaps` from kernel vanishing and trace-form duality: the
closed-fibre rank equality is now supplied unconditionally. -/
theorem S1848FReflectsIsoMaps_of_route' (hker : S1849KernelVanishes)
    (hiii : S1849EqualRankInclusion) : S1848FReflectsIsoMaps :=
  S1848FReflectsIsoMaps_of_route hker (fun f hf p => S1862_rankAtStalk_eq f hf p) hiii

/-- The full residue-fibre statement from the single remaining commutative-algebra
input and trace-form duality. -/
theorem S1848FReflectsIsoMaps_of_purity (h : S1862FiberPurity)
    (hiii : S1849EqualRankInclusion) : S1848FReflectsIsoMaps :=
  S1848FReflectsIsoMaps_of_route' (S1849KernelVanishes_of_fiberPurity h) hiii

/-! ## 6. Formal checks and axiom audit -/

#check S1862_comap_bot_eq_m
#check S1862_rankAtStalk_m_eq_finrank
#check S1862_rankAtStalk_eq
#check S1862_ker_le_smul
#check S1862_eq_bot_of_smul_eq
#check S1862FiberPurity
#check S1849KernelVanishes_of_fiberPurity
#check S1848FReflectsIsoMaps_of_route'
#check S1848FReflectsIsoMaps_of_purity

#print axioms S1862_comap_bot_eq_m
#print axioms S1862_rankAtStalk_m_eq_finrank
#print axioms S1862_rankAtStalk_eq
#print axioms S1862_ker_le_smul
#print axioms S1862_eq_bot_of_smul_eq
#print axioms S1849KernelVanishes_of_fiberPurity
#print axioms S1848FReflectsIsoMaps_of_route'
#print axioms S1848FReflectsIsoMaps_of_purity

end LeanFormal.IUT.XiFPaper.S1862RPrimeKernelRankActual

