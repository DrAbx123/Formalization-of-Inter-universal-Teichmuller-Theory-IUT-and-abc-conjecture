/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1846

# S1846: the missing faithful-flatness input of field 4 at R'

S1842 reduced the fourth field of the six-field fibre functor at the closed point
(0,0) of Spec R' to the statement

  S1842MonoFaithfullyFlat :
  for every mono f : X ⟶ Y of finite etale R'-algebras, Y is faithfully flat
  over X for the X-algebra structure induced by f.

This file proves S1842MonoFaithfullyFlat unconditionally.

The proof is the one suggested in the S1842 header.  Let e : X be the support
idempotent of Y over X, so that Module.support X Y = basicOpen e (S1842) and
f (1 - e) = 0 (S1842).  The algebra decomposes as

  X ≃ C × B,   C = X ⧸ (e),   B = X ⧸ (1 - e),

and f factors through the second projection q : X → B.  If f is mono, the two
maps

  h1 : X × X → X,  (x, x') ↦ x,
  h2 : X × X → X,  (x, x') ↦ (the element whose C-coordinate is that of x' and
                              whose B-coordinate is that of x)

agree after f, hence are equal.  Evaluating at (1, 0) gives 1 = 0 in C, so
e is a unit; being idempotent, e = 1.  Hence Module.support X Y = ⊤.
Since Y is finite flat over X, support ⊤ implies faithful flatness: for a
maximal ideal m, if m • ⊤ = ⊤ then Y ⧸ m • ⊤ = 0 has empty support, while
Module.support_quotient says its support is support Y ∩ zeroLocus m, which
contains the point m.

No sorry, admit, new axiom, Shrink, ULift or PUnit occurs here.

## Verification (session S1846, 2026-11-01)

Compiled with

    lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1846MonoFFActual.olean
      tmp/sheaf/xif/paper/S1846MonoFFActual.lean

-> EXIT=0, no errors, no sorryAx.  Every #print axioms below prints only
[propext, Classical.choice, Quot.sound].
-/

import tmp.sheaf.xif.paper.S1842RPrimeMonoActual
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Etale.Pi

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1846MonoFFActual

open CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1842RPrimeMonoActual

attribute [local instance] S1779PointClosureAlgebra

/-! ## 1. The support idempotent is trivial for a monomorphism -/

/-- **The key algebraic step**: if f : X ⟶ Y is a mono of finite etale
R'-algebras and e is the support idempotent, then e = 1. -/
theorem S1846SupportIdempotent_eq_one {X Y : CommAlgCat.FiniteEtale.{0} S1779R}
    (f : X ⟶ Y) (hf : Mono f) :
    letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
    ∀ (e : (X : Type)), IsIdempotentElem e →
      Module.support (X : Type) (Y : Type) = PrimeSpectrum.basicOpen e → e = 1 := by
  letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
  haveI hST : IsScalarTower S1779R (X : Type) (Y : Type) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change (algebraMap S1779R (Y : Type)) r =
      f.hom.hom ((algebraMap S1779R (X : Type)) r)
    exact (f.hom.hom.commutes r).symm
  intro e he hsupp
  -- (1 - e) kills the unit of Y
  have hf1e : f.hom.hom (1 - e) = 0 := by
    have h := S1842OneSubESmulOne f e he hsupp
    rwa [Algebra.smul_def, mul_one] at h
  -- the quotient by (1 - e)
  let I : Ideal (X : Type) := Ideal.span {e}
  let J : Ideal (X : Type) := Ideal.span {1 - e}
  let C : Type := (X : Type) ⧸ I
  let B : Type := (X : Type) ⧸ J
  -- the product decomposition X ≃ C × B
  let iso : (X : Type) ≃ₐ[S1779R] C × B :=
    AlgEquiv.prodQuotientOfIsIdempotentElem (R := S1779R) (S := (X : Type))
      he he.one_sub (by ring) (he.mul_one_sub_self)
  have iso_snd : ∀ x : (X : Type), (iso x).2 = Ideal.Quotient.mk J x := by
    intro x
    exact AlgEquiv.prodQuotientOfIsIdempotentElem_apply_snd (R := S1779R)
      he he.one_sub (by ring) (he.mul_one_sub_self) x
  -- the quotient map q : X → B
  let q : X.obj → B := Ideal.Quotient.mk J
  have iso_snd_q : ∀ x : (X : Type), (iso x).2 = q x := iso_snd
  -- f factors through q
  have hJker : J ≤ RingHom.ker f.hom.hom := by
    have hmem : (1 - e) ∈ RingHom.ker f.hom.hom := by
      simp [RingHom.mem_ker, hf1e]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  have key : ∀ x x' : (X : Type), q x = q x' → f.hom.hom x = f.hom.hom x' := by
    intro x x' hq
    have hmem : x - x' ∈ J := (Ideal.Quotient.mk_eq_mk_iff_sub_mem x x').mp hq
    have h0 : f.hom.hom (x - x') = 0 := by
      simpa [RingHom.mem_ker] using hJker hmem
    have hsub : f.hom.hom x - f.hom.hom x' = 0 := by
      rw [← map_sub]
      exact h0
    exact sub_eq_zero.mp hsub
  -- the two endomorphisms of X agreeing after f
  let ev (i : Fin 2) : ((j : Fin 2) → (X : Type)) →ₐ[S1779R] (X : Type) :=
    Pi.evalAlgHom S1779R (fun _ : Fin 2 => (X : Type)) i
  let h1' : ((j : Fin 2) → (X : Type)) →ₐ[S1779R] (X : Type) := ev 0
  let h2' : ((j : Fin 2) → (X : Type)) →ₐ[S1779R] (X : Type) :=
    iso.symm.toAlgHom.comp
      (AlgHom.prod
        ((AlgHom.fst S1779R C B).comp (iso.toAlgHom.comp (ev 1)))
        ((AlgHom.snd S1779R C B).comp (iso.toAlgHom.comp (ev 0))))
  -- the product object X × X of the category
  let Zobj : CommAlgCat.FiniteEtale.{0} S1779R :=
    CommAlgCat.FiniteEtale.of S1779R ((j : Fin 2) → (X : Type))
  let h1m : Zobj ⟶ X := CommAlgCat.FiniteEtale.ofHom h1'
  let h2m : Zobj ⟶ X := CommAlgCat.FiniteEtale.ofHom h2'
  -- the two maps agree after f
  have hcomp : h1m ≫ f = h2m ≫ f := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro z
    change f.hom.hom (h1' z) = f.hom.hom (h2' z)
    apply key
    have h1z : q (h1' z) = (iso (z 0)).2 := by
      rw [← iso_snd_q (h1' z)]
      simp [h1', ev]
    have h2z : q (h2' z) = (iso (z 0)).2 := by
      rw [← iso_snd_q (h2' z)]
      have hiso : iso (h2' z) = ((iso (z 1)).1, (iso (z 0)).2) := by
        simp [h2', ev, AlgEquiv.apply_symm_apply]
      rw [hiso]
    rw [h1z, h2z]
  -- mono cancels them
  haveI : Mono f := hf
  have hEq : h1m = h2m := Mono.right_cancellation h1m h2m hcomp
  -- evaluate at (1, 0)
  let z0 : (j : Fin 2) → (X : Type) := fun j => if j = 0 then 1 else 0
  have hz0_zero : z0 0 = (1 : (X : Type)) := by simp [z0]
  have hz0_one : z0 1 = (0 : (X : Type)) := by simp [z0]
  have hval : h1m.hom.hom z0 = h2m.hom.hom z0 :=
    congrArg (fun (φ : Zobj ⟶ X) => φ.hom.hom z0) hEq
  -- hence 1 = 0 in C = X ⧸ (e)
  have hone : (1 : C) = 0 := by
    have hcongr : (iso (h1m.hom.hom z0)).1 = (iso (h2m.hom.hom z0)).1 :=
      congrArg (fun p : C × B => p.1) (congrArg iso hval)
    have hleft : (iso (h1m.hom.hom z0)).1 = 1 := by
      change (iso (h1' z0)).1 = 1
      simp [h1', ev, hz0_zero]
    have hright : (iso (h2m.hom.hom z0)).1 = 0 := by
      change (iso (h2' z0)).1 = 0
      simp [h2', ev, hz0_zero, hz0_one, AlgEquiv.apply_symm_apply]
    rw [hleft, hright] at hcongr
    exact hcongr
  -- so e is a unit, hence e = 1
  have hmem : (1 : (X : Type)) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hone
  have htop : I = ⊤ := Ideal.eq_top_iff_one I |>.mpr hmem
  have hunit : IsUnit e := by
    have hspan : Ideal.span {e} = ⊤ := htop
    exact Ideal.span_singleton_eq_top.mp hspan
  exact (IsIdempotentElem.iff_eq_one_of_isUnit hunit).mp he

/-! ## 2. Main theorem: a mono of finite etale algebras is faithfully flat -/

/-- **S1842MonoFaithfullyFlat**, proved unconditionally. -/
theorem S1846MonoFaithfullyFlat : S1842MonoFaithfullyFlat := by
  intro X Y f hf
  letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
  haveI hST : IsScalarTower S1779R (X : Type) (Y : Type) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change (algebraMap S1779R (Y : Type)) r =
      f.hom.hom ((algebraMap S1779R (X : Type)) r)
    exact (f.hom.hom.commutes r).symm
  obtain ⟨e, he, hsupp⟩ := S1842ExistsIdempotentSupport f
  have he1 : e = 1 := S1846SupportIdempotent_eq_one f hf e he hsupp
  -- the support is everything
  have hsupp_top : Module.support (X : Type) (Y : Type) = ⊤ := by
    rw [hsupp, he1, PrimeSpectrum.basicOpen_one]
    simp
  -- Y is finite and flat over X
  haveI hFinY : Module.Finite S1779R (Y : Type) := Y.property.left
  haveI hFinX : Module.Finite S1779R (X : Type) := X.property.left
  haveI hFinXY : Module.Finite (X : Type) (Y : Type) :=
    Module.Finite.of_restrictScalars_finite S1779R (X : Type) (Y : Type)
  haveI hEtaleXY : Algebra.Etale (X : Type) (Y : Type) := S1842EtaleOfHom f
  haveI hFlatXY : Module.Flat (X : Type) (Y : Type) := inferInstance
  -- support ⊤ + finite flat = faithfully flat
  refine Module.FaithfullyFlat.mk ?_
  intro m hm htop
  let p : PrimeSpectrum (X : Type) := ⟨m, hm.isPrime⟩
  have hp : p ∈ Module.support (X : Type) (Y : Type) := by
    rw [hsupp_top]
    exact Set.mem_univ p
  have hpq : p ∈ Module.support (X : Type)
      ((Y : Type) ⧸ (m • (⊤ : Submodule (X : Type) (Y : Type)))) := by
    rw [Module.support_quotient (M := (Y : Type)) m]
    refine ⟨hp, ?_⟩
    rw [PrimeSpectrum.mem_zeroLocus p (m : Set (X : Type))]
  haveI hsub : Subsingleton ((Y : Type) ⧸ (m • (⊤ : Submodule (X : Type) (Y : Type)))) := by
    rw [Submodule.Quotient.subsingleton_iff]
    exact htop
  have hempty : Module.support (X : Type)
      ((Y : Type) ⧸ (m • (⊤ : Submodule (X : Type) (Y : Type)))) = ∅ :=
    Module.support_eq_empty
  rw [hempty] at hpq
  exact hpq

/-! ## 3. Consumers: the unconditional field 4 at R' -/

/-- The concrete S1835 target, now unconditional. -/
theorem S1846BCInjectiveOnMonos : S1835BCInjectiveOnMonos :=
  S1842BCInjectiveOnMonos_of_monoFaithfullyFlat S1846MonoFaithfullyFlat

/-- **Field 4** of the six-field fibre functor, now unconditional. -/
theorem S1846BCPreservesEpis : S1835BCPreservesEpis :=
  S1842BCPreservesEpis_of_monoFaithfullyFlat S1846MonoFaithfullyFlat

/-- The same conclusion in the form consumed by S1835's six-field assembly. -/
theorem S1846PreservesEpis : Functor.PreservesEpimorphisms S1835Fiber :=
  S1842PreservesEpis_of_monoFaithfullyFlat S1846MonoFaithfullyFlat

/-! ## 4. Checks and axiom audit -/

#check S1846SupportIdempotent_eq_one
#check S1846MonoFaithfullyFlat
#check S1846BCInjectiveOnMonos
#check S1846BCPreservesEpis
#check S1846PreservesEpis

#print axioms S1846SupportIdempotent_eq_one
#print axioms S1846MonoFaithfullyFlat
#print axioms S1846BCInjectiveOnMonos
#print axioms S1846BCPreservesEpis
#print axioms S1846PreservesEpis

end LeanFormal.IUT.XiFPaper.S1846MonoFFActual