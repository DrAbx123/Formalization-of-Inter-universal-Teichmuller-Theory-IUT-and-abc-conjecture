/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1901

# S1901: the equal-rank inclusion at `R'`, via trace duality and the rank equality

S1849 isolated the last missing input of the S1848 route as `S1849EqualRankInclusion`:

  an injective map `f : A ⟶ B` of finite etale `R'`-algebras which have equal rank at every
  prime of `R'` is surjective,

and `S1862` removed the closed-fibre rank equality from the hypotheses of the route
(`S1862_rankAtStalk_eq`), leaving only kernel vanishing and the trace-form input.

This file *proves* `S1849EqualRankInclusion` from the two inputs produced by S1860 and S1862:
trace duality for finite etale `R'`-algebras (`S1859ProjectiveTraceDuality_proof`, S1860) and the
closed-fibre rank equality (`S1862_rankAtStalk_eq`, S1862).

## Proof

Let `K = R'_⊥` be the residue field of the generic point of `Spec R'` (the localisation of `R'`
at `⊥`); since `R'` is a domain, `K` is a field and `R' → K` is injective.

1. *(Trace duality over `R'`.)*  For `b : B`, the map `a ↦ Tr_{B/R'}(b * f a)` is an
   `R'`-linear functional on `A`; by `S1859ProjectiveTraceDuality_proof` there is `a₀ : A`
   with `Tr_{A/R'}(a₀ * a) = Tr_{B/R'}(b * f a)` for all `a : A`.
2. *(Generic fibre.)*  Base changing to `K` the inclusion `f` becomes an injective
   `K`-algebra map `A_K → B_K`; the rank equality at the generic point makes the two
   `K`-vector spaces equidimensional, so it is an algebra equivalence `e : A_K ≃ₐ[K] B_K`.
   Trace invariance under `e` (`Algebra.trace_eq_of_algEquiv`) upgrades the duality identity
   to `Tr_{A_K}(a₀ * x) = Tr_{A_K}(e⁻¹(b) * x)` for all `x : A_K`, and the trace form of the
   finite etale `K`-algebra `A_K` is nondegenerate by S1860's unit-determinant criterion
   (`isUnit_det_traceMatrix_of_isLocalRing`, `bilinForm_bijective_of_isUnit_det`).  Hence
   `e(a₀ ⊗ 1) = b ⊗ 1`, i.e. `f a₀ ⊗ 1 = b ⊗ 1` in `B_K`.
3. *(Torsion-freeness.)*  `B` is flat, hence torsion-free over the domain `R'`, so
   `B → B_K`, `y ↦ 1 ⊗ y`, is injective; therefore `b = f a₀`, and `f` is surjective.

## Consumers

* `S1901_S1849SurjectiveOnInjective`: the surjectivity half `S1849SurjectiveOnInjective` of the
  residue-fibre reflection statement, using S1862's closed-fibre rank equality.
* `S1901_S1848FReflectsIsoMaps_of_kernelVanishes`: S1862's route theorem
  `S1848FReflectsIsoMaps_of_route'` with the trace-form input now discharged, i.e. the
  residue-fibre reflection statement from kernel vanishing alone.
* `S1901_S1848FReflectsIsoMaps_of_purity`: the same from S1862's single remaining
  commutative-algebra input `S1862FiberPurity`.

## Honest boundary

No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit` occurs in this file.  Everything
asserted as a theorem is proved.  The proposition `S1849KernelVanishes` occurs only as the
explicit hypothesis of the last consumer; it is still open, at the fibre-purity level
`S1862FiberPurity` (see S1862).  The two inputs consumed from earlier files are theorems there:
trace duality (`S1859ProjectiveTraceDuality_proof`, S1860) and the closed-fibre rank equality
(`S1862_rankAtStalk_eq`, S1862).

## Verification

Compiled with

    lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1901EqualRankTraceActual.olean
      tmp/sheaf/xif/paper/S1901EqualRankTraceActual.lean

-> EXIT=0, no errors, no `sorryAx`; every `#print axioms` below prints only
`[propext, Classical.choice, Quot.sound]`.

Note on options (S1901, recorded for maintainers): this file must *not* set
`backward.isDefEq.respectTransparency false`.  For `K = Localization.AtPrime (⊥ : Ideal R')`
(an `OreLocalization` in Mathlib 4.32.2) that option makes the definitional-equality checks for
the tensor types `K ⊗[R'] A` diverge: elaboration dies with a deterministic heartbeat timeout
at `whnf`.  Raising `synthInstance.maxHeartbeats` is equally counterproductive, since the
`Module.Free.chooseBasis` search then spends its whole budget on the same problem.  The
trace-form criterion is therefore stated for an *abstract* field `K` and only instantiated at
`K = R'_⊥`, which keeps every instance search cheap.
-/

import tmp.sheaf.xif.paper.S1862RPrimeKernelRankActual
import tmp.sheaf.xif.paper.S1860TraceDualityActual

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
open scoped TensorProduct

namespace LeanFormal.IUT.XiFPaper.S1901EqualRankTraceActual

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1848RPrimeReflectActual
open LeanFormal.IUT.XiFPaper.S1849RPrimeReflectCompleteActual
open LeanFormal.IUT.XiFPaper.S1862RPrimeKernelRankActual
open LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual
open LeanFormal.IUT.XiFPaper.S1860TraceDualityActual

set_option autoImplicit false

/-! ## 1. Finite flat modules over `R'` are projective -/

/-- A finite flat module over the Noetherian ring `R'` is projective: it is finitely presented,
and finitely presented flat modules are projective. -/
theorem S1901_projective_of_finite_flat (M : Type) [AddCommGroup M] [Module S1779R M]
    [Module.Finite S1779R M] [Module.Flat S1779R M] : Module.Projective S1779R M := by
  haveI : Module.FinitePresentation S1779R M :=
    Module.finitePresentation_of_finite S1779R M
  exact Module.Flat.projective_of_finitePresentation

/-! ## 2. The generic point of `Spec R'` -/

/-- The localisation of `R'` at the zero ideal, i.e. the residue field of the generic point. -/
abbrev S1901K : Type := Localization.AtPrime (⊥ : Ideal S1779R)

instance S1901K_isFractionRing : IsFractionRing S1779R S1901K := by
  simpa [Ideal.primeCompl_bot] using
    (Localization.isLocalization (M := (⊥ : Ideal S1779R).primeCompl))

instance S1901K_field : Field S1901K := IsFractionRing.toField S1779R

theorem S1901K_algebraMap_injective : Function.Injective (algebraMap S1779R S1901K) :=
  IsFractionRing.injective S1779R S1901K

/-- The trace form of the generic fibre is nondegenerate: it is bijective as a map into the
dual, by the unit-determinant criterion of S1860 applied over the field `K`. -/
theorem S1901_traceForm_bijective_generic {K : Type} [Field K] [Algebra S1779R K]
    (A : CommAlgCat.FiniteEtale.{0} S1779R)
    [Module.Finite K (K ⊗[S1779R] (A : Type))]
    [Module.Flat K (K ⊗[S1779R] (A : Type))]
    [Algebra.Etale K (K ⊗[S1779R] (A : Type))]
    [Module.Free K (K ⊗[S1779R] (A : Type))] :
    Function.Bijective
      (Algebra.traceForm K (K ⊗[S1779R] (A : Type))) := by
  have hdet := isUnit_det_traceMatrix_of_isLocalRing (R := K)
    (A := K ⊗[S1779R] (A : Type)) (Module.Free.chooseBasis K _)
  refine bilinForm_bijective_of_isUnit_det (Module.Free.chooseBasis K _)
    (Algebra.traceForm K (K ⊗[S1779R] (A : Type))) ?_
  simpa [Algebra.traceMatrix_of_basis] using hdet

/-! ## 3. The trace comparison in the generic fibre -/

section TraceComparison

universe u v

variable {R : Type u} {A : Type v} {B : Type v} {S : Type u}
  [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [Field S] [Algebra R S]
  [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]
  [Module.Flat R B] [Module.Flat R S]
  [Module.Finite S (S ⊗[R] A)] [Module.Flat S (S ⊗[R] A)] [Module.Free S (S ⊗[R] A)]
  [Module.Finite S (S ⊗[R] B)] [Module.Flat S (S ⊗[R] B)] [Module.Free S (S ⊗[R] B)]

/-- **The trace comparison.**  Let `R → S` be an injective map to a field, `f : A → B` an
injective map of `R`-algebras which becomes equidimensional after base change to `S`, and let
`a₀ : A`, `b : B` satisfy `Tr_{A/R}(a₀ * x) = Tr_{B/R}(b * f x)` for all `x : A`.  If the
trace form of `S ⊗ A` is nondegenerate, then `f a₀ = b`: the base change of `f` to the field
`S` is an algebra equivalence, and the trace of `b` is detected there; `B` is torsion-free
over `R`, so the equality descends. -/
theorem S1901_trace_comparison
    (halg : Function.Injective (algebraMap R S))
    (f : A →ₐ[R] B) (hinj : Function.Injective f)
    (hfin : Module.finrank S (S ⊗[R] A) = Module.finrank S (S ⊗[R] B))
    (hnondeg : ∀ x : S ⊗[R] A,
      (∀ y : S ⊗[R] A, Algebra.trace S (S ⊗[R] A) (x * y) = 0) → x = 0)
    (b : B) (a0 : A)
    (hA0 : ∀ x : A, algebraTrace (R := R) (A := A) (a0 * x) =
      algebraTrace (R := R) (A := B) (b * f x)) :
    f a0 = b := by
  -- the base change of `f` and its bijectivity
  let Φ : S ⊗[R] A →ₐ[S] S ⊗[R] B := Algebra.TensorProduct.lTensor (A := S) f
  have hΦ_tmul : ∀ (s : S) (a : A), Φ (s ⊗ₜ[R] a) = s ⊗ₜ[R] f a := by
    intro s a
    simp [Φ]
  have hlin : Φ.toLinearMap =
      TensorProduct.map (LinearMap.id : S →ₗ[R] S) f.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s a => simp [Φ]
    | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  have hΦ_inj : Function.Injective Φ := by
    have hinj_lin : Function.Injective
        (TensorProduct.map (LinearMap.id : S →ₗ[R] S) f.toLinearMap) := by
      have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S) (f := f.toLinearMap)
        (by simpa using hinj)
      simpa [LinearMap.lTensor_def] using h
    intro x y hxy
    apply hinj_lin
    rw [← hlin]
    exact hxy
  haveI : FiniteDimensional S (S ⊗[R] A) := ‹Module.Finite S (S ⊗[R] A)›
  haveI : FiniteDimensional S (S ⊗[R] B) := ‹Module.Finite S (S ⊗[R] B)›
  have hΦ_surj : Function.Surjective Φ := by
    have hker : LinearMap.ker Φ.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr hΦ_inj
    have hk : Module.finrank S ↥(LinearMap.ker Φ.toLinearMap) = 0 := by
      rw [hker]
      simp
    have hrange : Module.finrank S ↥(LinearMap.range Φ.toLinearMap) =
        Module.finrank S (S ⊗[R] A) := by
      have h := LinearMap.finrank_range_add_finrank_ker Φ.toLinearMap
      rw [hk, add_zero] at h
      exact h
    have htop : LinearMap.range Φ.toLinearMap = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [hrange, hfin]
    intro y
    have hy : y ∈ LinearMap.range Φ.toLinearMap := by
      rw [htop]
      exact Submodule.mem_top
    exact LinearMap.mem_range.mp hy
  -- the algebra equivalence of the fibres
  set e : S ⊗[R] A ≃ₐ[S] S ⊗[R] B := AlgEquiv.ofBijective Φ ⟨hΦ_inj, hΦ_surj⟩ with he
  have he_apply : ∀ x : S ⊗[R] A, e x = Φ x := fun x => rfl
  have he_tmul : ∀ a : A, e ((1 : S) ⊗ₜ[R] a) = (1 : S) ⊗ₜ[R] f a := by
    intro a
    rw [he_apply]
    exact hΦ_tmul 1 a
  -- the preimage of `b ⊗ 1`
  obtain ⟨c, hc⟩ : ∃ c : S ⊗[R] A, e c = (1 : S) ⊗ₜ[R] b :=
    ⟨e.symm ((1 : S) ⊗ₜ[R] b), AlgEquiv.apply_symm_apply _ _⟩
  -- the key identity on the spanning set
  have hbase : ∀ a : A, Algebra.trace S (S ⊗[R] A) (c * ((1 : S) ⊗ₜ[R] a)) =
      Algebra.trace S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a0 * ((1 : S) ⊗ₜ[R] a)) := by
    intro a
    have hL : Algebra.trace S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a0 * ((1 : S) ⊗ₜ[R] a)) =
        algebraMap R S (algebraTrace (R := R) (A := A) (a0 * a)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        ← algebraTrace_eq_trace (R := S) (A := S ⊗[R] A)]
      exact BaseChange.algebraTrace_baseChange (R := R) (A := A) (S := S) (x := a0 * a)
    have hR : Algebra.trace S (S ⊗[R] A) (c * ((1 : S) ⊗ₜ[R] a)) =
        algebraMap R S (algebraTrace (R := R) (A := A) (a0 * a)) := by
      have hstep : Algebra.trace S (S ⊗[R] A) (c * ((1 : S) ⊗ₜ[R] a)) =
          Algebra.trace S (S ⊗[R] B) (e (c * ((1 : S) ⊗ₜ[R] a))) :=
        (Algebra.trace_eq_of_algEquiv e (c * ((1 : S) ⊗ₜ[R] a))).symm
      rw [hstep, map_mul e c ((1 : S) ⊗ₜ[R] a), hc, he_tmul a,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        ← algebraTrace_eq_trace (R := S) (A := S ⊗[R] B)]
      rw [BaseChange.algebraTrace_baseChange (R := R) (A := B) (S := S) (x := b * f a), hA0 a]
    exact (hR).trans (hL).symm
  -- hence for all `y`
  have hkey : ∀ y : S ⊗[R] A, Algebra.trace S (S ⊗[R] A) (c * y) =
      Algebra.trace S (S ⊗[R] A) ((1 : S) ⊗ₜ[R] a0 * y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s a =>
        have hs : (s ⊗ₜ[R] a : S ⊗[R] A) = s • ((1 : S) ⊗ₜ[R] a) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hs, Algebra.mul_smul_comm, Algebra.mul_smul_comm, map_smul, map_smul, hbase a]
    | add x y hx hy => rw [mul_add, mul_add, map_add, map_add, hx, hy]
  -- so `c = a₀ ⊗ 1`
  have hc_eq : c = (1 : S) ⊗ₜ[R] a0 := by
    refine sub_eq_zero.mp (hnondeg (c - (1 : S) ⊗ₜ[R] a0) ?_)
    intro y
    rw [sub_mul, map_sub, hkey y, sub_self]
  -- and hence `b = f a₀` by torsion-freeness of `B`
  have hb : (1 : S) ⊗ₜ[R] b = (1 : S) ⊗ₜ[R] f a0 := by
    calc (1 : S) ⊗ₜ[R] b = e c := hc.symm
      _ = e ((1 : S) ⊗ₜ[R] a0) := by rw [hc_eq]
      _ = (1 : S) ⊗ₜ[R] f a0 := he_tmul a0
  have hinjB : Function.Injective (fun y : B => (1 : S) ⊗ₜ[R] y) := by
    have h1 : Function.Injective
        (TensorProduct.map (Algebra.linearMap R S) (LinearMap.id : B →ₗ[R] B)) := by
      have h := Module.Flat.rTensor_preserves_injective_linearMap (M := B)
        (f := Algebra.linearMap R S) halg
      simpa [LinearMap.rTensor_def] using h
    intro x y hxy
    have hR : (1 : R) ⊗ₜ[R] x = (1 : R) ⊗ₜ[R] y := by
      apply h1
      simpa using hxy
    have := congrArg (TensorProduct.lid R B) hR
    simpa using this
  exact (hinjB hb).symm

end TraceComparison

/-! ## 4. The equal-rank inclusion at `R'` -/

/-- **`S1849EqualRankInclusion` is proved.**  An injective map of finite etale `R'`-algebras
whose ranks at every prime agree is surjective. -/
theorem S1901_EqualRankInclusion : S1849EqualRankInclusion := by
  intro A B f hinj hrank
  haveI hFA : Module.Finite S1779R (A : Type) := A.property.left
  haveI hFB : Module.Finite S1779R (B : Type) := B.property.left
  haveI hEA : Algebra.Etale S1779R (A : Type) := A.property.right
  haveI hEB : Algebra.Etale S1779R (B : Type) := B.property.right
  haveI hFlatA : Module.Flat S1779R (A : Type) := inferInstance
  haveI hFlatB : Module.Flat S1779R (B : Type) := inferInstance
  haveI hProjA : Module.Projective S1779R (A : Type) := S1901_projective_of_finite_flat _
  haveI hProjB : Module.Projective S1779R (B : Type) := S1901_projective_of_finite_flat _
  -- the fibres
  haveI hKA : Module.Finite S1901K (S1901K ⊗[S1779R] (A : Type)) :=
    Module.Finite.base_change S1779R S1901K (A : Type)
  haveI hFlatKA : Module.Flat S1901K (S1901K ⊗[S1779R] (A : Type)) :=
    Module.Flat.baseChange S1779R S1901K (A : Type)
  haveI hEtKA : Algebra.Etale S1901K (S1901K ⊗[S1779R] (A : Type)) :=
    Algebra.Etale.baseChange S1779R (A : Type) S1901K
  haveI hFreeKA : Module.Free S1901K (S1901K ⊗[S1779R] (A : Type)) :=
    Module.free_of_flat_of_isLocalRing
  haveI hKB : Module.Finite S1901K (S1901K ⊗[S1779R] (B : Type)) :=
    Module.Finite.base_change S1779R S1901K (B : Type)
  haveI hFlatKB : Module.Flat S1901K (S1901K ⊗[S1779R] (B : Type)) :=
    Module.Flat.baseChange S1779R S1901K (B : Type)
  haveI hEtKB : Algebra.Etale S1901K (S1901K ⊗[S1779R] (B : Type)) :=
    Algebra.Etale.baseChange S1779R (B : Type) S1901K
  haveI hFreeKB : Module.Free S1901K (S1901K ⊗[S1779R] (B : Type)) :=
    Module.free_of_flat_of_isLocalRing
  haveI hFlatR_S : Module.Flat S1779R S1901K := IsLocalization.flat S1901K (nonZeroDivisors S1779R)
  -- the rank equality at the generic point gives equidimensional fibres
  have hfin : Module.finrank S1901K (S1901K ⊗[S1779R] (A : Type)) =
      Module.finrank S1901K (S1901K ⊗[S1779R] (B : Type)) := by
    have hA := Module.rankAtStalk_eq_finrank_tensorProduct (M := (A : Type))
      (p := (⊥ : PrimeSpectrum S1779R))
    have hB := Module.rankAtStalk_eq_finrank_tensorProduct (M := (B : Type))
      (p := (⊥ : PrimeSpectrum S1779R))
    have hA' : Module.rankAtStalk (A : Type) (⊥ : PrimeSpectrum S1779R) =
        Module.finrank S1901K (S1901K ⊗[S1779R] (A : Type)) := hA
    have hB' : Module.rankAtStalk (B : Type) (⊥ : PrimeSpectrum S1779R) =
        Module.finrank S1901K (S1901K ⊗[S1779R] (B : Type)) := hB
    exact hA'.symm.trans ((hrank ⊥).trans hB')
  -- nondegeneracy of the trace form of the fibre
  have hnondeg : ∀ x : S1901K ⊗[S1779R] (A : Type),
      (∀ y : S1901K ⊗[S1779R] (A : Type),
        Algebra.trace S1901K (S1901K ⊗[S1779R] (A : Type)) (x * y) = 0) → x = 0 := by
    intro x hx
    have hbij := S1901_traceForm_bijective_generic (K := S1901K) A
    have h0 : Algebra.traceForm S1901K (S1901K ⊗[S1779R] (A : Type)) x = 0 := by
      apply LinearMap.ext
      intro y
      rw [Algebra.traceForm_apply, LinearMap.zero_apply]
      exact hx y
    exact hbij.1 (show Algebra.traceForm S1901K (S1901K ⊗[S1779R] (A : Type)) x =
        Algebra.traceForm S1901K (S1901K ⊗[S1779R] (A : Type)) 0 from by rw [h0, map_zero])
  intro b
  -- the trace-dual element
  let φ : (A : Type) →ₗ[S1779R] S1779R :=
    { toFun := fun a => algebraTrace (R := S1779R) (A := (B : Type)) (b * f.hom.hom a)
      map_add' := by
        intro x y
        rw [map_add, mul_add, algebraTrace_add]
      map_smul' := by
        intro r x
        rw [map_smul, Algebra.mul_smul_comm, algebraTrace_smul]
        simp }
  obtain ⟨a0, ha0, -⟩ := S1859ProjectiveTraceDuality_proof A hProjA φ
  have hA0 : ∀ x : (A : Type), algebraTrace (R := S1779R) (A := (A : Type)) (a0 * x) =
      algebraTrace (R := S1779R) (A := (B : Type)) (b * f.hom.hom x) := by
    intro x
    have h := ha0 x
    rw [projectiveTraceForm_apply] at h
    exact h
  exact ⟨a0, S1901_trace_comparison (R := S1779R) (A := (A : Type)) (B := (B : Type))
    (S := S1901K) (halg := S1901K_algebraMap_injective) (f := f.hom.hom) hinj hfin hnondeg
    b a0 hA0⟩

/-! ## 5. Consumers: the surjectivity half and the S1848 route -/

/-- **`S1849SurjectiveOnInjective`**: the surjectivity half of the residue-fibre reflection
statement.  The rank equality at every prime is supplied unconditionally by S1862. -/
theorem S1901_S1849SurjectiveOnInjective : S1849SurjectiveOnInjective := by
  intro A B f hinj hf
  exact S1901_EqualRankInclusion f hinj (fun p => S1862_rankAtStalk_eq f hf p)

/-- The residue-fibre reflection statement at `R'` from kernel vanishing alone: S1862's route
theorem with the trace-form input `S1849EqualRankInclusion` discharged here. -/
theorem S1901_S1848FReflectsIsoMaps_of_kernelVanishes (hker : S1849KernelVanishes) :
    S1848FReflectsIsoMaps :=
  S1848FReflectsIsoMaps_of_route' hker S1901_EqualRankInclusion

/-- The residue-fibre reflection statement at `R'` from the *single* remaining input
`S1862FiberPurity` (fibre purity of the kernel of a map which is an isomorphism on the closed
fibre).  This is S1862's `S1848FReflectsIsoMaps_of_purity` with its trace-form hypothesis
`S1849EqualRankInclusion` discharged here. -/
theorem S1901_S1848FReflectsIsoMaps_of_purity (h : S1862FiberPurity) :
    S1848FReflectsIsoMaps :=
  S1848FReflectsIsoMaps_of_purity h S1901_EqualRankInclusion

/-! ## 6. Formal checks and axiom audit -/

#check S1901_projective_of_finite_flat
#check S1901K
#check S1901K_field
#check S1901_traceForm_bijective_generic
#check S1901_trace_comparison
#check S1901_EqualRankInclusion
#check S1901_S1849SurjectiveOnInjective
#check S1901_S1848FReflectsIsoMaps_of_kernelVanishes
#check S1901_S1848FReflectsIsoMaps_of_purity

#print axioms S1901_projective_of_finite_flat
#print axioms S1901_traceForm_bijective_generic
#print axioms S1901_trace_comparison
#print axioms S1901_EqualRankInclusion
#print axioms S1901_S1849SurjectiveOnInjective
#print axioms S1901_S1848FReflectsIsoMaps_of_kernelVanishes
#print axioms S1901_S1848FReflectsIsoMaps_of_purity

end LeanFormal.IUT.XiFPaper.S1901EqualRankTraceActual