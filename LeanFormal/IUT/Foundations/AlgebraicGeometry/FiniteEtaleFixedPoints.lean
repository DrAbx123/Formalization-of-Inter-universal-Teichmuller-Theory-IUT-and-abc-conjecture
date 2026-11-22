import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.Tactic

/-!
# Scratch: fixed points of a finite group action on a finite étale algebra

Let `R` be a commutative ring, `A` a finite étale `R`-algebra, and `G` a finite
group acting on `A` by `R`-algebra automorphisms.  This scratch file proves:

* the fixed-point subalgebra `A^G` is a subalgebra whose inclusion is finite and
  integral, and `A` is formally unramified over `A^G`;
* the affine quotient universal property: any `G`-invariant `R`-algebra map
  `B → A` factors uniquely through `A^G`;
* if `|G|` is invertible in `R` (the tame/Reynolds case), then `A^G` is a finite
  projective `R`-module, hence finite flat and finitely presented, and
  `A^G` is finite étale over `R` as soon as `A` is formally étale over `A^G`.

The general (possibly wild) case is *not* proved here; the precise remaining
gap is recorded in the final section.  No `sorry`, `axiom` or placeholder is
used anywhere in this file.
-/

open scoped TensorProduct

namespace ABCBridge.FiniteEtaleFixedPoints

noncomputable section

universe u

variable (R A G : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [MulSemiringAction G A] [SMulCommClass G R A]

/-! ## The fixed-point subalgebra -/

/-- The fixed-point subalgebra `A^G` of `A` with respect to the action of `G`. -/
def fixedPointSubalgebra : Subalgebra R A := FixedPoints.subalgebra R A G

instance : SMulCommClass G (fixedPointSubalgebra R A G) A :=
  inferInstanceAs (SMulCommClass G (FixedPoints.subalgebra R A G) A)

/-- The inclusion of the fixed-point subalgebra into `A`. -/
def fixedPointInclusion : fixedPointSubalgebra R A G →ₐ[R] A :=
  (fixedPointSubalgebra R A G).val

@[simp]
lemma mem_fixedPointSubalgebra {x : A} :
    x ∈ fixedPointSubalgebra R A G ↔ ∀ g : G, g • x = x :=
  Iff.rfl

@[simp]
lemma fixedPointInclusion_apply (x : fixedPointSubalgebra R A G) :
    fixedPointInclusion R A G x = (x : A) :=
  rfl

lemma fixedPointInclusion_injective : Function.Injective (fixedPointInclusion R A G) :=
  fun _ _ h => Subtype.ext h

/-- The action of `G` on `A` as `R`-algebra automorphisms. -/
def groupActionAlgEquiv (g : G) : A ≃ₐ[R] A := MulSemiringAction.toAlgEquiv R A g

@[simp]
lemma groupActionAlgEquiv_apply (g : G) (x : A) :
    groupActionAlgEquiv R A G g x = g • x :=
  rfl

/-- Every element of the fixed-point subalgebra is fixed by `G`. -/
lemma fixedPointInclusion_fixed (g : G) (x : fixedPointSubalgebra R A G) :
    groupActionAlgEquiv R A G g (fixedPointInclusion R A G x) = fixedPointInclusion R A G x :=
  x.2 g

/-- The fixed-point subalgebra satisfies `Algebra.IsInvariant`: every fixed point
of `A` lies in `A^G`. -/
instance fixedPointSubalgebra_isInvariant : Algebra.IsInvariant (fixedPointSubalgebra R A G) A G where
  isInvariant x hx := ⟨⟨x, hx⟩, rfl⟩

/-- The affine quotient universal property: every `G`-invariant `R`-algebra map
`B → A` factors uniquely through `A^G`. -/
theorem fixedPoints_lift_algHom {B : Type u} [CommRing B] [Algebra R B]
    (φ : B →ₐ[R] A) (hφ : ∀ (g : G) (b : B), groupActionAlgEquiv R A G g (φ b) = φ b) :
    ∃! ψ : B →ₐ[R] fixedPointSubalgebra R A G,
      (fixedPointInclusion R A G).comp ψ = φ := by
  let ψ : B →ₐ[R] fixedPointSubalgebra R A G :=
    φ.codRestrict (fixedPointSubalgebra R A G) fun b => by
      rw [mem_fixedPointSubalgebra]
      exact fun g => hφ g b
  refine ⟨ψ, ?_, ?_⟩
  · ext b
    rfl
  · intro ψ' hψ'
    ext b
    exact congrArg (fun f => f b) hψ'

/-- Integrality of `A` over `A^G`. -/
theorem fixedPointSubalgebra_isIntegral [Finite G] :
    Algebra.IsIntegral (fixedPointSubalgebra R A G) A :=
  Algebra.IsInvariant.isIntegral (fixedPointSubalgebra R A G) A G

/-- `A` is finite as a module over the fixed-point subalgebra whenever it is finite
over `R`. -/
theorem moduleFinite_over_fixedPointSubalgebra [Module.Finite R A] :
    Module.Finite (fixedPointSubalgebra R A G) A :=
  Module.Finite.of_restrictScalars_finite R (fixedPointSubalgebra R A G) A

/-! ## Formal unramifiedness over intermediate subalgebras -/

section IntermediateSubalgebra

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- For an intermediate subalgebra `S` between `R` and `A`, formal unramifiedness
of `A` over `R` implies formal unramifiedness of `A` over `S`: the canonical map
`Ω[A⁄R] → Ω[A⁄S]` is surjective. -/
theorem formallyUnramified_of_intermediate [Algebra.FormallyUnramified R A]
    (S : Subalgebra R A) : Algebra.FormallyUnramified S A := by
  refine ⟨⟨fun x y => ?_⟩⟩
  have hsurj : Function.Surjective (KaehlerDifferential.map R S A A) :=
    KaehlerDifferential.map_surjective R S A
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  rw [Subsingleton.elim x' y']

end IntermediateSubalgebra

/-- `A` is formally unramified over the fixed-point subalgebra when `A` is formally
unramified over `R`. -/
theorem formallyUnramified_over_fixedPointSubalgebra [Algebra.FormallyUnramified R A] :
    Algebra.FormallyUnramified (fixedPointSubalgebra R A G) A :=
  formallyUnramified_of_intermediate (fixedPointSubalgebra R A G)

/-- `A` is formally unramified over the fixed-point subalgebra when `A` is finite
étale over `R`. -/
theorem formallyUnramified_over_fixedPointSubalgebra_of_etale [Algebra.Etale R A] :
    Algebra.FormallyUnramified (fixedPointSubalgebra R A G) A :=
  formallyUnramified_over_fixedPointSubalgebra R A G

/-! ## The tame (Reynolds) case -/

section Reynolds

variable [Fintype G]

/-- The inverse of `|G|` in `R`, available because `|G|` is a unit. -/
def groupCardInv (hG : IsUnit (Fintype.card G : R)) : R := ↑hG.unit⁻¹

omit [Group G] in
lemma groupCardInv_mul_card (hG : IsUnit (Fintype.card G : R)) :
    groupCardInv R G hG * (Fintype.card G : R) = 1 := by
  have h : (↑hG.unit⁻¹ : R) * ↑hG.unit = 1 := hG.unit.inv_mul
  simpa [groupCardInv, hG.unit_spec] using h

/-- The orbit-sum map `a ↦ ∑ g, g • a`. -/
def orbitSum : A →ₗ[R] A where
  toFun a := ∑ g : G, g • a
  map_add' a b := by
    simp only [smul_add, Finset.sum_add_distrib]
  map_smul' r a := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun g _ => smul_comm g r a

@[simp]
lemma orbitSum_apply (a : A) : orbitSum R A G a = ∑ g : G, g • a :=
  rfl

/-- The orbit sum of `a` is fixed by `G`. -/
lemma orbitSum_mem (a : A) (g : G) : g • orbitSum R A G a = orbitSum R A G a := by
  rw [orbitSum_apply, Finset.smul_sum]
  simp only [← mul_smul]
  exact Equiv.sum_comp (Equiv.mulLeft g) (fun x : G => x • a)

/-- The orbit sum is `A^G`-linear. -/
lemma orbitSum_smul_of_fixed (s : fixedPointSubalgebra R A G) (a : A) :
    orbitSum R A G (s • a) = s • orbitSum R A G a := by
  rw [orbitSum_apply, orbitSum_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [smul_comm g s a]

/-- The Reynolds operator: the `G`-average of an element of `A`, rescaled by
`|G|^{-1}`.  It is `R`-linear and lands in `A^G`. -/
def reynolds (hG : IsUnit (Fintype.card G : R)) : A →ₗ[R] fixedPointSubalgebra R A G where
  toFun a :=
    ⟨groupCardInv R G hG • orbitSum R A G a, by
      intro g
      rw [smul_comm g (groupCardInv R G hG) (orbitSum R A G a), orbitSum_mem]⟩
  map_add' a b := by
    apply Subtype.ext
    change groupCardInv R G hG • orbitSum R A G (a + b) =
      groupCardInv R G hG • orbitSum R A G a + groupCardInv R G hG • orbitSum R A G b
    rw [map_add, smul_add]
  map_smul' r a := by
    apply Subtype.ext
    change groupCardInv R G hG • orbitSum R A G (r • a) =
      r • (groupCardInv R G hG • orbitSum R A G a)
    rw [map_smul, smul_smul, smul_smul, mul_comm]

@[simp]
lemma reynolds_apply_coe (hG : IsUnit (Fintype.card G : R)) (a : A) :
    (reynolds R A G hG a : A) = groupCardInv R G hG • orbitSum R A G a :=
  rfl

@[simp]
lemma reynolds_apply_one (hG : IsUnit (Fintype.card G : R)) :
    (reynolds R A G hG 1 : A) = 1 := by
  rw [reynolds_apply_coe, orbitSum_apply]
  simp only [smul_one, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, groupCardInv_mul_card, one_smul]

lemma reynolds_apply_one_subtype (hG : IsUnit (Fintype.card G : R)) :
    reynolds R A G hG 1 = 1 := by
  apply Subtype.ext
  simpa using reynolds_apply_one R A G hG

/-- The Reynolds operator as an `A^G`-linear map. -/
def reynoldsS (hG : IsUnit (Fintype.card G : R)) :
    A →ₗ[fixedPointSubalgebra R A G] fixedPointSubalgebra R A G where
  toFun a := reynolds R A G hG a
  map_add' a b := (reynolds R A G hG).map_add a b
  map_smul' s a := by
    apply Subtype.ext
    change groupCardInv R G hG • orbitSum R A G (s • a) =
      (s : A) • (groupCardInv R G hG • orbitSum R A G a)
    rw [orbitSum_smul_of_fixed]
    change groupCardInv R G hG • ((s : A) • orbitSum R A G a) =
      (s : A) • (groupCardInv R G hG • orbitSum R A G a)
    rw [smul_comm]

/-- The Reynolds operator is a retraction of the inclusion `A^G → A` as
`R`-linear maps. -/
theorem reynolds_comp_inclusion (hG : IsUnit (Fintype.card G : R)) :
    (reynolds R A G hG).comp (fixedPointInclusion R A G).toLinearMap = LinearMap.id := by
  ext x
  rw [LinearMap.comp_apply, LinearMap.id_apply, AlgHom.toLinearMap_apply,
    fixedPointInclusion_apply, reynolds_apply_coe, orbitSum_apply]
  have hx : ∀ g : G, g • (x : A) = (x : A) := x.2
  simp only [hx, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, groupCardInv_mul_card, one_smul]

/-- The fixed-point subalgebra is a direct summand of `A` as an `R`-module when
`|G|` is invertible in `R`. -/
theorem fixedPointSubalgebra_projective (hG : IsUnit (Fintype.card G : R))
    [Module.Projective R A] :
    Module.Projective R (fixedPointSubalgebra R A G) :=
  Module.Projective.of_split (fixedPointInclusion R A G).toLinearMap
    (reynolds R A G hG) (reynolds_comp_inclusion R A G hG)

/-- The fixed-point subalgebra is a finite `R`-module when `A` is. -/
theorem fixedPointSubalgebra_finite (hG : IsUnit (Fintype.card G : R))
    [Module.Finite R A] :
    Module.Finite R (fixedPointSubalgebra R A G) :=
  Module.Finite.of_surjective (reynolds R A G hG)
    (fun x => ⟨fixedPointInclusion R A G x,
      congrArg (fun f => f x) (reynolds_comp_inclusion R A G hG)⟩)

/-- The fixed-point subalgebra is a flat `R`-module when `A` is finite projective. -/
theorem fixedPointSubalgebra_flat (hG : IsUnit (Fintype.card G : R))
    [Module.Projective R A] :
    Module.Flat R (fixedPointSubalgebra R A G) := by
  haveI := fixedPointSubalgebra_projective R A G hG
  exact Module.Flat.of_projective

/-- The fixed-point subalgebra is finitely presented as an `R`-module when `A` is
finite projective. -/
theorem fixedPointSubalgebra_finitePresentation (hG : IsUnit (Fintype.card G : R))
    [Module.Projective R A] [Module.Finite R A] :
    Module.FinitePresentation R (fixedPointSubalgebra R A G) := by
  haveI := fixedPointSubalgebra_projective R A G hG
  haveI := fixedPointSubalgebra_finite R A G hG
  exact Module.finitePresentation_of_projective R _

/-- The fixed-point subalgebra is finitely presented as an `R`-algebra when `A` is
finite projective. -/
theorem fixedPointSubalgebra_algebraFinitePresentation (hG : IsUnit (Fintype.card G : R))
    [Module.Projective R A] [Module.Finite R A] :
    Algebra.FinitePresentation R (fixedPointSubalgebra R A G) := by
  haveI := fixedPointSubalgebra_finitePresentation R A G hG
  exact Algebra.FinitePresentation.of_finitePresentation R _

/-- In the tame case, if in addition `A` is formally étale over `A^G` (the remaining
geometric input, see the final section), then `A^G` is finite étale over `R`. -/
theorem etale_fixedPointSubalgebra_of_formallyEtale
    (hG : IsUnit (Fintype.card G : R))
    [Module.Finite R A] [Algebra.Etale R A]
    [Algebra.FormallyEtale (fixedPointSubalgebra R A G) A] :
    Algebra.Etale R (fixedPointSubalgebra R A G) := by
  -- First, `A` is finite projective over `R`.
  haveI : Module.Flat R A := Algebra.Smooth.flat R A
  haveI : Module.FinitePresentation R A :=
    Module.FinitePresentation.of_finite_of_finitePresentation R A
  haveI : Module.Projective R A := Module.Flat.projective_of_finitePresentation
  -- The fixed-point subalgebra is finite projective, flat and finitely presented.
  haveI : Module.Projective R (fixedPointSubalgebra R A G) :=
    fixedPointSubalgebra_projective R A G hG
  haveI : Module.Finite R (fixedPointSubalgebra R A G) :=
    fixedPointSubalgebra_finite R A G hG
  haveI : Module.Flat R (fixedPointSubalgebra R A G) := Module.Flat.of_projective
  haveI : Module.FinitePresentation R (fixedPointSubalgebra R A G) :=
    fixedPointSubalgebra_finitePresentation R A G hG
  haveI : Algebra.FinitePresentation R (fixedPointSubalgebra R A G) :=
    Algebra.FinitePresentation.of_finitePresentation R _
  -- Formal unramifiedness of `A` over `A^G` (unconditional).
  haveI : Algebra.FormallyUnramified (fixedPointSubalgebra R A G) A :=
    formallyUnramified_over_fixedPointSubalgebra_of_etale R A G
  -- Kähler base change: `A ⊗[A^G] Ω[A^G⁄R] ≃ Ω[A⁄R]`.
  have hK : A ⊗[fixedPointSubalgebra R A G] Ω[(fixedPointSubalgebra R A G)⁄R] ≃ₗ[A]
      Ω[A⁄R] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R (fixedPointSubalgebra R A G) A
  haveI : Subsingleton (A ⊗[fixedPointSubalgebra R A G] Ω[(fixedPointSubalgebra R A G)⁄R]) :=
    ⟨fun x y => hK.injective (Subsingleton.elim _ _)⟩
  -- The map `z ↦ 1 ⊗ z` is injective because the Reynolds retraction splits it.
  haveI : Subsingleton Ω[(fixedPointSubalgebra R A G)⁄R] := by
    refine ⟨fun x y => ?_⟩
    have hinj : Function.Injective (fun z : Ω[(fixedPointSubalgebra R A G)⁄R] =>
        (1 : A) ⊗ₜ[fixedPointSubalgebra R A G] z) := by
      intro x y hxy
      have h := congrArg (fun w =>
        (TensorProduct.lid (fixedPointSubalgebra R A G)
          Ω[(fixedPointSubalgebra R A G)⁄R]).toLinearMap
        ((reynoldsS R A G hG).rTensor Ω[(fixedPointSubalgebra R A G)⁄R] w)) hxy
      simpa [reynoldsS, reynolds_apply_one_subtype R A G hG] using h
    exact hinj (Subsingleton.elim _ _)
  haveI : Algebra.FormallyUnramified R (fixedPointSubalgebra R A G) := ⟨inferInstance⟩
  exact Algebra.Etale.of_formallyUnramified_of_flat

end Reynolds

/-! ## Exact residual

The following two statements are *not* proved in this file.

1. **General projectivity/finiteness without inverting `|G|`.**  When `|G|` is not
   a unit of `R`, the Reynolds operator is unavailable.  The inclusion
   `A^G → A` is then not known here to be a direct summand as an `R`-module, and
   consequently neither `Module.Finite R A^G` nor `Module.Projective R A^G` is
   proved.  Note that the trace form of `A/R` does not give a retraction in
   general (e.g. over `F_p[t]` the Artin--Schreier cover has zero trace form),
   and the `G`-invariant separability idempotent of `A/R` lies in the *diagonal*
   invariants `(A ⊗_R A)^G`, which is not `A^G ⊗_R A` in general (e.g. for the
   Galois cover `Q(√2)/Q` one has `(A ⊗_Q A)^G ≅ Q × Q` while `A^G ⊗_Q A ≅ A`).
2. **Formal étaleness of `A` over `A^G`.**  The hypothesis
   `Algebra.FormallyEtale (fixedPointSubalgebra R A G) A` in
   `etale_fixedPointSubalgebra_of_formallyEtale` is not discharged here.  What is
   proved unconditionally is formal unramifiedness
   (`formallyUnramified_over_fixedPointSubalgebra`).  In the tame case, once
   formal étaleness of `A/A^G` is available, the theorem
   `etale_fixedPointSubalgebra_of_formallyEtale` completes the proof that `A^G` is
   finite étale over `R`.
-/


/-! ## Axiom audit -/

#print axioms fixedPoints_lift_algHom
#print axioms fixedPointSubalgebra_isIntegral
#print axioms moduleFinite_over_fixedPointSubalgebra
#print axioms formallyUnramified_over_fixedPointSubalgebra
#print axioms fixedPointSubalgebra_projective
#print axioms fixedPointSubalgebra_finite
#print axioms fixedPointSubalgebra_flat
#print axioms fixedPointSubalgebra_finitePresentation
#print axioms fixedPointSubalgebra_algebraFinitePresentation
#print axioms etale_fixedPointSubalgebra_of_formallyEtale


end

end ABCBridge.FiniteEtaleFixedPoints