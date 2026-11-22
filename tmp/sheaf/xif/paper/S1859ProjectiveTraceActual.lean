
/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1859

# S1859: the trace of a finitely generated projective module, and S1858ProjectiveTraceGluing

S1858 showed that Mathlib's `Algebra.trace` is *junk zero* on an `R'`-algebra without a
finite basis, so `S1853GlobalTracePerfect` is literally false for a finite etale `R'`-algebra
which is not free as a module.  The genuine missing input recorded there was
`S1858ProjectiveTraceGluing`: a trace form for finite *projective* modules together with
its compatibility with localisation at maximal ideals.  This file supplies it.

## What is proved in this file

1. **The trace of an endomorphism of a finitely generated projective module.**
   `FreeCover` is a finite free cover `p : R^n -> M` together with a splitting
   `i : M -> R^n` (`p ∘ i = id`).  The cover trace `trace c f = tr(i ∘ f ∘ p)` is shown
   independent of the cover (the key identity is `tr(A ∘ B) = tr(B ∘ A)` for the two
   comparison maps between two different free covers).  This gives `projTrace`.
2. **Well-definedness, additivity, multiplicativity.**  `projTrace (f + g) = projTrace f +
   projTrace g`, `projTrace (a • f) = a * projTrace f`, and the cyclic
   multiplicativity `projTrace (f ∘ g) = projTrace (g ∘ f)`.
3. **Agreement with Mathlib on free modules** (`projTrace_eq_trace_of_free`), hence on a free
   finite algebra `projTrace (lmul x) = Algebra.trace R A x` and
   `projectiveTraceForm = Algebra.traceForm` (`algebraTrace_eq_trace`,
   `projectiveTraceForm_eq_traceForm`).
4. **Base change compatibility.**  For a commutative `R`-algebra `S`,
   `projTrace_S (f.baseChange S) = algebraMap R S (projTrace_R f)`; for an algebra
   `A`, `algebraTrace_S (1 ⊗ x) = algebraMap R S (algebraTrace_R x)`
   (`projTrace_baseChange`, `algebraTrace_baseChange`).
5. **`S1858ProjectiveTraceGluing` is proved** (`S1858ProjectiveTraceGluing_proof`):
   for every finite etale `R'`-algebra `A` the projective trace form of `A` localises at
   every maximal ideal to Mathlib's trace form of the (automatically free) localised
   algebra.  This is the exact missing input isolated in S1858.

## The precise remaining input

With the projective trace in place, what is still missing for the S1849/S1853 route is
*trace duality*, i.e. the **surjectivity** of the trace-dual map
`A -> A^*, a ↦ (b ↦ projectiveTraceForm a b)`, not merely its injectivity.  This is
recorded below as `S1859ProjectiveTraceDuality` (a plain `Prop` with no inhabitant).
Even granting it, `S1849EqualRankInclusion` still requires the integral-descent step:
an inclusion `A ⊆ B` of finite etale `R'`-algebras with equal rank at every prime has
equal generic fibre (`A ⊗ K = B ⊗ K`, from constancy of the rank over the domain `R'`),
and then one has to show that an element of `B` which becomes an element of `A` after
inverting a non-zero scalar already lies in `A`; the trace form represents the
relevant functionals on `A` but not on the torsion quotient `B/A`.  Finally the six-field
statement `S1835BCReflectsIsos` (field 6 at `R'`) additionally needs
`S1849KernelVanishes` and the closed-fibre rank equality;  this file does not claim any
of these.

## Honest boundary

No `sorry`, `admit`, new axiom, `Shrink`, `ULift` or `PUnit` occurs in this file.  Everything
asserted as a theorem is proved, and the axiom audit at the end prints only
`[propext, Classical.choice, Quot.sound]`.  `S1859ProjectiveTraceDuality` is a
`Prop` with no inhabitant and is never used as a hypothesis for an unconditional
statement.
-/

import tmp.sheaf.xif.paper.S1858GlobalTraceActual
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 20
set_option linter.unusedSectionVars false
open scoped TensorProduct
open LinearMap

namespace LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual

universe u v w w'

section Cover

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite free cover of `M` together with a splitting. -/
structure FreeCover (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] where
  n : ℕ
  p : (Fin n → R) →ₗ[R] M
  i : M →ₗ[R] Fin n → R
  hpi : p ∘ₗ i = LinearMap.id

variable {F : Type w} {F' : Type w'} [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
  [AddCommGroup F'] [Module R F'] [Module.Free R F'] [Module.Finite R F']

theorem trace_eq_of_covers {p : F →ₗ[R] M} {i : M →ₗ[R] F} (hpi : p ∘ₗ i = LinearMap.id)
    {p' : F' →ₗ[R] M} {i' : M →ₗ[R] F'} (hpi' : p' ∘ₗ i' = LinearMap.id)
    (f : M →ₗ[R] M) :
    LinearMap.trace R F (i ∘ₗ f ∘ₗ p) = LinearMap.trace R F' (i' ∘ₗ f ∘ₗ p') := by
  have h1 : ∀ y, p' (i' y) = y := fun y => DFunLike.congr_fun hpi' y
  have h2 : ∀ y, p (i y) = y := fun y => DFunLike.congr_fun hpi y
  let A : F' →ₗ[R] F := i ∘ₗ f ∘ₗ p'
  let B : F →ₗ[R] F' := i' ∘ₗ p
  have hAB : A ∘ₗ B = i ∘ₗ f ∘ₗ p := by
    ext x
    simp [A, B, h1]
  have hBA : B ∘ₗ A = i' ∘ₗ f ∘ₗ p' := by
    ext x
    simp [A, B, h2]
  rw [← hAB, ← hBA]
  exact LinearMap.trace_comp_comm' B A

end Cover

namespace FreeCover

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The trace of an endomorphism computed with a finite free cover. -/
def trace (c : FreeCover R M) (f : M →ₗ[R] M) : R :=
  LinearMap.trace R (Fin c.n → R) (c.i ∘ₗ f ∘ₗ c.p)

/-- The cover trace does not depend on the cover. -/
theorem trace_eq (c c' : FreeCover R M) (f : M →ₗ[R] M) : c.trace f = c'.trace f :=
  trace_eq_of_covers (R := R) (M := M) (F := Fin c.n → R) (F' := Fin c'.n → R)
    c.hpi c'.hpi f

theorem trace_add (c : FreeCover R M) (f g : M →ₗ[R] M) :
    c.trace (f + g) = c.trace f + c.trace g := by
  simp only [trace, LinearMap.add_comp, LinearMap.comp_add, map_add]

theorem trace_smul (c : FreeCover R M) (a : R) (f : M →ₗ[R] M) :
    c.trace (a • f) = a * c.trace f := by
  simp only [trace, LinearMap.smul_comp, LinearMap.comp_smul, map_smul, smul_eq_mul]

theorem trace_comp_comm (c : FreeCover R M) (f g : M →ₗ[R] M) :
    c.trace (f ∘ₗ g) = c.trace (g ∘ₗ f) := by
  have h2 : ∀ y, c.p (c.i y) = y := fun y => DFunLike.congr_fun c.hpi y
  have hfg : (c.i ∘ₗ f ∘ₗ c.p) ∘ₗ (c.i ∘ₗ g ∘ₗ c.p) = c.i ∘ₗ (f ∘ₗ g) ∘ₗ c.p := by
    ext x
    simp [h2]
  have hgf : (c.i ∘ₗ g ∘ₗ c.p) ∘ₗ (c.i ∘ₗ f ∘ₗ c.p) = c.i ∘ₗ (g ∘ₗ f) ∘ₗ c.p := by
    ext x
    simp [h2]
  simp only [trace]
  rw [← hfg, ← hgf]
  simpa [Module.End.mul_eq_comp] using
    LinearMap.trace_mul_comm (f := c.i ∘ₗ f ∘ₗ c.p) (g := c.i ∘ₗ g ∘ₗ c.p)

end FreeCover

section ProjTrace

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]

lemma exists_cover : Nonempty (FreeCover R M) := by
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  exact ⟨⟨n, p, i, hpi⟩⟩

/-- **The trace of an endomorphism of a finitely generated projective module**, computed
using a finite free cover and its splitting. -/
noncomputable def projTrace (f : M →ₗ[R] M) : R :=
  (Classical.choice (exists_cover (R := R) (M := M))).trace f

theorem projTrace_eq_cover (c : FreeCover R M) (f : M →ₗ[R] M) :
    projTrace f = c.trace f :=
  FreeCover.trace_eq (Classical.choice (exists_cover (R := R) (M := M))) c f

theorem projTrace_add (f g : M →ₗ[R] M) :
    projTrace (f + g) = projTrace f + projTrace g := by
  rw [projTrace_eq_cover (Classical.choice (exists_cover (R := R) (M := M))),
    projTrace_eq_cover (Classical.choice (exists_cover (R := R) (M := M))),
    projTrace_eq_cover (Classical.choice (exists_cover (R := R) (M := M)))]
  exact FreeCover.trace_add _ f g

theorem projTrace_smul (a : R) (f : M →ₗ[R] M) :
    projTrace (a • f) = a * projTrace f := by
  rw [projTrace_eq_cover (Classical.choice (exists_cover (R := R) (M := M))),
    projTrace_eq_cover (Classical.choice (exists_cover (R := R) (M := M)))]
  exact FreeCover.trace_smul _ a f

/-- The trace is cyclically invariant: `tr(f ∘ g) = tr(g ∘ f)`. -/
theorem projTrace_comp_comm (f g : M →ₗ[R] M) :
    projTrace (f ∘ₗ g) = projTrace (g ∘ₗ f) := by
  rw [projTrace_eq_cover (Classical.choice (exists_cover (R := R) (M := M))),
    projTrace_eq_cover (Classical.choice (exists_cover (R := R) (M := M)))]
  exact FreeCover.trace_comp_comm _ f g

theorem projTrace_zero : projTrace (0 : M →ₗ[R] M) = 0 := by
  simpa using projTrace_smul (0 : R) (0 : M →ₗ[R] M)

theorem projTrace_neg (f : M →ₗ[R] M) : projTrace (-f) = -projTrace f := by
  have h : (-f) = (-1 : R) • f := by simp
  rw [h, projTrace_smul]
  ring

/-- On a finite free module the projective trace agrees with Mathlib's linear-map trace. -/
theorem projTrace_eq_trace_of_free [Module.Free R M] (f : M →ₗ[R] M) :
    projTrace f = LinearMap.trace R M f := by
  classical
  set c := Classical.choice (exists_cover (R := R) (M := M)) with hc
  rw [projTrace_eq_cover c]
  have h := trace_eq_of_covers (R := R) (M := M) (F := Fin c.n → R) (F' := M)
    c.hpi (p' := (LinearMap.id : M →ₗ[R] M)) (i' := (LinearMap.id : M →ₗ[R] M)) rfl f
  simpa [FreeCover.trace] using h

end ProjTrace

section AlgebraTrace

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The projective algebra trace of an element. -/
noncomputable def algebraTrace [Module.Finite R A] [Module.Projective R A] (x : A) : R :=
  projTrace (R := R) (M := A) (Algebra.lmul R A x)

theorem algebraTrace_add [Module.Finite R A] [Module.Projective R A] (x y : A) :
    algebraTrace (R := R) (A := A) (x + y) = algebraTrace x + algebraTrace y := by
  simp only [algebraTrace, map_add, projTrace_add]

theorem algebraTrace_smul [Module.Finite R A] [Module.Projective R A] (a : R) (x : A) :
    algebraTrace (R := R) (A := A) (a • x) = a * algebraTrace x := by
  have hsmul : Algebra.lmul R A (algebraMap R A a) = a • (1 : Module.End R A) := by
    ext y
    simp [Algebra.smul_def]
  calc algebraTrace (a • x)
      = projTrace (Algebra.lmul R A (algebraMap R A a * x)) := by
          rw [algebraTrace, Algebra.smul_def]
    _ = projTrace (Algebra.lmul R A (algebraMap R A a) * Algebra.lmul R A x) := by
          rw [map_mul]
    _ = projTrace (Algebra.lmul R A (algebraMap R A a) ∘ₗ Algebra.lmul R A x) := by
          rw [Module.End.mul_eq_comp]
    _ = projTrace ((a • (1 : Module.End R A)) ∘ₗ Algebra.lmul R A x) := by rw [hsmul]
    _ = projTrace (a • (Algebra.lmul R A x)) := by
          rw [LinearMap.smul_comp, Module.End.one_eq_id, LinearMap.id_comp]
    _ = a * projTrace (Algebra.lmul R A x) := projTrace_smul a _
    _ = a * algebraTrace x := rfl

/-- The projective trace form `(x,y) ↦ tr(x*y)`. -/
noncomputable def projectiveTraceForm [Module.Finite R A] [Module.Projective R A] :
    LinearMap.BilinForm R A :=
  LinearMap.mk₂ R (fun x y => algebraTrace (x * y))
    (fun x₁ x₂ y => by rw [add_mul]; exact algebraTrace_add _ _)
    (fun a x y => by rw [smul_mul_assoc]; exact algebraTrace_smul _ _)
    (fun x y₁ y₂ => by rw [mul_add]; exact algebraTrace_add _ _)
    (fun a x y => by rw [mul_smul_comm]; exact algebraTrace_smul _ _)

theorem projectiveTraceForm_apply [Module.Finite R A] [Module.Projective R A]
    (x y : A) : projectiveTraceForm (R := R) (A := A) x y = algebraTrace (x * y) := rfl

/-- On a finite free algebra the projective trace is Mathlib's algebra trace. -/
theorem algebraTrace_eq_trace [Module.Finite R A] [Module.Projective R A]
    [Module.Free R A] (x : A) :
    algebraTrace (R := R) (A := A) x = Algebra.trace R A x := by
  rw [algebraTrace, projTrace_eq_trace_of_free, Algebra.trace_apply]

theorem projectiveTraceForm_eq_traceForm [Module.Finite R A] [Module.Projective R A]
    [Module.Free R A] : projectiveTraceForm (R := R) (A := A) = Algebra.traceForm R A := by
  ext x y
  rw [projectiveTraceForm_apply, Algebra.traceForm_apply, algebraTrace_eq_trace]

end AlgebraTrace


namespace BaseChange

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

variable (S : Type u) [CommRing S] [Algebra R S]

variable [Module.Finite R M] [Module.Projective R M]
  [Module.Finite S (S ⊗[R] M)] [Module.Projective S (S ⊗[R] M)]

/-- The trace of the base change computed from the base change of a cover. -/
theorem baseChange_trace_cover (c : FreeCover R M) (f : M →ₗ[R] M) :
    projTrace (R := S) (M := S ⊗[R] M) (f.baseChange S) = algebraMap R S (c.trace f) := by
  classical
  haveI : Module.Free S (S ⊗[R] (Fin c.n → R)) :=
    Algebra.TensorProduct.instFree R S (Fin c.n → R)
  haveI : Module.Finite S (S ⊗[R] (Fin c.n → R)) :=
    Module.Finite.base_change R S (Fin c.n → R)
  set cS : FreeCover S (S ⊗[R] M) :=
    Classical.choice (exists_cover (R := S) (M := S ⊗[R] M)) with hcS
  have hcomp : (LinearMap.baseChange S c.p) ∘ₗ (LinearMap.baseChange S c.i) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, c.hpi, LinearMap.baseChange_id]
  have heq := trace_eq_of_covers (R := S) (M := S ⊗[R] M)
    (F := S ⊗[R] (Fin c.n → R)) (F' := Fin cS.n → S)
    (p := LinearMap.baseChange S c.p) (i := LinearMap.baseChange S c.i) hcomp
    (p' := cS.p) (i' := cS.i) cS.hpi (f.baseChange S)
  rw [projTrace_eq_cover cS, FreeCover.trace, ← heq]
  have hbc : (LinearMap.baseChange S c.i) ∘ₗ (f.baseChange S) ∘ₗ (LinearMap.baseChange S c.p)
      = (c.i ∘ₗ f ∘ₗ c.p).baseChange S := by
    have h1 : (c.i ∘ₗ f ∘ₗ c.p).baseChange S
        = (LinearMap.baseChange S c.i) ∘ₗ
          ((f.baseChange S) ∘ₗ (LinearMap.baseChange S c.p)) := by
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rw [h1]
  rw [hbc, LinearMap.trace_baseChange, FreeCover.trace]

/-- **Base change compatibility of the projective trace.** -/
theorem projTrace_baseChange (f : M →ₗ[R] M) :
    projTrace (R := S) (M := S ⊗[R] M) (f.baseChange S) = algebraMap R S (projTrace f) := by
  classical
  set c : FreeCover R M := Classical.choice (exists_cover (R := R) (M := M)) with hc
  calc projTrace (R := S) (M := S ⊗[R] M) (f.baseChange S)
      = algebraMap R S (c.trace f) := baseChange_trace_cover S c f
    _ = algebraMap R S (projTrace f) := by rw [projTrace_eq_cover c]


section AlgebraBaseChange

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (S : Type u) [CommRing S] [Algebra R S]
variable [Module.Finite R A] [Module.Projective R A]
  [Module.Finite S (S ⊗[R] A)] [Module.Projective S (S ⊗[R] A)]

/-- **Base change compatibility of the algebra trace.** -/
theorem algebraTrace_baseChange (x : A) :
    algebraTrace (R := S) (A := S ⊗[R] A) (1 ⊗ₜ[R] x) =
      algebraMap R S (algebraTrace (R := R) (A := A) x) := by
  have h := projTrace_baseChange (R := R) (M := A) (S := S) (Algebra.lmul R A x)
  rw [Algebra.baseChange_lmul] at h
  exact h

end AlgebraBaseChange

end BaseChange



namespace Gluing

open BaseChange
open LeanFormal.IUT.XiFPaper.S1858GlobalTraceActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual

/-- **S1858ProjectiveTraceGluing is now proved.**  For every finite etale `R'`-algebra
`A`, the projective trace form of `A` localises at every maximal ideal to the
(Mathlib) trace form of the (free) localised algebra. -/
theorem S1858ProjectiveTraceGluing_proof :
    LeanFormal.IUT.XiFPaper.S1858GlobalTraceActual.S1858ProjectiveTraceGluing := by
  intro A
  haveI : Module.FinitePresentation S1779R (A : Type) :=
    Module.FinitePresentation.of_finite_of_finitePresentation (R := S1779R) (S := (A : Type))
  haveI : Module.Projective S1779R (A : Type) := Module.Flat.projective_of_finitePresentation
  refine ⟨projectiveTraceForm (R := S1779R) (A := (A : Type)), ?_⟩
  intro p hp hmax x y
  haveI : p.IsMaximal := hmax
  let S := Localization.AtPrime p
  haveI : IsLocalRing S := inferInstance
  haveI : Module.Finite S (S ⊗[S1779R] (A : Type)) := inferInstance
  haveI : Module.Flat S (S ⊗[S1779R] (A : Type)) := inferInstance
  haveI : Module.Free S (S ⊗[S1779R] (A : Type)) :=
    Module.free_of_flat_of_isLocalRing
  rw [projectiveTraceForm_apply, Algebra.traceForm_apply]
  rw [show (1 ⊗ₜ[S1779R] x) * (1 ⊗ₜ[S1779R] y) = (1 : S) ⊗ₜ[S1779R] (x * y) by
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp]
  rw [← algebraTrace_eq_trace (R := S) (A := S ⊗[S1779R] (A : Type))]
  rw [algebraTrace_baseChange]

end Gluing




open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual

/-! ## The precise remaining input: trace duality -/

/-- **The precise remaining input.**  The trace-dual map `A → A^*`,
`a ↦ (b ↦ projectiveTraceForm a b)`, is bijective for every finite etale `R'`-algebra `A`.

S1858 isolated localisation compatibility of the trace form as the missing input; that
compatibility is now proved (`Gluing.S1858ProjectiveTraceGluing_proof`).  What remains is
the passage from the local unit-determinant statement
`S1853TraceFormActual.isUnit_det_traceMatrix_of_isLocalRing` to the global isomorphism:
the localisation of dual modules `(A^*)_p ≅ (A_p)^*` together with the fact that a map of
finite modules is an isomorphism as soon as it is so at every maximal ideal.  This is
trace-form perfectness (the different of a finite etale algebra is trivial) stated for the
genuine projective trace form rather than for the junk-zero `Algebra.traceForm`. -/
def S1859ProjectiveTraceDuality : Prop :=
  ∀ (A : CommAlgCat.FiniteEtale.{0} S1779R) (hproj : Module.Projective S1779R (A : Type)),
    letI : Module.Projective S1779R (A : Type) := hproj
    ∀ φ : (A : Type) →ₗ[S1779R] S1779R,
      ∃! a : (A : Type), ∀ b : (A : Type),
        projectiveTraceForm (R := S1779R) (A := (A : Type)) a b = φ b

/-- The corrected form of `S1853GlobalTracePerfect`: nondegeneracy of the *projective*
trace form of a finite etale `R'`-algebra.  (The literal `S1853GlobalTracePerfect` is
false, cf. S1858, because it is stated with Mathlib's junk-zero `Algebra.traceForm`.) -/
def S1859ProjectiveTracePerfect : Prop :=
  ∀ (A : CommAlgCat.FiniteEtale.{0} S1779R) (hproj : Module.Projective S1779R (A : Type)),
    letI : Module.Projective S1779R (A : Type) := hproj
    (projectiveTraceForm (R := S1779R) (A := (A : Type))).Nondegenerate

/-- Trace duality implies the corrected trace perfectness. -/
theorem S1859ProjectiveTracePerfect_of_duality
    (h : S1859ProjectiveTraceDuality) : S1859ProjectiveTracePerfect := by
  intro A hproj
  letI : Module.Projective S1779R (A : Type) := hproj
  have hleft : ∀ x : (A : Type),
      (∀ y : (A : Type),
        projectiveTraceForm (R := S1779R) (A := (A : Type)) x y = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, ha, huniq⟩ := h A hproj (0 : (A : Type) →ₗ[S1779R] S1779R)
    have hx' : x = a := huniq x hx
    have h0' : (0 : (A : Type)) = a := huniq 0 (by simp)
    rw [hx', ← h0']
  refine ⟨hleft, ?_⟩
  intro y hy
  apply hleft y
  intro x
  have h := hy x
  rwa [show projectiveTraceForm (R := S1779R) (A := (A : Type)) y x =
      projectiveTraceForm (R := S1779R) (A := (A : Type)) x y by
    rw [projectiveTraceForm_apply, projectiveTraceForm_apply, mul_comm]]


/-! ## Formal checks -/

#check FreeCover
#check trace_eq_of_covers
#check FreeCover.trace_eq
#check projTrace
#check projTrace_eq_cover
#check projTrace_add
#check projTrace_smul
#check projTrace_comp_comm
#check projTrace_eq_trace_of_free
#check algebraTrace
#check algebraTrace_add
#check algebraTrace_smul
#check algebraTrace_eq_trace
#check projectiveTraceForm
#check projectiveTraceForm_apply
#check projectiveTraceForm_eq_traceForm
#check BaseChange.baseChange_trace_cover
#check BaseChange.projTrace_baseChange
#check BaseChange.algebraTrace_baseChange
#check Gluing.S1858ProjectiveTraceGluing_proof
#check S1859ProjectiveTraceDuality
#check S1859ProjectiveTracePerfect
#check S1859ProjectiveTracePerfect_of_duality

#print axioms FreeCover.trace_eq
#print axioms projTrace_add
#print axioms projTrace_smul
#print axioms projTrace_comp_comm
#print axioms projTrace_eq_trace_of_free
#print axioms algebraTrace_eq_trace
#print axioms projectiveTraceForm_eq_traceForm
#print axioms BaseChange.projTrace_baseChange
#print axioms BaseChange.algebraTrace_baseChange
#print axioms Gluing.S1858ProjectiveTraceGluing_proof
#print axioms S1859ProjectiveTracePerfect_of_duality

end LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual