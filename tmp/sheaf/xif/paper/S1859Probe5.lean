
import tmp.sheaf.xif.paper.S1858GlobalTraceActual
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Finite

noncomputable section
set_option maxHeartbeats 2000000
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

end BaseChange


end LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual