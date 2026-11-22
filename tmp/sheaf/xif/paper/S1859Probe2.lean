
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

section Cover

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite free cover of `M` together with a splitting. -/
structure FreeCover where
  n : ℕ
  p : (Fin n → R) →ₗ[R] M
  i : M →ₗ[R] Fin n → R
  hpi : p ∘ₗ i = LinearMap.id

variable {F F' : Type*} [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
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

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

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

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
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

/-- The trace is cyclically invariant. -/
theorem projTrace_comp_comm (f g : M →ₗ[R] M) :
    projTrace (f ∘ₗ g) = projTrace (g ∘ₗ f) := by
  rw [projTrace_eq_cover (Classical.choice (exists_cover (R := R) (M := M))),
    projTrace_eq_cover (Classical.choice (exists_cover (R := R) (M := M)))]
  exact FreeCover.trace_comp_comm _ f g

theorem projTrace_zero : projTrace (0 : M →ₗ[R] M) = 0 := by
  simpa using projTrace_add (0 : M →ₗ[R] M) 0

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
  simpa using h

end ProjTrace

section AlgebraTrace

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The projective algebra trace of an element. -/
noncomputable def algebraTrace [Module.Finite R A] [Module.Projective R A] (x : A) : R :=
  projTrace (R := R) (M := A) (Algebra.lmul R A x)

/-- The projective trace form. -/
noncomputable def projectiveTraceForm [Module.Finite R A] [Module.Projective R A] :
    LinearMap.BilinForm R A :=
  fun x y => algebraTrace (R := R) (A := A) (x * y)

/-- On a finite free algebra the projective trace is Mathlib's algebra trace. -/
theorem algebraTrace_eq_trace [Module.Finite R A] [Module.Projective R A]
    [Module.Free R A] (x : A) :
    algebraTrace (R := R) (A := A) x = Algebra.trace R A x := by
  rw [algebraTrace, projTrace_eq_trace_of_free, Algebra.trace_apply]

theorem projectiveTraceForm_apply [Module.Finite R A] [Module.Projective R A]
    (x y : A) : projectiveTraceForm (R := R) (A := A) x y = algebraTrace (x * y) := rfl

theorem projectiveTraceForm_eq_traceForm [Module.Finite R A] [Module.Projective R A]
    [Module.Free R A] : projectiveTraceForm (R := R) (A := A) = Algebra.traceForm R A := by
  ext x y
  rw [projectiveTraceForm_apply, Algebra.traceForm_apply, algebraTrace_eq_trace]

end AlgebraTrace

end LeanFormal.IUT.XiFPaper.S1859ProjectiveTraceActual
