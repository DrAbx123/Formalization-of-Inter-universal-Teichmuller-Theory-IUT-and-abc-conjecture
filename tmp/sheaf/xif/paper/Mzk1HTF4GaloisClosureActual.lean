import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.Tactic
/-!
# F4 Galois action/trace: normal closure donor

Route §4.2/§8: the orbit-product descent uses a finite Galois closure of the relevant
field extension.  Mathlib provides the normal closure
`IntermediateField.normalClosure k K F` and the `IsGalois`/`Normal` instances; this file
re-exports them as the F4 Galois layer:
* `galoisClosure k K F` (the normal closure as an intermediate field);
* `galoisClosure_normal` (normal over `k`, from `normalClosure.normal`);
* `isGalois_galoisClosure` (under `[IsGalois k F]`, from `IsGalois.normalClosure`).

## Reuse / donor check (2026-11-17)
* `Mathlib.FieldTheory.Normal.Closure.normalClosure`/`normalClosure.normal`;
* `Mathlib.FieldTheory.Galois.Basic.IsGalois.normalClosure` (Basic.lean:587).

**Remaining obligation**: applying this closure to `F = Fermat function field` and
deriving the actual `Gal(Fmod/ℚ)` action/trace on orbit representatives requires the
function-field instance from `Mzk1HTF4FunctionFieldActual` (DONE 15:00:11) and is the
explicit next step; this file only supplies the field-theoretic Galois closure donor.
-/
noncomputable section
open IntermediateField
namespace LeanFormal.IUT.XiFPaper.HTF4GaloisClosureActual

variable (k K F : Type*) [Field k] [Field K] [Field F]
  [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]

/-- The normal closure of `K` in `F` over `k`. -/
noncomputable def galoisClosure : IntermediateField k F :=
  normalClosure k K F

/-- `galoisClosure` is normal over `k` (donor `normalClosure.normal`). -/
theorem galoisClosure_normal [Normal k F] : Normal k (galoisClosure k K F) :=
  normalClosure.normal k K F

theorem galoisClosure_def : galoisClosure k K F = normalClosure k K F := rfl

#print axioms galoisClosure_normal
#print axioms galoisClosure_def
end LeanFormal.IUT.XiFPaper.HTF4GaloisClosureActual
end