import tmp.sheaf.n8.closure.C7OneFactorAlgEquiv
import Mathlib.RingTheory.PiTensorProduct

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

/-!
# Constructed one-factor algebra equivalence

Evaluation at the unique tensor index is multilinear; `liftAlgHom` makes it an
algebra homomorphism.  Its underlying linear map is
`PiTensorProduct.subsingletonEquiv`, which is bijective.  Hence it is the
required algebra equivalence.  No arbitrary `AlgEquiv` is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7OneFactorAlgEquiv

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open scoped BigOperators ENNReal TensorProduct

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

/-- Evaluation at the unique tensor index. -/
noncomputable def oneFactorEval :
    MultilinearMap ℚ_[pNat S] (fun _ : Unit => PaperKf S) (PaperKf S) where
  toFun f := f ()
  map_update_add' := by
    intro _ m i x y
    cases i
    simp
  map_update_smul' := by
    intro _ m i r x
    cases i
    simp

/-- The algebra homomorphism obtained by lifting the one-factor evaluation. -/
noncomputable def oneFactorEvalAlgHom :
    PaperBlock S →ₐ[ℚ_[pNat S]] PaperKf S :=
  PiTensorProduct.liftAlgHom (oneFactorEval S)
    (by rfl) (by intro x y; rfl)

theorem oneFactorEvalAlgHom_apply (x : PaperBlock S) :
    oneFactorEvalAlgHom S x =
      PiTensorProduct.subsingletonEquiv
        (R := ℚ_[pNat S]) (s := fun _ : Unit => PaperKf S) () x := by
  rfl

theorem oneFactorEvalAlgHom_bijective :
    Function.Bijective (oneFactorEvalAlgHom S) := by
  have h : (oneFactorEvalAlgHom S : PaperBlock S → PaperKf S) =
      (PiTensorProduct.subsingletonEquiv
        (R := ℚ_[pNat S]) (s := fun _ : Unit => PaperKf S) () :
          PaperBlock S → PaperKf S) := by
    funext x
    exact oneFactorEvalAlgHom_apply S x
  rw [h]
  exact (PiTensorProduct.subsingletonEquiv
    (R := ℚ_[pNat S]) (s := fun _ : Unit => PaperKf S) ()).bijective

/-- The required algebra equivalence. -/
noncomputable def oneFactorAlgEquiv :
    PaperBlock S ≃ₐ[ℚ_[pNat S]] PaperKf S :=
  AlgEquiv.ofBijective (oneFactorEvalAlgHom S)
    (oneFactorEvalAlgHom_bijective S)

theorem oneFactorAlgEquiv_apply (x : PaperBlock S) :
    oneFactorAlgEquiv S x =
      PiTensorProduct.subsingletonEquiv
        (R := ℚ_[pNat S]) (s := fun _ : Unit => PaperKf S) () x := by
  rfl

theorem missingOneFactorTensorAlgEquiv_proved :
    MissingOneFactorTensorAlgEquiv S :=
  ⟨oneFactorAlgEquiv S⟩

end LeanFormal.IUT.N8Closure.C7OneFactorAlgEquiv

end