import LeanFormal.IUT.IUTIV.Estimates.ArchimedeanTensorMetric

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVProp15CompositeActual — IUT IV Prop 1.5(i) composite

Genuine composite of the existing direct-sum-vs-tensor metric assets:
the algebra map a⊗b ↦ (ab, a b̄) is a bijection, the direct-sum metric is
twice the tensor metric, and the length identity carries factor 2.
No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVProp15CompositeActual

open LeanFormal.IUT.IUTIV.Estimates
open scoped TensorProduct

theorem iutIVProp15i_composite :
    (∀ x y : (ℂ ⊗[ℝ] ℂ),
      complexProdInner (complexTensorToProd x) (complexTensorToProd y) =
        2 * inner ℝ x y) ∧
      (∀ x : (ℂ ⊗[ℝ] ℂ),
        ‖(complexTensorToProd x).1‖ ^ 2 + ‖(complexTensorToProd x).2‖ ^ 2 =
          2 * ‖x‖ ^ 2) ∧
      Function.Bijective complexTensorToProd :=
  ⟨complexTensorToProd_inner, complexTensorToProd_norm_sq, complexTensorToProd_bijective⟩

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVProp15CompositeActual

end
