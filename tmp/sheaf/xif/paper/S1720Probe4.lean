import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
set_option backward.isDefEq.respectTransparency false
example (K : Type) [Field K] :
    (AlgebraicClosure.instCommRing K : CommRing (AlgebraicClosure K)) =
      (AlgebraicClosure.instField K).toCommRing := rfl
example (K : Type) [Field K] : (AlgebraicClosure.instCommRing K : CommRing (AlgebraicClosure K)) =
      (AlgebraicClosure.instField K).toCommRing := by
  congr
