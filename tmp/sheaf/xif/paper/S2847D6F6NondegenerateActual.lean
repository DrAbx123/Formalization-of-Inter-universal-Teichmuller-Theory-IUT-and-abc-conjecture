import tmp.sheaf.xif.paper.S2844D6F6BaseChangeActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual
open LeanFormal.IUT.XiFPaper.S2814bE37ChartZOverActual
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open scoped SpecOfNotation
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2847D6F6NondegenerateActual

local instance : Field S2844D6F6BaseChangeActual.K := inferInstance
local instance : NumberField S2844D6F6BaseChangeActual.K :=
  LeanFormal.IUT.XiFPaper.S2809E6FiniteActual.S2809_numberField
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

theorem S2847_zero_satisfies :
    (0 : S2844D6F6BaseChangeActual.K) ^ 2 + 0 =
      (0 : S2844D6F6BaseChangeActual.K) ^ 3 - 0 := by
  norm_num

theorem S2847_neg_one_satisfies :
    (-1 : S2844D6F6BaseChangeActual.K) ^ 2 + (-1) =
      (0 : S2844D6F6BaseChangeActual.K) ^ 3 - 0 := by
  norm_num

noncomputable def S2847ChartZOver_zero :
    S2844D6F6BaseChangeActual.S2844Base ⟶
      S2844D6F6BaseChangeActual.S2844X :=
  S2844D6F6BaseChangeActual.S2844ChartZOver
    (0 : S2844D6F6BaseChangeActual.K) 0 S2847_zero_satisfies

noncomputable def S2847ChartZOver_neg_one :
    S2844D6F6BaseChangeActual.S2844Base ⟶
      S2844D6F6BaseChangeActual.S2844X :=
  S2844D6F6BaseChangeActual.S2844ChartZOver
    (0 : S2844D6F6BaseChangeActual.K) (-1) S2847_neg_one_satisfies

noncomputable def S2847ProjectiveZero :
    S2844D6F6BaseChangeActual.S2844Curve.toProjective.Point :=
  S2844D6F6BaseChangeActual.S2844ZSchemeToProjectivePoint
    (E37ChartZSchemePoint S2844D6F6BaseChangeActual.K
      (0 : S2844D6F6BaseChangeActual.K) 0 S2847_zero_satisfies)

noncomputable def S2847ProjectiveNegOne :
    S2844D6F6BaseChangeActual.S2844Curve.toProjective.Point :=
  S2844D6F6BaseChangeActual.S2844ZSchemeToProjectivePoint
    (E37ChartZSchemePoint S2844D6F6BaseChangeActual.K
      (0 : S2844D6F6BaseChangeActual.K) (-1) S2847_neg_one_satisfies)

theorem S2847_affine_ne :
    S2844D6F6BaseChangeActual.S2844ZSchemeToAffinePoint
        (E37ChartZSchemePoint S2844D6F6BaseChangeActual.K
          (0 : S2844D6F6BaseChangeActual.K) 0 S2847_zero_satisfies) ≠
      S2844D6F6BaseChangeActual.S2844ZSchemeToAffinePoint
        (E37ChartZSchemePoint S2844D6F6BaseChangeActual.K
          (0 : S2844D6F6BaseChangeActual.K) (-1) S2847_neg_one_satisfies) := by
  rw [S2844D6F6BaseChangeActual.S2844ZOver_roundtrip,
    S2844D6F6BaseChangeActual.S2844ZOver_roundtrip]
  intro h
  have hsome : WeierstrassCurve.Affine.Point.some
      (0 : S2844D6F6BaseChangeActual.K) 0 _ =
      WeierstrassCurve.Affine.Point.some
        (0 : S2844D6F6BaseChangeActual.K) (-1) _ := h
  have hy : (0 : S2844D6F6BaseChangeActual.K) = -1 :=
    (WeierstrassCurve.Affine.Point.some.inj hsome).2
  norm_num at hy

theorem S2847_projective_ne :
    S2847ProjectiveZero ≠ S2847ProjectiveNegOne := by
  intro h
  apply S2847_affine_ne
  have h' : S2844D6F6BaseChangeActual.S2844ZSchemeToAffinePoint
        (E37ChartZSchemePoint S2844D6F6BaseChangeActual.K
          (0 : S2844D6F6BaseChangeActual.K) 0 S2847_zero_satisfies) =
      S2844D6F6BaseChangeActual.S2844ZSchemeToAffinePoint
        (E37ChartZSchemePoint S2844D6F6BaseChangeActual.K
          (0 : S2844D6F6BaseChangeActual.K) (-1) S2847_neg_one_satisfies) := by
    apply (WeierstrassCurve.Projective.Point.toAffineAddEquiv
      S2844D6F6BaseChangeActual.S2844Curve.toProjective).symm.injective
    simpa [S2847ProjectiveZero, S2847ProjectiveNegOne,
      S2844D6F6BaseChangeActual.S2844ZSchemeToProjectivePoint] using h
  exact h'

theorem S2847_glued_zero :
    S2844D6F6BaseChangeActual.S2844GluedOverMap S2847ChartZOver_zero =
      S2847ProjectiveZero := by
  change S2844D6F6BaseChangeActual.S2844GluedMap
    (E37ChartZSchemePoint S2844D6F6BaseChangeActual.K
      (0 : S2844D6F6BaseChangeActual.K) 0 S2847_zero_satisfies ≫
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K) =
    S2844D6F6BaseChangeActual.S2844ZSchemeToProjectivePoint
      (E37ChartZSchemePoint S2844D6F6BaseChangeActual.K
        (0 : S2844D6F6BaseChangeActual.K) 0 S2847_zero_satisfies)
  rw [S2844D6F6BaseChangeActual.S2844GluedMap_chartZ]

theorem S2847_glued_neg_one :
    S2844D6F6BaseChangeActual.S2844GluedOverMap S2847ChartZOver_neg_one =
      S2847ProjectiveNegOne := by
  change S2844D6F6BaseChangeActual.S2844GluedMap
    (E37ChartZSchemePoint S2844D6F6BaseChangeActual.K
      (0 : S2844D6F6BaseChangeActual.K) (-1) S2847_neg_one_satisfies ≫
        S2820E37ChartZMap S2844D6F6BaseChangeActual.K) =
    S2844D6F6BaseChangeActual.S2844ZSchemeToProjectivePoint
      (E37ChartZSchemePoint S2844D6F6BaseChangeActual.K
        (0 : S2844D6F6BaseChangeActual.K) (-1) S2847_neg_one_satisfies)
  rw [S2844D6F6BaseChangeActual.S2844GluedMap_chartZ]

theorem S2847ChartZOver_ne :
    S2847ChartZOver_zero ≠ S2847ChartZOver_neg_one := by
  intro h
  apply S2847_projective_ne
  rw [← S2847_glued_zero, ← S2847_glued_neg_one, h]

theorem S2847_not_isPointFiber :
    ¬ IsPointFiber S2844D6F6BaseChangeActual.S2844Fiber := by
  intro h
  have hsub := h (Opposite.op S2844D6F6BaseChangeActual.S2844Base)
  change Subsingleton
    (Discrete (S2844D6F6BaseChangeActual.S2844Base ⟶
      S2844D6F6BaseChangeActual.S2844X)) at hsub
  have heqDisc :
      (Discrete.mk S2847ChartZOver_zero) =
        (Discrete.mk S2847ChartZOver_neg_one) :=
    Subsingleton.elim _ _
  exact S2847ChartZOver_ne (congrArg Discrete.as heqDisc)

#check S2847_not_isPointFiber
#print axioms S2847_not_isPointFiber

end LeanFormal.IUT.XiFPaper.S2847D6F6NondegenerateActual
end
