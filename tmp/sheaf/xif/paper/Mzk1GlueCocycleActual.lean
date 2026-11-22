import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1GlueCocycleActual

/-- The user-facing cocycle equation of a gluing data in the identity-transition case,
stated with an explicit equality of the two overlap schemes and eqToHom: this avoids the
non-definitional identification of 𝟙 (V (i,j)) with a morphism out of V (j,i), which
blocks the direct rewriting of Scheme.GlueData.glue_condition. -/
theorem glue_condition_eqToHom {D : Scheme.GlueData} (i j : D.J)
    (hV : D.V (i, j) = D.V (j, i)) (ht : D.t i j = eqToHom hV) :
    eqToHom hV ≫ (D.f j i ≫ D.ι j) = D.f i j ≫ D.ι i := by
  rw [← ht]
  exact D.glue_condition i j

/-- The cocycle equation in its plain form, when the two overlap schemes are equal and the
transition is the identity. -/
theorem glue_condition_of_v_eq {D : Scheme.GlueData} (i j : D.J)
    (hV : D.V (i, j) = D.V (j, i)) (ht : D.t i j = eqToHom hV) :
    D.f i j ≫ D.ι i = eqToHom hV ≫ (D.f j i ≫ D.ι j) :=
  (glue_condition_eqToHom i j hV ht).symm

#print axioms glue_condition_eqToHom
#print axioms glue_condition_of_v_eq
end LeanFormal.IUT.XiFPaper.Mzk1GlueCocycleActual
