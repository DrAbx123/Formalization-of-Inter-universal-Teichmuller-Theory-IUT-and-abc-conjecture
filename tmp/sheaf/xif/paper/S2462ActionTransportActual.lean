import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual

noncomputable section
set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2462ActionTransportActual

open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

/-- Coercion of the local S2440 action (the action obtained by restricting
the Galois action through galRestrict) to L. -/
theorem s2462_coe_smul_local (σ : Gal(L/K)) (a : RingOfIntegers L) :
    ((letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
        instMulSemiringActionAlgEquivRingOfIntegers_tmp K L
      σ • a : RingOfIntegers L) : L) = σ (algebraMap (RingOfIntegers L) L a) := by
  have h : ((letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
      instMulSemiringActionAlgEquivRingOfIntegers_tmp K L
      σ • a : RingOfIntegers L)) =
      galRestrict (RingOfIntegers K) K L (RingOfIntegers L) σ a := by
    with_unfolding_all rfl
  rw [h]
  exact algebraMap_galRestrict_apply (RingOfIntegers K) σ a

/-- Coercion of the ambient Mathlib action (the restricted action on
integralClosure Z L) to L. -/
theorem s2462_coe_smul_global (σ : Gal(L/K)) (a : RingOfIntegers L) :
    ((letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
        RingOfIntegers.instMulSemiringAction (K := L) (G := Gal(L/K))
      σ • a : RingOfIntegers L) : L) = σ (algebraMap (RingOfIntegers L) L a) := by
  change (σ • (a : L)) = σ (algebraMap (RingOfIntegers L) L a)
  rw [AlgEquiv.smul_def]

/-- The two smul operations on O_L agree. -/
theorem s2462_smul_eq (σ : Gal(L/K)) (a : RingOfIntegers L) :
    (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
        instMulSemiringActionAlgEquivRingOfIntegers_tmp K L
     σ • a) =
    (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
        RingOfIntegers.instMulSemiringAction (K := L) (G := Gal(L/K))
     σ • a) := by
  apply RingOfIntegers.ext
  rw [s2462_coe_smul_local, s2462_coe_smul_global]

/-- The algebra homomorphisms induced by the two actions agree. -/
theorem s2462_toAlgHom_eq (σ : Gal(L/K)) :
    @MulSemiringAction.toAlgHom Gal(L/K) (RingOfIntegers K) (RingOfIntegers L)
      _ _ _ _ (instMulSemiringActionAlgEquivRingOfIntegers_tmp K L)
      (instSMulCommClassAlgEquivRingOfIntegers_tmp K L) σ =
    @MulSemiringAction.toAlgHom Gal(L/K) (RingOfIntegers K) (RingOfIntegers L)
      _ _ _ _ (RingOfIntegers.instMulSemiringAction (K := L) (G := Gal(L/K)))
      (inferInstance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L)) σ := by
  apply AlgHom.ext
  intro a
  simpa only [MulSemiringAction.toAlgHom_apply] using
    s2462_smul_eq (K := K) (L := L) σ a

/-- Transport of IsArithFrobAt between the local S2440 action and the
ambient Mathlib action on O_L. -/
theorem s2462_isArithFrobAt_transport (σ : Gal(L/K)) (P : Ideal (RingOfIntegers L)) :
    @IsArithFrobAt (RingOfIntegers K) (RingOfIntegers L) _ _ _
      Gal(L/K) _ (instMulSemiringActionAlgEquivRingOfIntegers_tmp K L)
      (instSMulCommClassAlgEquivRingOfIntegers_tmp K L) σ P ↔
    @IsArithFrobAt (RingOfIntegers K) (RingOfIntegers L) _ _ _
      Gal(L/K) _ (RingOfIntegers.instMulSemiringAction (K := L) (G := Gal(L/K)))
      (inferInstance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L)) σ P := by
  unfold IsArithFrobAt
  rw [s2462_toAlgHom_eq]

#print axioms s2462_smul_eq
#print axioms s2462_toAlgHom_eq
#print axioms s2462_isArithFrobAt_transport

end LeanFormal.IUT.XiFPaper.S2462ActionTransportActual
end
