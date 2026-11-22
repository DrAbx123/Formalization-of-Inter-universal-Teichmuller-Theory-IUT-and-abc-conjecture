import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open Polynomial NumberField
namespace LeanFormal.IUT.XiFPaper.S2463ActionTransportActual

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

noncomputable abbrev s2463ActionA : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instMulSemiringActionAlgEquivRingOfIntegers_tmp K L
noncomputable abbrev s2463ActionG : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  RingOfIntegers.instMulSemiringAction L

/-- The `SMul` underlying a `MulSemiringAction`; used to state the matching `SMulCommClass`
without depending on the ambient action instance. -/
noncomputable abbrev s2463ActionSMul (i : MulSemiringAction Gal(L/K) (RingOfIntegers L)) :
    SMul Gal(L/K) (RingOfIntegers L) :=
  i.toDistribMulAction.toDistribSMul.toSMul

/-- The scalar `SMul (𝓞 K) (𝓞 L)` given by the `Algebra` structure. -/
noncomputable abbrev s2463AlgebraSMul : SMul (RingOfIntegers K) (RingOfIntegers L) := inferInstance

noncomputable abbrev s2463SmulCommA :
    @SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L)
      (s2463ActionSMul K L (s2463ActionA K L)) (s2463AlgebraSMul K L) :=
  LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual.instSMulCommClassAlgEquivRingOfIntegers_tmp K L

noncomputable abbrev s2463SmulCommG :
    @SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L)
      (s2463ActionSMul K L (s2463ActionG K L)) (s2463AlgebraSMul K L) :=
  inferInstance

theorem s2463_smul_eq (sigma : Gal(L/K)) (a : RingOfIntegers L) :
    (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) := s2463ActionA K L
     letI : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) := s2463SmulCommA K L
     sigma • a) =
    (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) := s2463ActionG K L
     letI : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) := s2463SmulCommG K L
     sigma • a) := by
  letI iA : MulSemiringAction Gal(L/K) (RingOfIntegers L) := s2463ActionA K L
  letI iAg : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) := s2463SmulCommA K L
  have hA : algebraMap (RingOfIntegers L) L (sigma • a) =
      sigma (algebraMap (RingOfIntegers L) L a) := by
    rw [show sigma • a =
      (galRestrict (RingOfIntegers K) K L (RingOfIntegers L)) sigma a from rfl]
    exact algebraMap_galRestrict_apply (RingOfIntegers K) sigma a
  apply RingOfIntegers.coe_injective
  show algebraMap (RingOfIntegers L) L (sigma • a) = algebraMap (RingOfIntegers L) L
    (letI : MulSemiringAction Gal(L/K) (RingOfIntegers L) := s2463ActionG K L
     letI : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) := s2463SmulCommG K L
     sigma • a)
  rw [hA]
  rfl

theorem s2463_toAlgHom_eq (sigma : Gal(L/K)) :
    @MulSemiringAction.toAlgHom Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) _ _ _ _
      (s2463ActionA K L) (s2463SmulCommA K L) sigma =
    @MulSemiringAction.toAlgHom Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) _ _ _ _
      (s2463ActionG K L) (s2463SmulCommG K L) sigma := by
  apply AlgHom.ext
  intro a
  rw [MulSemiringAction.toAlgHom_apply, MulSemiringAction.toAlgHom_apply]
  exact s2463_smul_eq K L sigma a

theorem s2463_isArithFrobAt_iff (sigma : Gal(L/K)) (P : Ideal (RingOfIntegers L)) :
    @IsArithFrobAt (RingOfIntegers K) (RingOfIntegers L) _ _ _ Gal(L/K) _
      (s2463ActionA K L) (s2463SmulCommA K L) sigma P ↔
    @IsArithFrobAt (RingOfIntegers K) (RingOfIntegers L) _ _ _ Gal(L/K) _
      (s2463ActionG K L) (s2463SmulCommG K L) sigma P := by
  unfold IsArithFrobAt
  rw [s2463_toAlgHom_eq K L sigma]

#print axioms s2463_smul_eq
#print axioms s2463_toAlgHom_eq
#print axioms s2463_isArithFrobAt_iff

end LeanFormal.IUT.XiFPaper.S2463ActionTransportActual
end
