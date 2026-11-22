import tmp.sheaf.xif.paper.S2063BaseAlgebraBridgeActual

-- S2064: group-level S2047GaloisEquivRequired via closure conjugation,
-- using the actual S2063 base/closure equivalences.  No fake.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2064GaloisEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
open LeanFormal.IUT.XiFPaper.S2063BaseAlgebraBridgeActual
open LeanFormal.IUT.XiFPaper.S2045OperationKummerActual

variable (v : FinitePrimePlace 2 7)
local instance (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) := ⟨v.prime⟩

noncomputable abbrev S2064BaseEquiv :
    Iut.SourceFinitePlaceReconstruction.Base (QPlace v) ≃+* ℚ_[v.1] :=
  (galoisEquivOfBaseData (v := v)).baseEquiv

noncomputable abbrev S2064ClosureEquiv :
    AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)) ≃+*
      AlgebraicClosure ℚ_[v.1] :=
  (galoisEquivOfBaseData (v := v)).closureEquiv

theorem S2064ClosureEquiv_algebraMap
    (x : Iut.SourceFinitePlaceReconstruction.Base (QPlace v)) :
    S2064ClosureEquiv (v := v) (algebraMap _ _ x) =
      algebraMap _ _ (S2064BaseEquiv (v := v) x) :=
  (galoisEquivOfBaseData (v := v)).closure_compat x

noncomputable def S2064ConjRing (σ : Gv v) :
    AlgebraicClosure ℚ_[v.1] ≃+* AlgebraicClosure ℚ_[v.1] :=
  (S2064ClosureEquiv (v := v)).symm.trans σ.toRingEquiv |>.trans
    (S2064ClosureEquiv (v := v))

noncomputable def S2064ToLocal (σ : Gv v) : LocalAbsoluteGalois v.1 :=
  AlgEquiv.ofRingEquiv (f := S2064ConjRing (v := v) σ) (by
    intro r
    obtain ⟨x, rfl⟩ := (S2064BaseEquiv (v := v)).surjective r
    simp only [S2064ConjRing, RingEquiv.trans_apply,
      AlgEquiv.coe_ringEquiv]
    rw [← S2064ClosureEquiv_algebraMap (v := v) x]
    simp only [RingEquiv.symm_apply_apply]
    rw [AlgEquiv.commutes]
  )

noncomputable def S2064ConjRingInv (τ : LocalAbsoluteGalois v.1) :
    AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)) ≃+*
      AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)) :=
  (S2064ClosureEquiv (v := v)).trans τ.toRingEquiv |>.trans
    (S2064ClosureEquiv (v := v)).symm

noncomputable def S2064ToGv (τ : LocalAbsoluteGalois v.1) : Gv v :=
  AlgEquiv.ofRingEquiv (f := S2064ConjRingInv (v := v) τ) (by
    intro x
    simp only [S2064ConjRingInv, RingEquiv.trans_apply, RingEquiv.symm_apply_apply,
      AlgEquiv.coe_ringEquiv]
    rw [S2064ClosureEquiv_algebraMap (v := v) x]
    rw [AlgEquiv.commutes]
    rw [← S2064ClosureEquiv_algebraMap (v := v) x]
    exact RingEquiv.symm_apply_apply (S2064ClosureEquiv (v := v)) (algebraMap _ _ x)
  )

noncomputable def S2064GaloisEquiv : Gv v ≃* LocalAbsoluteGalois v.1 where
  toFun := S2064ToLocal (v := v)
  invFun := S2064ToGv (v := v)
  left_inv σ := by
    apply AlgEquiv.ext
    intro x
    simp [S2064ToLocal, S2064ToGv, S2064ConjRing, S2064ConjRingInv,
      AlgEquiv.trans_apply]
  right_inv τ := by
    apply AlgEquiv.ext
    intro x
    simp [S2064ToLocal, S2064ToGv, S2064ConjRing, S2064ConjRingInv,
      AlgEquiv.trans_apply]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    simp [S2064ToLocal, S2064ConjRing, AlgEquiv.trans_apply, mul_apply]

/-- The group-level S2045GaloisEquiv / S2046GaloisEquivRequired, in the orientation
required by S2045/S2046. -/
noncomputable abbrev S2064S2045GaloisEquiv :
    S2045GaloisEquiv (v := v) :=
  (S2064GaloisEquiv (v := v)).symm

#check S2064GaloisEquiv
#check S2064S2045GaloisEquiv
#print axioms S2064GaloisEquiv
#print axioms S2064S2045GaloisEquiv

end LeanFormal.IUT.XiFPaper.S2064GaloisEquivActual

end