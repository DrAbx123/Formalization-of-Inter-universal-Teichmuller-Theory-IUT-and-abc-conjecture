import tmp.sheaf.xif.paper.MultiradialProcessionActual

/-!
# Actual Ind1 action laws

The actual (Ind1) tensor action is the contract's `PolyIsoAction.tensorMap`.
This file proves its linearity and pure-tensor compatibility, the actual
unit law for the identity poly-isomorphism, and the actual component laws for
`PrcAutomorphism.ofPerm` built from the source links.

No inequality is judged; no arbitrary action or missing-only record is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace Ind1ActionLawsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsuleContract
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open scoped TensorProduct

universe ua uv upi umon ui uR uVQ uPlace uShell

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

section SourceLinks

variable (A : CapsuleTheaterAssignment l V I) (j : Fin (capsuleLevels l))

@[simp] theorem PrcAutomorphism.ofPerm_component
    (sigma : Capsule j.val ≃ Capsule j.val) (i : Capsule j.val) :
    (PrcAutomorphism.ofPerm A j sigma).component i =
      PrcTransition A j i (sigma i) := rfl

@[simp] theorem PrcAutomorphism.ofPerm_id_component (i : Capsule j.val) :
    (PrcAutomorphism.ofPerm A j (Equiv.refl (Capsule j.val))).component i =
      FPrimeStripEquiv.refl (PrcMember A j i) := by
  rw [PrcAutomorphism.ofPerm_component, PrcTransition_refl]

@[simp] theorem PrcAutomorphism.ofPerm_comp_component
    (sigma tau : Capsule j.val ≃ Capsule j.val) (i : Capsule j.val) :
    (PrcAutomorphism.ofPerm A j (sigma.trans tau)).component i =
      (PrcAutomorphism.comp A j (PrcAutomorphism.ofPerm A j sigma)
        (PrcAutomorphism.ofPerm A j tau)).component i := by
  simp [PrcAutomorphism.ofPerm, PrcAutomorphism.comp, PrcTransition_trans]

end SourceLinks

section TensorAction

variable {R : Type uR} [CommSemiring R]
variable (C : SourceProcessionCapsuleContract R l V I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ)

@[simp] theorem Ind1TensorAction_apply (x : ActualTensorPacket C j vQ) :
    Ind1TensorAction C j vQ x = (C.polyIso j).tensorMap vQ x := rfl

theorem Ind1TensorAction_map_add
    (x y : ActualTensorPacket C j vQ) :
    Ind1TensorAction C j vQ (x + y) =
      Ind1TensorAction C j vQ x + Ind1TensorAction C j vQ y :=
  map_add (Ind1TensorAction C j vQ) x y

theorem Ind1TensorAction_map_smul (a : R) (x : ActualTensorPacket C j vQ) :
    Ind1TensorAction C j vQ (a • x) =
      a • Ind1TensorAction C j vQ x :=
  map_smul (Ind1TensorAction C j vQ) a x

theorem Ind1TensorAction_tprod
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    Ind1TensorAction C j vQ (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R
        (fun i => (C.polyIso j).localFactorEquiv vQ i (x i)) :=
  PolyIsoAction.tensorMap_tprod (C.polyIso j) vQ x

def Ind1UnitAction : PolyIsoAction (C.logShell j) :=
  PolyIsoAction.refl (C.logShell j)

theorem Ind1UnitAction_tprod
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    (Ind1UnitAction C j).tensorMap vQ (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R x := by
  rw [PolyIsoAction.tensorMap_tprod]
  simp [Ind1UnitAction, PolyIsoAction.refl]

end TensorAction

end Ind1ActionLawsActual
end LeanFormal.IUT.XiFPaper
end
