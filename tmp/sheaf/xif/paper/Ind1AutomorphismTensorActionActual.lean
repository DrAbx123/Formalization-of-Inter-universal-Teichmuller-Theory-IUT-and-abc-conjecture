import tmp.sheaf.xif.paper.MultiradialProcessionActual

/-!
# Actual PrcAutomorphism action on the tensor packet

The Ind1 automorphism of the source procession acts on the actual tensor packet
by the canonical tensor re-indexing determined by its capsule permutation.
No shell identification is invented: this is the literal tensor-factor
permutation action, and the underlying linear equivalence is
`PiTensorProduct.reindex`.

The file proves the unit and linearity laws and the pure-tensor formula.  The
component unit/composition laws of `PrcAutomorphism.ofPerm` are supplied by
the actual source links in `Ind1ActionLawsActual`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace Ind1AutomorphismTensorActionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open scoped TensorProduct

universe ua uv upi umon ui uR uVQ uPlace uShell

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

section Action

variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ)

/-- The literal Ind1 action of a source procession automorphism on the actual
tensor packet: tensor re-indexing by the capsule permutation. -/
noncomputable def PrcAutomorphismTensorAction
    (P : PrcAutomorphism A j) :
    ActualTensorPacket C j vQ ≃ₗ[Real]
      (⨂[Real] i : Capsule j.val,
        DirectSumFactor (C.logShell j) vQ (P.perm.symm i)) :=
  PiTensorProduct.reindex (R := Real)
    (s := fun i => DirectSumFactor (C.logShell j) vQ i) (e := P.perm)

@[simp] theorem PrcAutomorphismTensorAction_id
    (x : ActualTensorPacket C j vQ) :
    PrcAutomorphismTensorAction A C j vQ (PrcAutomorphism.id A j) x = x := by
  change PiTensorProduct.reindex (R := Real)
    (s := fun i => DirectSumFactor (C.logShell j) vQ i)
    (e := Equiv.refl (Capsule j.val)) x = x
  rw [PiTensorProduct.reindex_refl]
  rfl

theorem PrcAutomorphismTensorAction_map_add
    (P : PrcAutomorphism A j) (x y : ActualTensorPacket C j vQ) :
    PrcAutomorphismTensorAction A C j vQ P (x + y) =
      PrcAutomorphismTensorAction A C j vQ P x +
        PrcAutomorphismTensorAction A C j vQ P y :=
  map_add (PrcAutomorphismTensorAction A C j vQ P) x y

theorem PrcAutomorphismTensorAction_map_smul
    (P : PrcAutomorphism A j) (a : Real) (x : ActualTensorPacket C j vQ) :
    PrcAutomorphismTensorAction A C j vQ P (a • x) =
      a • PrcAutomorphismTensorAction A C j vQ P x :=
  map_smul (PrcAutomorphismTensorAction A C j vQ P) a x

theorem PrcAutomorphismTensorAction_tprod
    (P : PrcAutomorphism A j)
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    PrcAutomorphismTensorAction A C j vQ P
        (PiTensorProduct.tprod Real x) =
      PiTensorProduct.tprod Real (fun i => x (P.perm.symm i)) := by
  rw [PrcAutomorphismTensorAction, PiTensorProduct.reindex_tprod]

end Action

end Ind1AutomorphismTensorActionActual
end LeanFormal.IUT.XiFPaper
end
