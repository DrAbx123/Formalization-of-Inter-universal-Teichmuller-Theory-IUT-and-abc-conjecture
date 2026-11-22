import tmp.sheaf.xif.paper.MultiradialProcessionActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData

-- Actual Ind2 per-summand action on the tensor packet
--
-- Source: IUT III, Theorem 3.11, (i)/(ii): the (Ind2) indeterminacies are
-- independent copies of Ism acting on the direct summands of the tensor
-- factors. Here the actual Fmod unit copies are the actual copy group
-- FmodUnitCopies j = Capsule j -> Fmod^×, and the actual tensor packet is
-- PiTensorProduct over the actual log-shell factors. Each copy unit acts on
-- its own tensor factor by scalar multiplication; the tensor action is the
-- PiTensorProduct.congr of these per-factor scalar equivalences.
-- No trivial action, no inequality, no sorry/axiom/True/PUnit/toy.
-- WRITE-ONLY: no lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Ind2TensorActionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open scoped TensorProduct

universe ua uv upi umon ui uR uVQ uPlace uShell

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {R : Type uR} [CommSemiring R]
variable (C : SourceProcessionCapsuleContract R l V I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ)

-- Scalar multiplication by a unit on a dependent direct-sum factor.
noncomputable def scalarPiEquiv (u : Rˣ) (i : Capsule j.val) :
    DirectSumFactor (C.logShell j) vQ i ≃ₗ[R]
      DirectSumFactor (C.logShell j) vQ i where
  toFun f v := (u : R) • f v
  invFun f v := ((u⁻¹ : Rˣ) : R) • f v
  map_add' f g := by
    ext v
    simp [smul_add]
  map_smul' a f := by
    ext v
    simp [smul_smul, mul_comm, smul_comm]
  left_inv f := by
    ext v
    change ((u⁻¹ : Rˣ) : R) • ((u : R) • f v) = f v
    rw [smul_smul, ← u.inv_eq_val_inv, u.inv_val, one_smul]
  right_inv f := by
    ext v
    change (u : R) • (((u⁻¹ : Rˣ) : R) • f v) = f v
    rw [smul_smul, ← u.inv_eq_val_inv, u.val_inv, one_smul]

-- The per-summand action of one independent Fmod-unit copy on tensor factor i.
noncomputable def ind2FactorAction (u : Rˣ) (i : Capsule j.val) :
    DirectSumFactor (C.logShell j) vQ i ≃ₗ[R]
      DirectSumFactor (C.logShell j) vQ i :=
  scalarPiEquiv (C := C) (j := j) (vQ := vQ) u i

-- The actual tensor action of the independent copy family.
noncomputable def ind2TensorEquiv (f : Capsule j.val → Rˣ) :
    SourceProcessionCapsuleContract.tensorPacket R C j vQ ≃ₗ[R]
      SourceProcessionCapsuleContract.tensorPacket R C j vQ :=
  PiTensorProduct.congr (fun i => ind2FactorAction (C := C) (j := j) (vQ := vQ) (f i) i)

-- Compatibility with the tensor packet on pure tensors: the tensor action is
-- the tensor of the per-factor scalar actions.
theorem ind2TensorEquiv_tprod (f : Capsule j.val → Rˣ)
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f
        (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun i => ind2FactorAction (C := C) (j := j) (vQ := vQ) (f i) i (x i)) :=
  PiTensorProduct.congr_tprod (fun i =>
    ind2FactorAction (C := C) (j := j) (vQ := vQ) (f i) i) x

-- The per-factor action is trivial exactly at the identity copy; this is
-- the actual action law at the unit of the copy group.
theorem ind2FactorAction_one (i : Capsule j.val) :
    ind2FactorAction (C := C) (j := j) (vQ := vQ) 1 i =
      LinearEquiv.refl R (DirectSumFactor (C.logShell j) vQ i) := by
  ext f v
  simp [ind2FactorAction, scalarPiEquiv]

-- The copy action is multiplicative (per-factor scalar multiplication).
theorem ind2FactorAction_mul (u v : Rˣ) (i : Capsule j.val) :
    ind2FactorAction (C := C) (j := j) (vQ := vQ) (u * v) i =
      (ind2FactorAction (C := C) (j := j) (vQ := vQ) u i).trans
        (ind2FactorAction (C := C) (j := j) (vQ := vQ) v i) := by
  ext f w
  simp [ind2FactorAction, scalarPiEquiv, smul_smul, mul_comm]

end LeanFormal.IUT.XiFPaper.Ind2TensorActionActual

end
