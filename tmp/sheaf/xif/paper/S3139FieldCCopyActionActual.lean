import tmp.sheaf.xif.paper.S3139FieldCArchimedeanLogActual
import tmp.sheaf.xif.paper.S3139FieldCConjugateActual
import tmp.sheaf.xif.paper.S3139FieldCArchimedeanBundleActual
import tmp.sheaf.xif.paper.S3139FieldCArchimedeanConsumerActual
import tmp.sheaf.xif.paper.S3139FieldCConjugateConsumerActual
import tmp.sheaf.xif.paper.S3139FieldCResidualSummaryActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# S3139: field (C) — paper-faithful Real copy action from the actual archimedean character

This file assembles the field-(C) construction: the actual Real scalar character
`sourceFmodArchimedeanScalarCharacter` of `F_mod^x` (from the production
`infinitePlaceLog` at a supplied infinite place) gives the paper-faithful
realified copy action data `SourceInd2CopyActionData` (task-27 shape): the
copies of `F_mod^x` act on the tensor packet by the independent per-factor
scalar actions, and the action preserves the splitting-monoid scalar action
(IUT III:616-620, Fig. I.5; the (Ind1)/(Ind2) non-interference of III:710-729
is transported through the linearity of the copy action).

To instantiate the data shape we prove the tensor-level action laws for the
actual `Ind2TensorActionActual.ind2TensorEquiv` (its unit and multiplicativity
laws on the whole tensor packet, by tensor induction; the paper's per-summand
action is only stated on pure tensors in the production file).

**Component, not paper object.**  Named future consumer: the first-triangle
mutation (`SourceMultiradialRepresentation`) and the lattice/mainline q/Theta
readouts.  The finite-place conjugate channel remains the exact missing datum
`SourceConjugateLocalUnitMap`.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139FieldCCopyActionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldACResidualActual
open LeanFormal.IUT.XiFPaper.S3139FieldCArchimedeanLogActual
open LeanFormal.IUT.XiFPaper.S3139FieldCConjugateActual
open scoped TensorProduct

universe ua uv upi umon ui uR u

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. Tensor-level action laws for the actual Ind2 action -/

section TensorLaws

variable {R : Type uR} [CommSemiring R]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {C : SourceProcessionCapsuleContract R l V I}
variable {j : Fin (capsuleLevels l)} {vQ : C.VQ}

/-- The actual tensor action of the unit copy family is the identity. -/
theorem ind2TensorEquiv_one_apply
    (x : SourceProcessionCapsuleContract.tensorPacket R C j vQ) :
    ind2TensorEquiv (C := C) (j := j) (vQ := vQ) 1 x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      rw [map_smul, ind2TensorEquiv_tprod]
      simp [ind2FactorAction_one]
  | add x y hx hy => rw [map_add, hx, hy]

/-- The actual tensor action of the unit copy family is the identity
(equivalence form). -/
theorem ind2TensorEquiv_one :
    ind2TensorEquiv (C := C) (j := j) (vQ := vQ) (1 : Capsule j.val → Rˣ) =
      LinearEquiv.refl R (SourceProcessionCapsuleContract.tensorPacket R C j vQ) := by
  ext x
  exact ind2TensorEquiv_one_apply x

/-- The actual tensor copy action is multiplicative: the product copy family
acts as the composite of the two copies. -/
theorem ind2TensorEquiv_mul_apply (f g : Capsule j.val → Rˣ)
    (x : SourceProcessionCapsuleContract.tensorPacket R C j vQ) :
    ind2TensorEquiv (C := C) (j := j) (vQ := vQ) (f * g) x =
      ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f
        (ind2TensorEquiv (C := C) (j := j) (vQ := vQ) g x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      repeat rw [map_smul]
      simp only [ind2TensorEquiv_tprod, Pi.mul_apply, ind2FactorAction_mul]
      congr 1
      congr 1
      funext i
      ext v
      simp [ind2FactorAction, scalarPiEquiv, smul_smul, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- The actual tensor copy action is multiplicative (equivalence form). -/
theorem ind2TensorEquiv_mul (f g : Capsule j.val → Rˣ) :
    ind2TensorEquiv (C := C) (j := j) (vQ := vQ) (f * g) =
      (ind2TensorEquiv (C := C) (j := j) (vQ := vQ) g).trans
        (ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f) := by
  ext x
  rw [LinearEquiv.trans_apply]
  exact ind2TensorEquiv_mul_apply f g x

end TensorLaws

/-! ## 2. Copy-action data from an actual Real scalar character -/

/-- A multiplicative Real scalar character of `F_mod^x` (e.g. the actual
archimedean character `sourceFmodArchimedeanScalarCharacter`) supplies the
paper-faithful `SourceInd2CopyActionData`: copies act by the independent
per-factor scalar actions, preserving the splitting-monoid scalar action. -/
noncomputable def sourceInd2CopyActionDataOfScalarCharacter
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (D : SourceLGPData Real l V I)
    (χ : (I.initial.arithmetic.Fmod)ˣ →* ℝˣ)
    (j : Fin (capsuleLevels l)) (vQ : D.capsule.VQ) :
    SourceInd2CopyActionData Real D j vQ
      (Capsule j.val → (I.initial.arithmetic.Fmod)ˣ) where
  action := fun f => ind2TensorEquiv (C := D.capsule) (j := j) (vQ := vQ)
    (fun i => χ (f i))
  action_one := by
    have h : (fun i => χ ((1 : Capsule j.val →
        (I.initial.arithmetic.Fmod)ˣ) i)) = (1 : Capsule j.val → ℝˣ) := by
      funext i
      simp
    rw [h]
    exact ind2TensorEquiv_one
  action_mul := by
    intro c d
    have hfun : (fun i => χ ((c * d) i)) =
        (fun i => χ (c i)) * (fun i => χ (d i)) := by
      funext i
      simp [Pi.mul_apply, map_mul]
    rw [hfun]
    exact ind2TensorEquiv_mul (fun i => χ (c i)) (fun i => χ (d i))
  action_scalar := by
    intro c g x
    show ind2TensorEquiv (C := D.capsule) (j := j) (vQ := vQ)
        (fun i => χ (c i)) (((D.action j).scalar g) • x) =
      ((D.action j).scalar g) •
        ind2TensorEquiv (C := D.capsule) (j := j) (vQ := vQ)
          (fun i => χ (c i)) x
    exact (ind2TensorEquiv (C := D.capsule) (j := j) (vQ := vQ)
      (fun i => χ (c i))).map_smul ((D.action j).scalar g) x

/-- The paper-faithful copy action data built from the *actual* archimedean
Real character of `F_mod^x` (chosen infinite place of the actual `F_mod`). -/
noncomputable def sourceArchimedeanCopyActionData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (D : SourceLGPData Real l V I)
    (c : SourceInfinitePlaceChoice I.initial.arithmetic)
    (j : Fin (capsuleLevels l)) (vQ : D.capsule.VQ) :
    SourceInd2CopyActionData Real D j vQ
      (Capsule j.val → (I.initial.arithmetic.Fmod)ˣ) :=
  sourceInd2CopyActionDataOfScalarCharacter I D
    (sourceInfinitePlaceScalarCharacter I.initial.arithmetic c) j vQ

end LeanFormal.IUT.XiFPaper.S3139FieldCCopyActionActual

end
