import tmp.sheaf.xif.paper.S3139C2LocalDegreeDataActual
import tmp.sheaf.xif.paper.Ind2TensorActionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

/-!
# S3139: C2 — finite-place copy action from the local element map (light module)

Given the exact missing C2 datum `SourceFmodLocalElementMap` and the capsule
fiber assignment, this module constructs the finite-place copy action data
`SourceInd2CopyActionData` from the actual per-factor action
`Ind2TensorActionActual.ind2TensorEquiv`, after proving its tensor-level unit
and multiplicativity laws by tensor induction.  The complete copy-action
interface `SourceCopyActionChannels` records the finite-place channel together
with a supplied archimedean channel (constructed separately in
`S3139FieldCCopyActionActual`), so it composes without a heavy import chain.

**Component, not paper object.**  Named consumers: first-triangle mutation,
lattice/mainline q/Theta comparison.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139C2FiniteCopyActionLightActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.S3139FirstTriangleFieldACResidualActual
open LeanFormal.IUT.XiFPaper.S3139FieldCConjugateActual
open LeanFormal.IUT.XiFPaper.S3139C2LocalDegreeDataActual
open scoped TensorProduct

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}

/-! ## 1. Tensor-level laws for the actual Ind2 action (light re-proof) -/

section TensorLaws

variable {R : Type*} [CommSemiring R]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {C : SourceProcessionCapsuleContract R l V I}
variable {j : Fin (capsuleLevels l)} {vQ : C.VQ}

/-- The actual tensor copy action of the unit copy family is the identity. -/
theorem lightInd2_one_apply
    (x : SourceProcessionCapsuleContract.tensorPacket R C j vQ) :
    ind2TensorEquiv (C := C) (j := j) (vQ := vQ) 1 x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      rw [map_smul, ind2TensorEquiv_tprod]
      simp [ind2FactorAction_one]
  | add x y hx hy => rw [map_add, hx, hy]

/-- The actual tensor copy action of the unit copy family is the identity
(equivalence form). -/
theorem lightInd2_one :
    ind2TensorEquiv (C := C) (j := j) (vQ := vQ) (1 : Capsule j.val → Rˣ) =
      LinearEquiv.refl R (SourceProcessionCapsuleContract.tensorPacket R C j vQ) := by
  ext x
  exact lightInd2_one_apply x

/-- The actual tensor copy action is multiplicative on pure tensors. -/
theorem lightInd2_mul_apply (f g : Capsule j.val → Rˣ)
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
theorem lightInd2_mul (f g : Capsule j.val → Rˣ) :
    ind2TensorEquiv (C := C) (j := j) (vQ := vQ) (f * g) =
      (ind2TensorEquiv (C := C) (j := j) (vQ := vQ) g).trans
        (ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f) := by
  ext x
  rw [LinearEquiv.trans_apply]
  exact lightInd2_mul_apply f g x

end TensorLaws

/-! ## 2. The finite-place copy action -/

/-- The exact missing fiber-assignment datum: capsule labels assigned to the
prime-strip fibers (placeToMod/cusp alignment, III:616-620). -/
structure SourceCapsuleFiberAssignment (V : Type uv) (j : Fin (capsuleLevels l)) where
  fiber : Capsule j.val → V

/-- The realified unit of the unit copy at one fiber is the unit. -/
theorem localScalarUnit_one
    {F : FPrimeStrip.{umon, uv, upi} V}
    {A : LeanFormal.IUT.InitialThetaArithmeticData.{ui} l}
    (D : SourceFmodLocalElementMap (l := l) (V := V) F A) (v : V) :
    D.localScalarUnit 1 v = 1 := by
  apply Units.ext
  show Real.exp (Multiplicative.toAdd (D.localDegree 1 v)) = 1
  rw [D.localDegree_one]
  simp

/-- The finite-place copy action data constructed from the local element map. -/
noncomputable def sourceFinitePlaceCopyActionData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (Dlgp : SourceLGPData Real l V I)
    {F : FPrimeStrip.{umon, uv, upi} V}
    (D : SourceFmodLocalElementMap (l := l) (V := V) F
      I.initial.arithmetic)
    (j : Fin (capsuleLevels l)) (vQ : Dlgp.capsule.VQ)
    (σ : SourceCapsuleFiberAssignment (l := l) V j) :
    SourceInd2CopyActionData Real Dlgp j vQ
      (I.initial.arithmetic.Fmod)ˣ where
  action := fun c => ind2TensorEquiv (C := Dlgp.capsule) (j := j) (vQ := vQ)
    (fun i => D.localScalarUnit c (σ.fiber i))
  action_one := by
    have h : (fun i => D.localScalarUnit (1 : (I.initial.arithmetic.Fmod)ˣ)
        (σ.fiber i)) = (1 : Capsule j.val → ℝˣ) := by
      funext i
      exact localScalarUnit_one D (σ.fiber i)
    rw [h]
    exact lightInd2_one
  action_mul := by
    intro c d
    have hfun : (fun i => D.localScalarUnit (c * d) (σ.fiber i)) =
        (fun i => D.localScalarUnit c (σ.fiber i)) *
          (fun i => D.localScalarUnit d (σ.fiber i)) := by
      funext i
      exact D.localScalarUnit_mul c d (σ.fiber i)
    rw [hfun]
    exact lightInd2_mul (fun i => D.localScalarUnit c (σ.fiber i))
      (fun i => D.localScalarUnit d (σ.fiber i))
  action_scalar := by
    intro c g x
    show ind2TensorEquiv (C := Dlgp.capsule) (j := j) (vQ := vQ)
        (fun i => D.localScalarUnit c (σ.fiber i))
        (((Dlgp.action j).scalar g) • x) =
      ((Dlgp.action j).scalar g) •
        ind2TensorEquiv (C := Dlgp.capsule) (j := j) (vQ := vQ)
          (fun i => D.localScalarUnit c (σ.fiber i)) x
    exact (ind2TensorEquiv (C := Dlgp.capsule) (j := j) (vQ := vQ)
      (fun i => D.localScalarUnit c (σ.fiber i))).map_smul
        ((Dlgp.action j).scalar g) x

/-- The complete first-triangle copy-action interface: a supplied archimedean
channel (constructed in the field-(C) modules) together with the finite-place
channel constructed from the exact missing C2 data. -/
structure SourceCopyActionChannels
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (Dlgp : SourceLGPData Real l V I)
    {F : FPrimeStrip.{umon, uv, upi} V}
    (j : Fin (capsuleLevels l)) (vQ : Dlgp.capsule.VQ) where
  /-- the supplied archimedean realified copy action -/
  archimedean : SourceInd2CopyActionData Real Dlgp j vQ
    (Capsule j.val → (I.initial.arithmetic.Fmod)ˣ)
  /-- the finite-place conjugate local element map (exact missing datum) -/
  localElementMap : SourceFmodLocalElementMap (l := l) (V := V) F
    I.initial.arithmetic
  /-- the capsule-label to fiber assignment (exact missing datum) -/
  fiberAssignment : SourceCapsuleFiberAssignment (l := l) V j
  /-- the finite-place realified copy action (constructed from the data) -/
  finitePlace : SourceInd2CopyActionData Real Dlgp j vQ
    (I.initial.arithmetic.Fmod)ˣ
  finitePlace_eq : finitePlace =
    sourceFinitePlaceCopyActionData I Dlgp localElementMap j vQ fiberAssignment

/-- Assemble the complete copy-action interface from a supplied archimedean
channel and the exact C2 data. -/
noncomputable def sourceCopyActionChannels
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (Dlgp : SourceLGPData Real l V I)
    {F : FPrimeStrip.{umon, uv, upi} V}
    (D : SourceFmodLocalElementMap (l := l) (V := V) F
      I.initial.arithmetic)
    (j : Fin (capsuleLevels l)) (vQ : Dlgp.capsule.VQ)
    (arch : SourceInd2CopyActionData Real Dlgp j vQ
      (Capsule j.val → (I.initial.arithmetic.Fmod)ˣ))
    (σ : SourceCapsuleFiberAssignment (l := l) V j) :
    SourceCopyActionChannels (F := F) I Dlgp j vQ where
  archimedean := arch
  localElementMap := D
  fiberAssignment := σ
  finitePlace := sourceFinitePlaceCopyActionData I Dlgp D j vQ σ
  finitePlace_eq := rfl

end LeanFormal.IUT.XiFPaper.S3139C2FiniteCopyActionLightActual

end
