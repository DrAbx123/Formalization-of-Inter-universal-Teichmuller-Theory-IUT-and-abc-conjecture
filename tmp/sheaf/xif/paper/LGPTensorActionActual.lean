import tmp.sheaf.xif.paper.Ind2TensorActionActual
import tmp.sheaf.xif.paper.Ind1QuotientActual

-- Actual LGP scalar action on the actual tensor packet
--
-- Source: IUT III, Theorem 3.11, (i), (b); the LGP splitting monoid acts on
-- the tensor packet through its scalar action. Here the actual scalar is
-- sourceLGPScalar : Multiplicative Real -> Real (the actual theta-packet
-- exponential), and the action is the per-factor scalar action of its unit
-- on the actual tensor packet. This file constructs the actual action and
-- proves it commutes with the actual Ind1 tensor action.
-- No artificial product carrier; no inequality; no sorry/axiom/True/PUnit/toy.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.LGPTensorActionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open scoped TensorProduct

universe ua uv upi umon ui uVQ uPlace uShell

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ)

-- The actual LGP scalar as a unit of Real.
def lgpUnit (g : Multiplicative Real) : Realˣ :=
  Units.mk0 (sourceLGPScalar (I := I) g) (ne_of_gt (by
    change 0 < Real.exp g.toAdd
    exact Real.exp_pos _))

-- Actual LGP scalar action on the tensor packet.
noncomputable def lgpTensorEquiv (g : Multiplicative Real) :
    SourceProcessionCapsuleContract.tensorPacket Real C j vQ ≃ₗ[Real]
      SourceProcessionCapsuleContract.tensorPacket Real C j vQ :=
  PiTensorProduct.congr (fun i =>
    scalarPiEquiv (C := C) (j := j) (vQ := vQ) (lgpUnit (I := I) g) i)

-- Actual LGP scalar action on the Ind1-permuted tensor packet.
noncomputable def lgpTensorEquivPermuted (g : Multiplicative Real) :
    (⨂[Real] i : Capsule j.val,
      DirectSumFactor (C.logShell j) vQ ((C.polyIso j).labelPerm i)) ≃ₗ[Real]
    (⨂[Real] i : Capsule j.val,
      DirectSumFactor (C.logShell j) vQ ((C.polyIso j).labelPerm i)) :=
  PiTensorProduct.congr (fun i =>
    scalarPiEquiv (C := C) (j := j) (vQ := vQ) (lgpUnit (I := I) g)
      ((C.polyIso j).labelPerm i))

-- Actual tensor compatibility of the LGP action on pure tensors.
theorem lgpTensorEquiv_tprod (g : Multiplicative Real)
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    lgpTensorEquiv (I := I) C j vQ g (PiTensorProduct.tprod Real x) =
      PiTensorProduct.tprod Real
        (fun i => (lgpUnit (I := I) g : Real) • x i) := by
  simp [lgpTensorEquiv, PiTensorProduct.congr_tprod, scalarPiEquiv]

-- The actual LGP action and the actual Ind1 tensor action commute.
theorem ind1_lgp_tensor_commute (g : Multiplicative Real) :
    (lgpTensorEquivPermuted (I := I) C j vQ g).toLinearMap.comp
        (Ind1TensorAction (C := C) (j := j) (vQ := vQ)) =
      (Ind1TensorAction (C := C) (j := j) (vQ := vQ)).comp
        (lgpTensorEquiv (I := I) C j vQ g).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp [Ind1TensorAction, tensorMap_tprod, lgpTensorEquiv,
      lgpTensorEquivPermuted, scalarPiEquiv, PiTensorProduct.congr_tprod,
      PiTensorProduct.tprod_smul]
  | add x y hx hy =>
    simp [map_add, hx, hy]

#check lgpUnit
#check lgpTensorEquiv
#check lgpTensorEquivPermuted
#check lgpTensorEquiv_tprod
#check ind1_lgp_tensor_commute

end LeanFormal.IUT.XiFPaper.LGPTensorActionActual

end