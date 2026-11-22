import tmp.sheaf.xif.paper.PaperSourceThetaConsistencyActual
import tmp.sheaf.n8.closure.C3Roots
import tmp.sheaf.xif.paper.PaperC3TensorGeometryActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import tmp.sheaf.n8.closure.SourcePilotRegion

-- E6: q/theta consistency from the actual qVFamily q.
-- qUnit := qVFamily q unit; thetaPacket := sourceThetaPacketFromQ (norm of
-- that same qUnit).  No Classical.choice q and no sourceTheater packet.
-- Root-valued paper theta q_v^(j^2), q_v=q^(1/2l), is recorded with its
-- exact root relation.  The remaining SourcePilotRegionData q-candidate and
-- tensor-block fields are an exact gap, not fabricated.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorGeometryActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.LocalFieldPadicTensor

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- The actual qVFamily q unit and its norm-derived theta packet.
abbrev sourceQUnit : CompletionValueCarrier (sourceThetaPlace T b) :=
  sourceQVFamilyUnit T b

abbrev sourceQThetaPacket : FiniteThetaPacket l :=
  sourceThetaPacketFromQ T b

theorem sourceQThetaPacket_q_eq_norm :
    (sourceQThetaPacket (l := l) T b).q =
      ‖(sourceQUnit T b : CommonPrimeCompletion (sourceThetaPlace T b))‖ :=
  sourceThetaPacketFromQ_q (l := l) T b

-- Actual same-q consistency structure.
structure SourceQThetaConsistency where
  qUnit : CompletionValueCarrier (sourceThetaPlace T b)
  thetaPacket : FiniteThetaPacket l
  thetaPacket_q_eq_norm :
    thetaPacket.q =
      ‖(qUnit : CommonPrimeCompletion (sourceThetaPlace T b))‖

noncomputable def sourceQThetaConsistency :
    SourceQThetaConsistency (l := l) T b where
  qUnit := sourceQUnit T b
  thetaPacket := sourceQThetaPacket T b
  thetaPacket_q_eq_norm := sourceQThetaPacket_q_eq_norm T b

-- Root-valued paper theta: q_v = q^(1/(2l)); theta_j = q_v^(j^2).
abbrev sourceQRootSystem :
    NatRootSystem (unitToAlgClosed (sourceQUnit T b)) :=
  algClosedRootSystem (sourceQUnit T b)

noncomputable def sourceQRootUnit :
    (AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b)))ˣ :=
  (sourceQRootSystem T b).root (2 * l.value)

theorem sourceQRootUnit_pow :
    (sourceQRootUnit T b :
      AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b))) ^
      (2 * l.value) =
      (unitToAlgClosed (sourceQUnit T b) :
        AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b))) :=
  by
    change ((sourceQRootSystem T b).root (2 * l.value) :
      AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b))) ^
      (2 * l.value) = _
    exact congrArg
      (fun z : (AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b)))ˣ =>
        (z : AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b))))
      (NatRootSystem.pow_self (sourceQRootSystem T b) (2 * l.value)
        (Nat.mul_ne_zero (by norm_num) l.prime.ne_zero))

noncomputable def sourcePaperRootThetaUnit
    (j : SignedLabel l.value) :
    (AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b)))ˣ :=
  sourceQRootUnit T b ^ ((gaussExponent j.1).toNat ^ 2)

theorem sourcePaperRootThetaUnit_eq :
    sourcePaperRootThetaUnit (l := l) T b =
      fun j => sourceQRootUnit T b ^ ((gaussExponent j.1).toNat ^ 2) := rfl

-- Actual q candidate: directly the qVFamily q candidate.
noncomputable def sourceQDataQCand :
    FinitePlaceQCandidate (sourceThetaPlace T b).val :=
  qVFamily T b

abbrev SourceQTensorBlock : Type :=
  ArithmeticTensorTupleBlock (ι := PUnit) (V := fun _ : PUnit => Unit)
    (fun _ (_ : Unit) => sourceThetaPlace T b) (fun _ => ())

theorem sourceQDataQCand_q :
    (sourceQDataQCand T b).q = (qVFamily T b).q := rfl

-- Actual datum required by SourcePilotRegionData, with q/theta/qUnit filled
-- from qVFamily and sourceThetaPacketFromQ.  The tensor unit and tensor
-- landing are exact input data: no constant/trivial landing is invented.
structure SourcePilotRegionQData where
  tensorUnit : (SourceQTensorBlock T b)ˣ
  tensorLanding : CommonPrimeCompletion (sourceThetaPlace T b) →
    SourceQTensorBlock T b
  tensorLanding_q :
    tensorLanding (sourceQDataQCand T b).q =
      (Units.val tensorUnit)

noncomputable def sourcePilotRegionQData
    (tensorUnit : (SourceQTensorBlock T b)ˣ)
    (tensorLanding : CommonPrimeCompletion (sourceThetaPlace T b) →
      SourceQTensorBlock T b)
    (tensorLanding_q :
      tensorLanding (sourceQDataQCand T b).q =
        Units.val tensorUnit) :
    SourcePilotRegionQData T b where
  tensorUnit := tensorUnit
  tensorLanding := tensorLanding
  tensorLanding_q := tensorLanding_q

-- Actual q/theta/qUnit consistency of the completed data.
theorem sourcePilotRegionQData_theta_q :
    (sourceQThetaPacket (l := l) T b).q =
      ‖(sourceQUnit T b :
        CommonPrimeCompletion (sourceThetaPlace T b))‖ :=
  sourceQThetaPacket_q_eq_norm T b

theorem sourcePilotRegionQData_qUnit_eq :
    (sourceQUnit T b : CompletionValueCarrier (sourceThetaPlace T b)) =
      candidateUnits (K := T.arithmetic.F) (sourceThetaPlace T b)
        (sourceQDataQCand T b) := by
  rfl

-- Exact minimal tensor landing field: when no actual map is supplied, the
-- data structure keeps tensorUnit/tensorLanding as exact fields; no function
-- is fabricated.  The required tensor landing remains the only missing map.
structure SourcePilotRegionQTensorLandingGap where
  tensorLanding : CommonPrimeCompletion (sourceThetaPlace T b) →
    SourceQTensorBlock T b
  tensorUnit : (SourceQTensorBlock T b)ˣ
  tensorLanding_q : tensorLanding (sourceQDataQCand T b).q = Units.val tensorUnit

def SourcePilotRegionQTensorLandingGapRequired : Prop :=
  Nonempty (SourcePilotRegionQTensorLandingGap T b)
#check sourceQUnit
#check sourceQThetaPacket
#check sourceQThetaPacket_q_eq_norm
#check SourceQThetaConsistency
#check sourceQThetaConsistency
#check sourceQRootUnit
#check sourceQRootUnit_pow
#check sourcePaperRootThetaUnit
#check SourcePilotRegionQData

-- S62: actual one-factor tensor landing and tensor unit.
noncomputable def sourceQTensorLanding
    (x : CommonPrimeCompletion (sourceThetaPlace T b)) :
    SourceQTensorBlock T b :=
  finitePadicTensorTprod (p := qVFamTensorP T b)
    (fun _ : PUnit => CommonPrimeCompletion (sourceThetaPlace T b))
    (fun _ => x)

-- S62 exact result: the actual one-factor tensor map is sourceQTensorLanding.
-- The remaining tensorUnit/tensorLanding_q compatibility is exactly
-- SourcePilotRegionQTensorLandingGap; it is not collapsed to tensorUnit=1
-- because the pure tensor of q is not definitionally 1.

-- S140: direct actual tensorUnit from the pure tensor q, no LinearEquiv-as-ring-hom.
noncomputable def sourceQTensorUnit : (SourceQTensorBlock T b)ˣ :=
  Units.mkOfMulEqOne (sourceQTensorLanding T b (sourceQDataQCand T b).q)
    (sourceQTensorLanding T b ((sourceQDataQCand T b).q)⁻¹)
    (by
      have h := finitePadicTensorTprod_mul_tprod
        (p := qVFamTensorP T b)
        (ι := PUnit) (V := fun _ : PUnit => Unit)
        (places := fun _ _ => sourceThetaPlace T b)
        (tuple := fun _ => ())
        (x := fun _ => (sourceQDataQCand T b).q)
        (y := fun _ => ((sourceQDataQCand T b).q)⁻¹)
      rw [sourceQTensorLanding, sourceQTensorLanding, h]
      have hfun : (fun _ : PUnit =>
          (sourceQDataQCand T b).q * ((sourceQDataQCand T b).q)⁻¹) =
          (fun _ : PUnit => (1 : CommonPrimeCompletion (sourceThetaPlace T b))) := by
        funext _
        exact mul_inv_cancel₀ (sourceQDataQCand T b).q_ne_zero
      calc
        (finitePadicTensorTprod (p := qVFamTensorP T b)
            (fun _ : PUnit => CommonPrimeCompletion (sourceThetaPlace T b))
            (fun _ => (sourceQDataQCand T b).q * ((sourceQDataQCand T b).q)⁻¹)) =
          (finitePadicTensorTprod (p := qVFamTensorP T b)
            (fun _ : PUnit => CommonPrimeCompletion (sourceThetaPlace T b))
            (fun _ => (1 : CommonPrimeCompletion (sourceThetaPlace T b)))) :=
            congrArg (fun f => finitePadicTensorTprod (p := qVFamTensorP T b)
              (fun _ : PUnit => CommonPrimeCompletion (sourceThetaPlace T b)) f) hfun
        _ = 1 := rfl)

theorem sourceQTensorLanding_q :
    sourceQTensorLanding T b (sourceQDataQCand T b).q =
      Units.val (sourceQTensorUnit T b) := by
  exact (Units.val_mkOfMulEqOne _).symm

noncomputable def sourcePilotRegionQDataActual :
    SourcePilotRegionQData T b :=
  sourcePilotRegionQData T b (sourceQTensorUnit T b)
    (sourceQTensorLanding T b) (sourceQTensorLanding_q T b)

#check sourceQTensorUnit
#check sourceQTensorLanding_q
#check sourcePilotRegionQDataActual
/-- The actual canonical unit reference on the source tensor block. -/
noncomputable abbrev sourceQTensorUnitReference : Set (SourceQTensorBlock T b) :=
  arithmeticTupleCanonicalUnitReference
    (fun _ (_ : Unit) => sourceThetaPlace T b) (fun _ => ())

/-- S195: the actual qUnit tensor lambda-O hull is the multiplication image of
the actual tensor unit on the canonical unit reference, not the image of an
arbitrary tensor-block element. -/
noncomputable def sourceQTensorLambdaOHull : Set (SourceQTensorBlock T b) :=
  {x | ∃ o ∈ sourceQTensorUnitReference T b,
    x = Units.val (sourceQTensorUnit T b) * o}

/-- The corrected hull is the image of the canonical unit reference under the
actual tensor unit, not the image of an arbitrary tensor-block element. -/
theorem sourceQTensorLambdaOHull_eq_image_unitReference :
    sourceQTensorLambdaOHull T b =
      (fun o : SourceQTensorBlock T b =>
        Units.val (sourceQTensorUnit T b) * o) ''
        sourceQTensorUnitReference T b := by
  ext x
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨o, ho, rfl⟩

/-- The corrected hull is exactly the unit-scaled canonical unit reference. -/
theorem sourceQTensorLambdaOHull_eq_scaled_unitReference :
    sourceQTensorLambdaOHull T b =
      {x | ∃ o ∈ sourceQTensorUnitReference T b,
        x = Units.val (sourceQTensorUnit T b) * o} :=
  rfl

theorem sourcePilotRegionQTensorLandingGap_nonempty :
    Nonempty (SourcePilotRegionQTensorLandingGap T b) := by
  exact ⟨⟨sourceQTensorLanding T b, sourceQTensorUnit T b, sourceQTensorLanding_q T b⟩⟩

#check sourceQTensorLambdaOHull
#check sourceQTensorLambdaOHull_eq_scaled_unitReference
#check sourcePilotRegionQTensorLandingGap_nonempty
end LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual

end