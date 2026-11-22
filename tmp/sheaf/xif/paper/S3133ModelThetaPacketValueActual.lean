import tmp.sheaf.xif.paper.S3133ModelHodgeTheaterActual

/-!
# Model theta packet value: q = 1/5 (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: qpilot model assembly,
abc model theta-pilot/wrapper, lattice skeleton records.

Proves the concrete value facts of the model theta packet used by
modelHodgeTheater: its q is the actual Gaussian five theta value and equals
1/5, and the q-log is -log 5.  These feed the model q/descent and the
Cor 3.12 numeric route.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133ModelThetaPacketValueActual

local instance s3133ModelQFivePrimeFact : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual
open LeanFormal.IUT.XiFPaper.S3133ModelFPrimeStripActual
open LeanFormal.IUT.XiFPaper.S3133ModelHodgeTheaterActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual
open LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier

/-- The model theta packet's q is the actual Gaussian five theta value. -/
theorem modelThetaPacket_q (l : PrimeGeFive) (data : S3135ModelValueData) :
    (modelHodgeTheater l data).thetaPacket.q = gaussianFiveThetaQ := by
  rw [modelHodgeTheater_thetaPacket, lgpModelThetaPacket_q]

/-- The model theta packet's q is exactly 1/5. -/
theorem modelThetaPacket_q_eq_inv_five (l : PrimeGeFive)
    (data : S3135ModelValueData) :
    (modelHodgeTheater l data).thetaPacket.q = ((5 : Real)⁻¹) := by
  rw [modelThetaPacket_q, gaussianFiveThetaQ_eq_inv_five]

/-- The q-log of the model theta packet is -log 5. -/
theorem modelThetaPacket_log_q (l : PrimeGeFive) (data : S3135ModelValueData) :
    Real.log (modelHodgeTheater l data).thetaPacket.q = -Real.log 5 := by
  rw [modelThetaPacket_q_eq_inv_five, Real.log_inv]

end LeanFormal.IUT.XiFPaper.S3133ModelThetaPacketValueActual
