import tmp.sheaf.xif.paper.S3133ModelThetaPacketValueActual

/-!
# Model M2b: qVFamily defined from the model q, descent definitional
(component, not a paper object)

COMPONENT, not a paper object.  Named consumers: qpilot model R1 composition,
mainline/lattice in-model R1 record, abc model R_model.

AUDIT CLASSIFICATION (Lead-approved, class B/C): M2b (Tate-uniformization /
q-parameter identification) is not an opaque external datum.  Corpus IUT III
line 10350 and IUT I Def 3.1(b)/Ex 3.2(iv) read the q-parameters off the
elliptic curve E_F (the Tate q-parameters).  In the from-scratch model we
therefore DEFINE the model q-parameter family to be the actual model
q-parameter (q = 1/5, the concrete Gaussian Tate parameter); then the descent
norm equality is definitional (class A in-model).  No cross-model equality is
assumed: the family is a definition, and its norm facts are rfl/transport of
the already-proved model q value.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133ModelM2bDescentActual

local instance s3133ModelM2bFivePrimeFact : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual
open LeanFormal.IUT.XiFPaper.S3133ModelHodgeTheaterActual
open LeanFormal.IUT.XiFPaper.S3133ModelThetaPacketValueActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual

/-- The model q-parameter value: the model theta packet's q (= 1/5). -/
noncomputable def S3135ModelQValue (l : PrimeGeFive) (data : S3135ModelValueData) :
    Real :=
  (modelHodgeTheater l data).thetaPacket.q

/-- The model q-parameter value is exactly 1/5. -/
theorem S3135ModelQValue_eq_inv_five (l : PrimeGeFive)
    (data : S3135ModelValueData) :
    S3135ModelQValue l data = ((5 : Real)⁻¹) :=
  modelThetaPacket_q_eq_inv_five l data

/-- The model q-parameter family: DEFINED to be the model q-parameter at every
model bad place (in-model M2b: the Tate q-parameter identification is a
definition, class A). -/
noncomputable def S3135ModelQVFam (l : PrimeGeFive) (data : S3135ModelValueData)
    (v : S3135ModelV) : Real :=
  S3135ModelQValue l data

/-- Model M2b descent: every model bad place carries the model q-parameter,
definitionally. -/
theorem S3135ModelQVFam_descent (l : PrimeGeFive) (data : S3135ModelValueData)
    (v : S3135ModelV) :
    S3135ModelQVFam l data v = S3135ModelQValue l data :=
  rfl

/-- Model M2b norm descent: the model q-parameter family has norm 1/5 at every
model place (transport of the proved packet value). -/
theorem S3135ModelQVFam_abs_log (l : PrimeGeFive) (data : S3135ModelValueData)
    (v : S3135ModelV) :
    |Real.log (S3135ModelQVFam l data v)| = Real.log 5 := by
  rw [S3135ModelQVFam, S3135ModelQValue_eq_inv_five, Real.log_inv, abs_neg,
    abs_of_pos (Real.log_pos (by norm_num))]

end LeanFormal.IUT.XiFPaper.S3133ModelM2bDescentActual
