import tmp.sheaf.xif.paper.S3133ModelFPrimeStripActual
import tmp.sheaf.xif.paper.S3136ModelThetaPacketActual
import tmp.sheaf.xif.paper.S3133S3131GaussianModelComponentsActual

/-!
# Model HodgeTheater for the from-scratch model (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: qpilot model assembly
(modelOriginalInput), lattice theater-family skeleton, abc R_model.

Fills the model HodgeTheater slots: arithmetic :=
concreteGaussianInitialThetaArithmeticData l (the concrete Example 3.6/Gaussian
arithmetic), primeStrip := modelFPrimeStrip data (abc value package), and
thetaPacket := stage4's concrete model theta packet (q = 1/5, actual Gaussian
packet).  All slots are actual inhabitants; no placeholders.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133ModelHodgeTheaterActual

local instance s3133ModelGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3133ModelVBasisActual
open LeanFormal.IUT.XiFPaper.S3133ModelFPrimeStripActual
open LeanFormal.IUT.XiFPaper.S3135ModelValueDataActual
open LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual

/-- The model Hodge theater: concrete Gaussian arithmetic, the model prime strip,
and the concrete model theta packet (q = 1/5). -/
noncomputable def modelHodgeTheater (l : PrimeGeFive)
    (data : S3135ModelValueData) :
    HodgeTheater l S3135ModelV where
  arithmetic := concreteGaussianInitialThetaArithmeticData l
  primeStrip := modelFPrimeStrip data
  thetaPacket := lgpModelThetaPacket l

/-- The model Hodge theater's arithmetic is the concrete Gaussian arithmetic. -/
theorem modelHodgeTheater_arithmetic (l : PrimeGeFive)
    (data : S3135ModelValueData) :
    (modelHodgeTheater l data).arithmetic =
      concreteGaussianInitialThetaArithmeticData l :=
  rfl

/-- The model Hodge theater's theta packet is the concrete Gaussian packet. -/
theorem modelHodgeTheater_thetaPacket (l : PrimeGeFive)
    (data : S3135ModelValueData) :
    (modelHodgeTheater l data).thetaPacket = lgpModelThetaPacket l :=
  rfl

end LeanFormal.IUT.XiFPaper.S3133ModelHodgeTheaterActual
