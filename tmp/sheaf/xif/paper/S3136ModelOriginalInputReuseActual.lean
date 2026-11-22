import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual
import tmp.sheaf.xif.paper.S3136ModelThetaPacketActual

/-! # Stage-4 host: reuse of the prior-art OriginalInput/theater family for the model

PRIOR ART (§7.9): LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/
SourceUnitRegionHaarDataActual.lean proves the complete concrete theater family
(sourceHaarActualTheater:143, community laws, injectivity:288, Family:322) and, for
any SourceDefinition31Data S, the concrete OriginalInput sourceHaarActualOriginalInput:346
(with sourceHaarActual_primeStripAt:357).

CONSUMER: qpilot/hull model assembly. Our assembled SourceDefinition31Data
(S3136Source31RemainingSlotsActual.lgpSource31Data_full) can be fed directly into
the prior-art OriginalInput instead of introducing a parallel model-original-input
definition. This file exposes the reuse with the projection theorems.

LABEL: reuse adapter (no new construction). Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ModelOriginalInputReuseActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- The model original input: the prior-art concrete OriginalInput over any supplied
Definition 3.1 source datum. -/
def lgpModelOriginalInput (S : SourceDefinition31Data l) :
    OriginalInput.{0, 0, 0, 0, 0} l Unit :=
  sourceHaarActualOriginalInput (l := l) S

/-- Its initial source datum is the supplied S. -/
theorem lgpModelOriginalInput_initial (S : SourceDefinition31Data l) :
    (lgpModelOriginalInput S).initial = S := rfl

/-- Its prime strip at index (n,m) is the prior-art concrete prime strip. -/
theorem lgpModelOriginalInput_primeStripAt (S : SourceDefinition31Data l) (n m : Int) :
    (lgpModelOriginalInput S).primeStripAt n m =
      sourceHaarActualPrimeStrip n m :=
  sourceHaarActual_primeStripAt (l := l) S n m

#check lgpModelOriginalInput
#check lgpModelOriginalInput_initial
#check lgpModelOriginalInput_primeStripAt

end LeanFormal.IUT.XiFPaper.S3136ModelOriginalInputReuseActual
end