import tmp.sheaf.xif.paper.Mzk1CorrectedRegionLogLawConditionalShaActual
import tmp.sheaf.xif.paper.Mzk1B1B2GenericLemmasShaActual

/-! # corrected_gap1_unconditional assembly (data-level) -/

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalShaActual

open LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionLogLawConditionalShaActual

/-- Data package for the corrected Gap1 assembly: corrected log law + arithmetic
bound + positivity. -/
structure CorrectedGap1Data where
  logLaw : CorrectedRegionLogLaw
  c : Real
  epsilon : Real
  epsilon_pos : 0 < epsilon
  arithmetic_bound :
    Real.log c ≤
      (1 + epsilon) * (logLaw.unitLog + Real.log logLaw.ratio + logLaw.const)

/-- Assembly: the data package gives the corrected Gap1 pointwise inequality. -/
theorem corrected_gap1_unconditional (D : CorrectedGap1Data) :
    Real.log D.c ≤ (1 + D.epsilon) * D.logLaw.regionLog :=
  corrected_gap1_conditional D.logLaw D.c D.epsilon D.epsilon_pos D.arithmetic_bound

#print axioms corrected_gap1_unconditional

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedGap1UnconditionalShaActual
