import tmp.sheaf.xif.paper.S1063PerBQPilotPaperNonzeroActual
import tmp.sheaf.xif.paper.S1064GlobalQpilotClassicalThetaNonzeroActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1063PerBQPilotPaperNonzeroActual
open LeanFormal.IUT.XiFPaper.S1064GlobalQpilotClassicalThetaNonzeroActual

namespace LeanFormal.IUT.XiFPaper.Node09P5GlobalInequalityActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual global P5 per-b inequality, from the S1063 actual region inclusion,
actual qPilot positivity, and actual nonzero-hull finiteness. -/
theorem p5_s1064PerBInequality_actual :
    S1064PerBInequality (l := l) T :=
  fun b => S1063PerBQPilotPaperNonzeroActual.s1063PerBInequality (l := l) T b

/-- Actual weighted global P5 inequality: classical qPilot (weighted per-b
qPilot logs) is at most the global nonzero theta-hull log. -/
theorem p5_global_qPilot_le_thetaHullNonzero :
    S1064GlobalQpilotClassicalThetaNonzeroActual.qPilotClassicalLogGlobal (l := l) T ≤
      S1064GlobalQpilotClassicalThetaNonzeroActual.thetaHullNonzeroGlobal (l := l) T :=
  S1064GlobalQpilotClassicalThetaNonzeroActual.qPilotClassicalLogGlobal_le_thetaHullNonzeroGlobal_of_perB
    (l := l) T (p5_s1064PerBInequality_actual (l := l) T)

#print axioms p5_s1064PerBInequality_actual
#print axioms p5_global_qPilot_le_thetaHullNonzero

end LeanFormal.IUT.XiFPaper.Node09P5GlobalInequalityActual
end