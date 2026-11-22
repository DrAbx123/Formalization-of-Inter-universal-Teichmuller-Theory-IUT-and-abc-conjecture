import tmp.sheaf.xif.paper.S1348D6OrbicurveActual

noncomputable section
open CategoryTheory
open AlgebraicGeometry
open scoped SpecOfNotation
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual

namespace S1419Probe14Adapted

variable (l : PrimeGeFive)

example : (S1348Curve l).toAffine.Equation 1 2 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [S1348Curve, S1348K]
  trace_state
  sorry

end S1419Probe14Adapted

end
