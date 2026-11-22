import tmp.sheaf.xif.paper.ConcreteQMagnitudeSourceComparisonActual
import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual

-- SignedThetaAverageLeQMagnitude is incompatible with the actual q=1/5
-- arithmetic obstacle. This is an exact obstruction, not a fake proof.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.SignedThetaAverageObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteQMagnitudeSourceComparisonActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open scoped BigOperators

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (D : SourcePilotRegionDonors (l := l) (V := V) I)

-- The signed-average/q-magnitude bound is exactly the concrete Gaussian
-- q-magnitude bound, because the signed C3 and the Gaussian C3 are the same
-- source-theater C3.
theorem signedThetaAverageLeQMagnitude_iff_concreteQMagnitudeBound :
    SignedThetaAverageLeQMagnitude (l := l) (V := V) (I := I) D ↔
      ConcreteQMagnitudeBound (l := l) (V := V) (I := I) D := by
  unfold SignedThetaAverageLeQMagnitude ConcreteQMagnitudeBound
    concreteSignedAverage concreteGaussianC3
  rfl

-- Exact arithmetic obstruction: the signed average bound is false whenever
-- the actual q-magnitude is log 5 and the Gauss sum exceeds the label cardinality.
theorem not_signedThetaAverageLeQMagnitude_of_obstacle
    (h : ConcreteQMagnitudeObstacle (l := l) (V := V) (I := I) D) :
    ¬ SignedThetaAverageLeQMagnitude (l := l) (V := V) (I := I) D := by
  intro hbound
  exact (not_concreteQMagnitudeBound_of_obstacle
    (l := l) (V := V) (I := I) D h)
    ((signedThetaAverageLeQMagnitude_iff_concreteQMagnitudeBound
      (l := l) (V := V) (I := I) D).mp hbound)

#check signedThetaAverageLeQMagnitude_iff_concreteQMagnitudeBound
#check not_signedThetaAverageLeQMagnitude_of_obstacle

end LeanFormal.IUT.XiFPaper.SignedThetaAverageObstructionActual

end