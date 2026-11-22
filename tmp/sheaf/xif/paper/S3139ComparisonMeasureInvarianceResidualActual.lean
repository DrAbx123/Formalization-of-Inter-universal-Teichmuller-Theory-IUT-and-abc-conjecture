import tmp.sheaf.xif.paper.S3139RouteComparisonInvarianceConsumerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3139: V2 comparison measure-invariance residual (abc/mainline naming bridge)

abc and mainline agree that the C3 comparison is a linear automorphism, so
volume/measure invariance across the comparison region is NOT automatic.  The
route residual is carried explicitly under two equivalent names:

* mainline: S3131RouteComparisonInvarianceHypothesis (W) (phi := C3 comparison)
  := forall S, W.logVolume (phi '' S) = W.logVolume S  (FT.route.comparison-invariance);
* abc: S3135ComparisonMeasureInvariance := Haar/log-volume of the C3 automorphism
  image of a measurable set equals the volume (paper III Prop 3.9(i)/Remark
  3.9.5(i) normalization input).

This file records the abstract measure-invariance hypothesis for a comparison map
on an arbitrary type (the V2 route shape), proves the region-volume bridge, and
records that it is an explicit residual -- not hidden in any region definition.

**Component, not paper object.**  Registry frozen except approved re-pins.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.S3139ComparisonMeasureInvarianceResidualActual

universe uX

/-- abc's named V2 residual: the Haar/log-volume of the comparison image of a
measurable set equals its volume (comparison-invariance of the measure readout
under the C3 convention automorphism). -/
def S3135ComparisonMeasureInvariance
    {X : Type uX} (mu : Set X → ℝ) (phi : X → X) : Prop :=
  ∀ S : Set X, mu (phi '' S) = mu S

/-- Mainline's named V2 residual shape is the same statement for the log-volume
readout (definitional bridge). -/
theorem S3135ComparisonMeasureInvariance.logVolume_form
    {X : Type uX} (mu : Set X → ℝ) (phi : X → X)
    (h : S3135ComparisonMeasureInvariance mu phi)
    (S : Set X) :
    mu (phi '' S) = mu S :=
  h S

/-- With the explicit measure-invariance residual, the comparison image of a
comparison region has the same volume (the V2 route's needed bridge). -/
theorem S3135ComparisonMeasureInvariance.region_volume
    {X : Type uX} (mu : Set X → ℝ) (phi : X → X)
    (h : S3135ComparisonMeasureInvariance mu phi)
    (region : Set X) :
    mu (phi '' region) = mu region :=
  h region

end LeanFormal.IUT.XiFPaper.S3139ComparisonMeasureInvarianceResidualActual

end
