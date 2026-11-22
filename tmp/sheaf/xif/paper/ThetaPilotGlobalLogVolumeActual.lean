import tmp.sheaf.xif.paper.GlobalThetaPilotPossibleImageGeometryActual
import tmp.sheaf.xif.paper.GlobalQPilotProcessionLogVolumeActual

/-!
# Theta-pilot global scalar for xi-f

The final xi-f comparison only needs two actual scalars:

* thetaPilotProductProcessionLogVolume: the actual canonical-procession
  normalized sum of the component-indexed Theta-pilot log-volumes

    - log (globalThetaPilotThetaValue T b j)

  over the actual bad places b and signed labels j;

* qPilotGlobalScalar: the actual q-pilot procession magnitude
  qPilotProcessionLogMagnitude T.

This file keeps only those scalars, their defining equalities, and the exact
scalar comparison target.  It does not construct the qside global product
object/divisor bridge, since that bridge is not consumed by the final scalar
inequality.

No diagonal/constant tuple, PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.ThetaPilotGlobalLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotPossibleImageGeometryActual
open LeanFormal.IUT.XiFPaper.GlobalQPilotProcessionLogVolumeActual
open LeanFormal.IUT.XiFPaperThetaHull

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual label-wise Theta-pilot log-volume from the component-indexed theta
values. -/
noncomputable def thetaPilotLabelLogVolume
    (j : SignedLabel l.value) : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    - Real.log (globalThetaPilotThetaValue T b j)

/-- The label-wise value is the actual component sum. -/
theorem thetaPilotLabelLogVolume_eq (j : SignedLabel l.value) :
    thetaPilotLabelLogVolume T j =
      ∑ b : Bad (nativePlaceSelection T),
        - Real.log (globalThetaPilotThetaValue T b j) := rfl

/-- Actual canonical-procession normalized Theta-pilot log-volume. -/
noncomputable def thetaPilotProductProcessionLogVolume : Real :=
  (canonicalProcession (l := l)).average
    (fun j : SignedLabel l.value => thetaPilotLabelLogVolume T j)

/-- The Theta-pilot product procession scalar is the actual weighted average. -/
theorem thetaPilotProductProcessionLogVolume_eq :
    thetaPilotProductProcessionLogVolume T =
      (canonicalProcession (l := l)).average
        (fun j : SignedLabel l.value => thetaPilotLabelLogVolume T j) := rfl

/-- Actual signed Theta-pilot scalar. -/
noncomputable def thetaPilotSignedProcessionLogVolume : Real :=
  - thetaPilotProductProcessionLogVolume T

/-- The actual q-pilot procession magnitude scalar. -/
noncomputable def qPilotGlobalScalar : Real :=
  qPilotProcessionLogMagnitude T

/-- The q-pilot scalar is the actual q-pilot procession magnitude. -/
theorem qPilotGlobalScalar_eq :
    qPilotGlobalScalar T = qPilotProcessionLogMagnitude T := rfl

/-- Exact scalar comparison target: Theta-pilot procession volume at most the
q-pilot procession magnitude. -/
def thetaPilotProductVsQPilotComparison : Prop :=
  thetaPilotProductProcessionLogVolume T <= qPilotGlobalScalar T

/-- The scalar target unfolds to the two actual scalars. -/
theorem thetaPilotProductVsQPilotComparison_iff :
    thetaPilotProductVsQPilotComparison T ↔
      thetaPilotProductProcessionLogVolume T <= qPilotProcessionLogMagnitude T :=
  Iff.rfl

/-- Actual scalar data for xi-f. -/
structure ThetaPilotGlobalLogVolumeData where
  thetaPilotScalar : Real
  thetaPilotScalar_eq : thetaPilotScalar =
    thetaPilotProductProcessionLogVolume T
  qPilotScalar : Real
  qPilotScalar_eq : qPilotScalar = qPilotGlobalScalar T
  scalarComparison : thetaPilotScalar <= qPilotScalar

/-- The actual theta-pilot scalar. -/
noncomputable def thetaPilotGlobalScalar : Real :=
  thetaPilotProductProcessionLogVolume T

/-- The scalar comparison proposition H <= Q. -/
def thetaPilotGlobalScalarComparison : Prop :=
  thetaPilotGlobalScalar T <= qPilotGlobalScalar T

/-- H <= Q is exactly the product procession comparison target. -/
theorem thetaPilotGlobalScalarComparison_iff :
    thetaPilotGlobalScalarComparison T ↔
      thetaPilotProductVsQPilotComparison T :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.ThetaPilotGlobalLogVolumeActual

end
