import tmp.sheaf.xif.paper.Mzk1PaperQPilotLineBundleSourceActual
import tmp.sheaf.xif.paper.Mzk1Ob33DetLineActual
import Mathlib.Tactic

/-! # CONDITIONAL: Ob33 determinant line from the actual bad-prime source

The source is actual (bad-prime ideal product).  The determinant line/map/data
and arithmetic degree are obtained from Mzk1Ob33DetLineActual.
The remaining semantic identification
  qPilotDetArithmeticDegree = routeBThetaNormalized
is kept as an explicit Prop; the RouteB gap becomes exactly that Prop.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotLineBundleSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual q-pilot line-bundle source from the bad-prime ideal product. -/
noncomputable abbrev badPrimeSource : PaperQPilotLineBundleSource (A := T.arithmetic) :=
  qPilotLineBundleSourceOfBadPrimes T

/-- Actual determinant line of the bad-prime q-pilot source. -/
noncomputable def qPilotDetLineOfBadPrimes :
    SourceLineBundle (A := T.arithmetic) :=
  Mzk1Ob33DetLineActual.qPilotDetLine T.arithmetic (badPrimeSource T)

/-- Actual determinant data of the bad-prime q-pilot source. -/
noncomputable def qPilotDetDataOfBadPrimes :
    LeanFormal.IUT.PaperDeterminantLogVolume.PaperDeterminantLogVolumeData
      (k := T.arithmetic.K) :=
  Mzk1Ob33DetLineActual.qPilotDetData T.arithmetic (badPrimeSource T)

/-- Actual arithmetic degree of the bad-prime q-pilot source. -/
noncomputable def qPilotDetArithmeticDegreeOfBadPrimes : Real :=
  Mzk1Ob33DetLineActual.qPilotDetArithmeticDegree T.arithmetic (badPrimeSource T)

/-- Semantic identification of the arithmetic degree with the S3137 normalized
Theta reading.  This is the remaining paper-semantic Prop, not assumed. -/
def BadPrimeSourceReadingIdentification
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  qPilotDetArithmeticDegreeOfBadPrimes T = Mzk1Ob33DetLineActual.routeBThetaNormalized C3

/-- The Route B arithmetic-degree reading gap for the actual source is exactly
the above semantic identification Prop. -/
theorem routeB_gap_iff_badPrimeSource_identification
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    Mzk1Ob33DetLineActual.RouteBArithmeticDegreeReadingGap T.arithmetic
        (badPrimeSource T) C3 <->
      BadPrimeSourceReadingIdentification T C3 :=
  Iff.rfl

/-- Conditional Route B closure from the explicit semantic identification. -/
theorem routeB_gap_closed_of_identification
    {V : Type} {I : OriginalInput l V}
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : BadPrimeSourceReadingIdentification T C3) :
    Mzk1Ob33DetLineActual.RouteBArithmeticDegreeReadingGap T.arithmetic
      (badPrimeSource T) C3 :=
  (routeB_gap_iff_badPrimeSource_identification T C3).mpr h

#check badPrimeSource
#check qPilotDetLineOfBadPrimes
#check qPilotDetDataOfBadPrimes
#check qPilotDetArithmeticDegreeOfBadPrimes
#check BadPrimeSourceReadingIdentification
#check routeB_gap_iff_badPrimeSource_identification
#check routeB_gap_closed_of_identification
end LeanFormal.IUT.XiFPaper.Mzk1Ob33DetLineFromBadPrimeSourceActual
end
