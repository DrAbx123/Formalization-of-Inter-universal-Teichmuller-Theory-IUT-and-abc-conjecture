import tmp.sheaf.xif.paper.CuspRealizationActual
import tmp.sheaf.xif.paper.NativeCuspRealActual
import Iut.Foundations.Orbicurve

/-!
# Search for an actual real cusp coordinate map

Search result across the project Lean tree:

* OrbicurveBoundaryCusp is a geometric compactification-boundary structure
  (Iut.Foundations.Orbicurve): compactification, open map, residue scheme and a
  boundary point. It has no Real coordinate field.
* No declaration of type OrbicurveBoundaryCusp X -> Real exists in the tree.
* No declaration supplying a real cuspScale attached to a boundary cusp exists.
* The only cuspScale occurrences are fields of the source clause record
  SourceCuspClause and dependent source structures, not functions of a
  geometric boundary cusp.
* No archimedean cusp realization map exists.

Exact missing object: CuspCoordinateMap X with epsilonOf and cuspScaleOf
functions from OrbicurveBoundaryCusp X to Real, positivity, compatibility and
native realization proofs. This file records the search status and gives the
conditional construction from that exact map. No arbitrary map or real is
fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.CuspCoordinateSearchActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual
open LeanFormal.IUT.XiFPaper.NativeD7CuspActual
open LeanFormal.IUT.XiFPaper.NativeCuspRealActual
open LeanFormal.IUT.XiFPaper.CuspRealizationActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- The actual geometric cusp on which a real coordinate map would have to be
defined. -/
abbrev searchCusp : Iut.OrbicurveBoundaryCusp
    (nativeCompletion T).sourceSignQuotientData.cK :=
  nativeCuspObject T

/-- Exact missing search object: a real coordinate map on the actual geometric
cusp, with cusp scale and realization data. -/
def MissingCuspCoordinateSearch : Prop :=
  Nonempty (CuspCoordinateMap
    (nativeCompletion T).sourceSignQuotientData.cK)

/-- Conditional CuspRealizationData from the exact missing coordinate map. -/
noncomputable def cuspRealizationOfSearchMap
    (M : CuspCoordinateMap
      (nativeCompletion T).sourceSignQuotientData.cK) :
    CuspRealizationData (l := l) T :=
  cuspRealizationDataOfCoordinateMap T M (searchCusp T)

/-- Conditional cusp hypotheses from the exact missing coordinate map. -/
theorem nativeCuspHypotheses_of_searchMap
    (M : CuspCoordinateMap
      (nativeCompletion T).sourceSignQuotientData.cK) :
    Nonempty NativeCuspClauseHypotheses :=
  nativeCuspHypotheses_of_coordinateMap T M

/-- The actual search object is the geometric boundary cusp, not a Real. -/
theorem searchCusp_type :
    Iut.OrbicurveBoundaryCusp
      (nativeCompletion T).sourceSignQuotientData.cK :=
  searchCusp T

/-- Search status: the real cusp coordinate map is exactly the missing object;
the geometric cusp itself is actual. -/
def CuspCoordinateSearchStatus : Prop :=
  MissingCuspCoordinateSearch (l := l) T

end LeanFormal.IUT.XiFPaper.CuspCoordinateSearchActual

end
