import tmp.sheaf.xif.paper.CuspCoordinateSearchActualAdapted
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31RootLemmas

/-!
# Search for an actual SourceCuspClause usable for CuspCoordinateMap

Search result:

* SourceCuspClause is a real-valued record (epsilon, cuspScale, positivity and
  compatibility fields).
* No actual inhabitant of SourceCuspClause is constructed in the tree. D8 cusp
  construction is the conditional proposition
    D8CuspConstruction l = forall A, Nonempty SourceCuspClause,
  not a theorem.
* SourceDefinition31Data carries a cusp : SourceCuspClause field, but no actual
  SourceDefinition31Data is constructed unconditionally.
* Even a SourceCuspClause would give real epsilon/cuspScale values, not a
  function OrbicurveBoundaryCusp X -> Real with a geometric realization.

Exact missing object: an actual SourceCuspClause together with a geometric
coordinate realization on the native boundary cusp. Conditionally, the source
clause fields plus a CuspCoordinateMap build the cusp realization. No real
coordinate, map, source clause, compatibility proof, toy data, forbidden
placeholder, or unfilled proof is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.CuspFromSourceClauseActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual
open LeanFormal.IUT.XiFPaper.NativeD7CuspActual
open LeanFormal.IUT.XiFPaper.NativeCuspRealActual
open LeanFormal.IUT.XiFPaper.CuspRealizationActual
open LeanFormal.IUT.XiFPaper.CuspCoordinateSearchActualAdapted
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- The exact missing source cusp clause. -/
def MissingSourceCuspClause : Prop :=
  Nonempty Theorem311Source.SourceCuspClause

/-- Conditional source cusp realization: an actual SourceCuspClause plus a real
coordinate map on the geometric native cusp. -/
structure SourceCuspRealization
    (C : Theorem311Source.SourceCuspClause) : Prop where
  coordinateMap : CuspCoordinateMap
    (nativeCompletion T).sourceSignQuotientData.cK
  epsilon_agrees : forall cusp,
    coordinateMap.epsilonOf cusp = C.epsilon
  cuspScale_agrees : forall cusp,
    coordinateMap.cuspScaleOf cusp = C.cuspScale

/-- Exact missing object for constructing CuspCoordinateMap from source clauses:
a source cusp clause plus its geometric coordinate realization. -/
structure MissingSourceCuspCoordinate : Prop where
  clause : Theorem311Source.SourceCuspClause
  realization : SourceCuspRealization (l := l) T clause

/-- Conditional CuspCoordinateMap from an actual source clause and its exact
geometric realization. -/
noncomputable def cuspCoordinateMapOfSourceClause
    (M : MissingSourceCuspCoordinate (l := l) T) :
    CuspCoordinateMap (nativeCompletion T).sourceSignQuotientData.cK :=
  M.realization.coordinateMap

/-- The source cusp clause data alone does not supply a geometric map; the exact
missing object includes the realization. -/
def MissingSourceCuspCoordinateObject : Prop :=
  Nonempty (MissingSourceCuspCoordinate (l := l) T)

/-- The actual geometric cusp is available as the realization target. -/
theorem nativeCusp_target :
    Iut.OrbicurveBoundaryCusp
      (nativeCompletion T).sourceSignQuotientData.cK :=
  searchCusp T

/-- Conditional CuspRealizationData from the exact source clause realization. -/
theorem cuspRealizationData_of_sourceClause
    (M : MissingSourceCuspCoordinate (l := l) T) :
    Nonempty (CuspRealizationData (l := l) T) :=
  ⟨cuspRealizationDataOfCoordinateMap T
    (cuspCoordinateMapOfSourceClause T M) (nativeCuspObject T)⟩

end LeanFormal.IUT.XiFPaper.CuspFromSourceClauseActualAdapted

end
