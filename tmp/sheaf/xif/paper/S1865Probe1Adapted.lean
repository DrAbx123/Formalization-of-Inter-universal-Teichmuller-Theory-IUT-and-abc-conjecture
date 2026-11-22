import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1761DMStackSmallnessActual
import tmp.sheaf.xif.paper.S1743CoverSliceActual
import tmp.sheaf.xif.paper.S1756CoverSourceRepresentabilityActual
import tmp.sheaf.xif.paper.S1816OrbicurveCoversToAffineActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1865CoprodApexActual

open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1761DMStackSmallnessActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1827CloseRetractionActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual

/-- The empty object of the etale site: the empty scheme over Spec F'. -/
noncomputable abbrev S1865EmptyOver : SchemeOverField S1726K :=
  Over.mk (Scheme.emptyTo S1726Base.left)

/-- The empty etale stack: the representable stack of the empty scheme. -/
noncomputable def S1865EmptyStack : EtaleStackOverField S1726K where
  fiber := schemeRepresentableEtalePseudofunctor S1726K S1865EmptyOver
  isStack := S1761RepresentableIsStack S1865EmptyOver
  orbicurveSignature := none

/-- The canonical map from the empty site object to the affine base. -/
noncomputable def S1865EmptyToBase : S1865EmptyOver ⟶ S1726AffineOver :=
  Over.homMk (Scheme.emptyTo S1726AffineOver.left) (Subsingleton.elim _ _)

/-- The structure map of the empty cover: the unique (up to 2-iso) map from the
empty stack to the orbicurve. -/
noncomputable def S1865EmptyMap :
    Pseudofunctor.StrongTrans S1865EmptyStack.fiber S1726Orbicurve.stack.fiber :=
  S1742StrongTransOfHom (F := S1726K) S1865EmptyToBase

#check S1865EmptyMap
#check S1742StrongTransOfHom
#check S1743SchemeRepresentableMap

end LeanFormal.IUT.XiFPaper.S1865CoprodApexActual
