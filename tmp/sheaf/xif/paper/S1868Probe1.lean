import tmp.sheaf.xif.paper.S1854CoherentCategoryActual
import tmp.sheaf.xif.paper.S1816OrbicurveCoversToAffineActual
import tmp.sheaf.xif.paper.S1814OrbicurveCoversAffineActual
import tmp.sheaf.xif.paper.S1855RPrimeFiberIntegrationActual
import tmp.sheaf.xif.paper.S1753OrbicurveEtalePiAssemblyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

namespace ProbeS1868

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1799AffineFiniteEtaleEquivActual
open LeanFormal.IUT.XiFPaper.S1814OrbicurveCoversAffineActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1855RPrimeFiberIntegrationActual
open LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual

attribute [local instance] S1854CoherentCategory11

#check S1854Forget11
#check S1854QuotEquiv
#check S1854Forget11.map_id
#check S1854Forget11.map_comp
#check S1814AlgEquiv
#check S1814AlgEquiv.inverse
#check S1814AlgEquiv.inverse.obj
#check S1814AlgEquiv.inverse.map
#check coverToAlg
#check S1816Map
#check S1816Map_id_iff
#check S1816Map_comp
#check S1852FirstMissingOnCoherent
#check S1835Fiber
#check S1855FiberFunctor
#check S1753FiberFunctorTransport

end ProbeS1868
