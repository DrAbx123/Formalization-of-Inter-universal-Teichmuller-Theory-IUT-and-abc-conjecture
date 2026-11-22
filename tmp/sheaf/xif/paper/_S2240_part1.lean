noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

namespace LeanFormal.IUT.XiFPaper.S2240StrictConeIsoActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2130ExplicitD6Actual
open LeanFormal.IUT.XiFPaper.S2185ConcreteTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1844PointSeparatedActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2028SourceSchemeActual
open LeanFormal.IUT.XiFPaper.S1911RepresentableTwoPullbackActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual

universe u

abbrev S2240Y (S : SchemeOverField S1726K) : EtaleStackPseudofunctor S1726K :=
  schemeRepresentableEtalePseudofunctor S1726K S