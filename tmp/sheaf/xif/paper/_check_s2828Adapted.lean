import tmp.sheaf.xif.paper.S2822PointRealizationRouteActual
open AlgebraicGeometry CategoryTheory
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
namespace Test
variable (K : Type) [Field K] (e : E37ChartZOverlap K ≅ E37ChartYOverlap K)
example : Subsingleton (Spec (CommRingCat.of K)) := inferInstance
example : IsOpenImmersion (E37ProjChartZMap K e) := (E37ProjGlueData K e).ι_isOpenImmersion (ULift.up false)
example : IsOpenImmersion (E37ProjChartYMap K e) := (E37ProjGlueData K e).ι_isOpenImmersion (ULift.up true)
end Test