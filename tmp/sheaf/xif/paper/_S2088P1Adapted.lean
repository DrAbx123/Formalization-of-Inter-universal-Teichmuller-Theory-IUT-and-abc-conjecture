import tmp.sheaf.xif.paper.S2070CurveEtaleFundamentalCardActual
import tmp.sheaf.xif.paper.S2081CurveCardM2Actual

noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S2070CurveEtaleFundamentalCardActual
open LeanFormal.IUT.Foundations.Geometry
universe u

#check @ObjectProperty.lift
#check @ObjectProperty.liftCompιIso
#check @ObjectProperty.ι
#check @CategoryTheory.Limits.PreservesLimit
#check @CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone
#check @CategoryTheory.Limits.preservesLimit_iff_isLimit_mapCone
#check @CategoryTheory.Limits.preservesLimitsOfShape_pempty_of_preservesTerminal
#check @CategoryTheory.Limits.isLimitMapConeEmptyConeEquiv
#check @CategoryTheory.Limits.diagramIsoCospan
#check @CategoryTheory.Limits.PullbackCone.isLimitAux'
#check @CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone
#check @CategoryTheory.Limits.PreservesFiniteCoproducts.of_preserves_binary_and_initial
#check @CategoryTheory.Limits.preservesLimit_of_iso_diagram
#check @CategoryTheory.Limits.preservesColimit_of_iso_diagram
#check @CategoryTheory.Limits.fullyFaithful_reflectsLimits
#check @CategoryTheory.Limits.fullyFaithful_reflectsColimits
#check @CategoryTheory.Functor.ReflectsEpimorphisms
#check @CategoryTheory.Functor.PreservesEpimorphisms
#check @CategoryTheory.Functor.ReflectsIsomorphisms
#check @CategoryTheory.Functor.FullyFaithful.reflectsEpimorphisms
#check @CategoryTheory.Functor.FullyFaithful.reflectsIsomorphisms
#check @CategoryTheory.Limits.IsTerminal
#print CategoryTheory.Limits.IsTerminal
#print CategoryTheory.Functor.ReflectsEpimorphisms

end
