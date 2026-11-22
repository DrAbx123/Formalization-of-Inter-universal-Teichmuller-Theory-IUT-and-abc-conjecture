import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
import tmp.sheaf.xif.paper.S1633SignQuotientBasicActual
import tmp.sheaf.xif.paper.S2878GroupsInputActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1633SignQuotientBasicActual
open LeanFormal.IUT.XiFPaper.S2878GroupsInputActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open CategoryTheory AlgebraicGeometry
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3119GeometricCorePrefixAttempt

variable {l : PrimeGeFive}

local instance s3119Category : Category (Iut.SchemeOverField (S1348K l)) := inferInstance
local instance s3119Quiver : Quiver (Iut.SchemeOverField (S1348K l)) := instCategoryOver.toQuiver

/-- The two actual prefix fields xF and xF_geometry. -/
structure S3119XFData where
  xF : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F
  xF_geometry : SourceOncePuncturedGeometry (S1280Arithmetic l).curve xF

/-- Actual prefix from S1536. -/
noncomputable def S3119XFDataActual : S3119XFData (l := l) where
  xF := S1536XF
  xF_geometry := S1536XFGeometry


/-- Conditional stack lift: any Over automorphism of the representing S1419
scheme induces an endomorphism of the orbicurve stack via S1742. -/
noncomputable def S3119StackLift
    (α : S1419AffineOver (l := l) ⟶ S1419AffineOver (l := l)) :
    (S1536XF (l := l)).Hom (S1536XF (l := l)) :=
  S1742StrongTransOfHom (F := S1348K l) α

/-- Minimal xF group input target. -/
abbrev S3119GroupsInputTarget : Type 1 :=
  GroupsInput (S1536XF (l := l))
    (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).F)


/-- First missing field: geometric stack lift of the curve involution. -/
abbrev S3119MissingGeometricInvolution : Type 1 :=
  (S1536XF (l := l)).Hom (S1536XF (l := l))

/-- xFGroups target: actual orbicurve fundamental-group data. -/
abbrev S3119XFGroupsTarget : Type 1 :=
  SourceOrbicurveGroupData (S1536XF (l := l))
    (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).F)

#check S3119StackLift
#check S3119GroupsInputTarget
#check S3119XFData
#check S3119XFDataActual
#check S3119MissingGeometricInvolution
#check S3119XFGroupsTarget
#check S1633MissingGeometricInvolution
#check GroupsInput.toSourceOrbicurveGroupData

end LeanFormal.IUT.XiFPaper.S3119GeometricCorePrefixAttempt
end