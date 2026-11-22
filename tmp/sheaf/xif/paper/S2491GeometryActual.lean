import tmp.sheaf.xif.paper.S2482QiOrbicurveActual
import tmp.sheaf.xif.paper.S2482QiCurveActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
namespace LeanFormal.IUT.XiFPaper.S2491GeometryActual

#check S2482OncePuncturedGeometry
#check S2482PuncturedCurve
#check S2482Orbicurve
#check SourceOncePuncturedGeometry

theorem S2491Geometry : SourceOncePuncturedGeometry S2482PuncturedCurve S2482Orbicurve :=
  S2482OncePuncturedGeometry

end LeanFormal.IUT.XiFPaper.S2491GeometryActual
end