import tmp.sheaf.xif.paper.S3127G2AffineLiftExistsUniqueActual
import tmp.sheaf.xif.paper.S3127G2CoverIsoActual
import tmp.sheaf.xif.paper.S3127G2TargetActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientG2
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
namespace LeanFormal.IUT.XiFPaper.RawFacBaseProbe
#check AffineQuotientG2.baseSpec (R := S1348CoordinateRing l)
#check S1419AffineScheme l
example : AffineQuotientG2.baseSpec (R := S1348CoordinateRing l) = S1419AffineScheme l := rfl
end LeanFormal.IUT.XiFPaper.RawFacBaseProbe
end
