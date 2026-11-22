import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S3119XCoordinateFixingTargets
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119XCoordinateFixingTargets
namespace LeanFormal.IUT.XiFPaper.S3119PunctureAuditActual
variable {l : PrimeGeFive}

-- The actual xF_geometry object: it contains only the once-punctured signature,
-- with no puncture/compactification data.
#check SourceOncePuncturedGeometry
#check SourceOncePuncturedGeometry.signature_spec
#check SourceOncePuncturedGeometry.signature_eq_oncePuncturedElliptic
#check S1536XFGeometry
#check S1536XF

-- The nearest actual puncture data: punctured projective K-points, excluding
-- the projective zero (the point at infinity).
#check S1348EvalPoint
#check S1348EvalPunctured
#check S1348EvalPoint_ne_zero
#check S1348PointAlgHom_surjective
#check S1348Curve_isElliptic

/-- Minimal infinity-filtration target: every K-algebra automorphism sends x
into the degree-two filtered part.  This is the missing step; no actual is
currently supplied by the puncture/compactification data. -/
def S3119InfinityFiltrationTarget : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[S1348K l] S1348CoordinateRing l,
    φ (S3119x0 (l := l)) ∈ S3119filtR (l := l) 2

#check S3119XImageInFiltRTwoTarget
#check S3119InfinityFiltrationTarget
end LeanFormal.IUT.XiFPaper.S3119PunctureAuditActual
end
