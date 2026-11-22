import tmp.sheaf.xif.paper.S1555EllipticInvolutionActual
import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
/-! # S1556: stack lift of the curve [-1] involution
The actual curve-point involution S1555CurveInvolution is not an endomorphism
of the S1419 orbicurve.  Its stack lift would be a StrongTrans /
SchemeRepresentableMap of the representing affine stack, not a point map.
The identity Hom is actual; the exact first missing object is a nontrivial
endomorphism (and its TwoIso square/uniqueness).  No fake Hom is constructed. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1556OrbicurveInvolutionActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1555EllipticInvolutionActual
variable {l : PrimeGeFive}
/-- Identity endomorphism of the S1419 orbicurve (actual, not the involution). -/
noncomputable def S1556IdentityHom :
    (S1536XF (l := l)).Hom (S1536XF (l := l)) :=
  Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l))
/-- Exact first missing stack lift: a nontrivial endomorphism of xF. -/
abbrev S1556FirstMissingStackLift : Type 1 :=
  { f : (S1536XF (l := l)).Hom (S1536XF (l := l)) //
      f ≠ S1556IdentityHom (l := l) }
-- A full lift also needs TwoIso(comp f f, id), uniqueness, and the
-- OrbicurveSignAction derived from it.  The curve-point involution alone does
-- not provide a Pseudofunctor.StrongTrans/SchemeRepresentableMap of the
-- representing affine stack; that is the exact obstruction.
#check S1555CurveInvolution
#check Iut.HyperbolicOrbicurve.Hom.id
end LeanFormal.IUT.XiFPaper.S1556OrbicurveInvolutionActual
