import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1370SourceSignQuotientFix
import tmp.sheaf.xif.paper.S1360D9OrbicurveSlotActual
/-! # S1536: S1419 orbicurve as the xF prefix of the sign quotient
S1419Orbicurve is an actual Iut.HyperbolicOrbicurve over S1348K = (S1280Arithmetic l).F
with once-punctured-elliptic signature.  It therefore fills the xF and
xF_geometry fields of SourceSignQuotientGeometricCore/Data.  It supplies no
elliptic involution, sign action, quotient, group data, or K-side orbicurve, so
it cannot fill the full SQ; the exact first missing field is ellipticInvolution.
No fake X/SQ is asserted. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1370SourceSignQuotientFix
variable {l : PrimeGeFive}
/-- S1419's actual orbicurve, typed at the paper base field F. -/
noncomputable def S1536XF : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F :=
  S1419Orbicurve l
theorem S1536XF_signature :
    (S1536XF (l := l)).signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic :=
  S1419Orbicurve_signature l
/-- The xF_geometry field of the geometric core, filled by S1419's signature. -/
theorem S1536XFGeometry :
    SourceOncePuncturedGeometry (S1280Arithmetic l).curve
      (S1536XF (l := l)) where
  signature := by
    rw [S1536XF_signature, s1370_sourceTypeOneOne_eq_oncePunctured]
/-- The exact first field of SourceSignQuotientGeometricCore/Data not supplied
by S1419: an elliptic involution of xF. -/
abbrev S1536FirstMissingField : Type 1 :=
  (S1536XF (l := l)).Hom (S1536XF (l := l))
-- Full SQ would also need signAction, quotient, quotientWitness, xFGroups,
-- cF, cFGroups, fGroupInclusion, xK, cK, extensions, signatures, and epsilon;
-- S1419Orbicurve supplies none of these.
end LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
