import tmp.sheaf.xif.paper.S1490OrbicurveFundamentalGroupActual
import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
import tmp.sheaf.xif.paper.S2878GroupsInputActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1490OrbicurveFundamentalGroupActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2878GroupsInputActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 160000

namespace LeanFormal.IUT.XiFPaper.S3122XFGroupsAudit

variable {l : PrimeGeFive}

/-- xFGroups target: SourceOrbicurveGroupData on S1536XF at the absolute
Galois group. -/
def S3122XFGroupsTarget : Prop :=
  Nonempty (SourceOrbicurveGroupData (S1536XF (l := l))
    (Iut.AbsoluteGaloisProfinite (S1280Arithmetic l).F))

/-- S1490 target: OrbicurveFundamentalGroupData on S1419Orbicurve at S1490Galois. -/
def S3122S1490Target : Prop :=
  Nonempty (S1490Target (l := l))

/-- Exact equivalence: xFGroups is the S1490 fundamental-group datum. -/
theorem S3122XFGroups_iff_S1490 :
    S3122XFGroupsTarget (l := l) ↔ S3122S1490Target (l := l) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.groups⟩
  · rintro ⟨D⟩
    exact ⟨⟨D⟩⟩

/-- Exact first missing structure for xFGroups. -/
abbrev S3122FirstMissing : Type 1 :=
  S1490ArithmeticPiFirstMissing (l := l)

/-- Exact second missing geometric certificate. -/
abbrev S3122SecondMissing (C : S3122FirstMissing (l := l)) : Type 1 :=
  S1490GeometricPiSecondMissing C

#check S3122XFGroupsTarget
#check S3122S1490Target
#check S3122XFGroups_iff_S1490
#check S3122FirstMissing
#check S3122SecondMissing
#check S1490Target_nonempty_iff_firstMissing
#check S1490Target_nonempty_iff_gap
#check S1490ModelArithmeticGroup

end LeanFormal.IUT.XiFPaper.S3122XFGroupsAudit
end