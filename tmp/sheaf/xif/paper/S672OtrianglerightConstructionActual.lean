import tmp.sheaf.xif.paper.S357OtrianglerightStructuralSheafActual
import tmp.sheaf.xif.paper.S369OtriSplitFrobenioidActual
import tmp.sheaf.xif.paper.S548SplitFrobenioidActual
import tmp.sheaf.xif.paper.S557QvPhiSplitFrobenioidConditional

-- S672: assembly over an existing SplitFrobenioidPresentation.  Actual
-- q/root sections and O_tri submonoid remain explicit exact data.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S672OtrianglerightConstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S357OtrianglerightStructuralSheafActual
open CategoryTheory
open Iut

universe u

variable {l : PrimeGeFive} {K : Type u} [Field K]

/-- Assembly of the S357 structure from explicit O_tri sections on any
SplitFrobenioidPresentation. -/
noncomputable def otrianglerightOfSections
    (S : Iut.SplitFrobenioidPresentation.{u})
    (baseObject : S.frobenioid.carrier)
    (Otri : Submonoid
      (Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism baseObject)))
    (qSection rootSection : Otri)
    (root_pow : rootSection ^ (2 * l.value) = qSection)
    (structuralSheafCondition : Prop) :
    OtrianglerightOnSplitFrobenioid (l := l) S where
  baseObject := baseObject
  Otri := Otri
  qSection := qSection
  rootSection := rootSection
  root_pow := root_pow
  structuralSheafCondition := structuralSheafCondition

/-- Exact candidate data: O_tri submonoid, sections, and a *proved*
structural-sheaf condition. -/
structure OtrianglerightCandidate
    (S : Iut.SplitFrobenioidPresentation.{u}) where
  baseObject : S.frobenioid.carrier
  Otri : Submonoid
    (Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism baseObject))
  qSection : Otri
  rootSection : Otri
  root_pow : rootSection ^ (2 * l.value) = qSection
  structuralSheafCondition : Prop
  structuralSheafCondition_holds : structuralSheafCondition
  qSection_reflects_qVFamily : Prop

noncomputable def otrianglerightOfCandidate
    {S : Iut.SplitFrobenioidPresentation.{u}}
    (C : OtrianglerightCandidate (l := l) S) :
    OtrianglerightOnSplitFrobenioid (l := l) S :=
  otrianglerightOfSections (l := l) S C.baseObject C.Otri
    C.qSection C.rootSection C.root_pow C.structuralSheafCondition

def OtrianglerightCandidateRequired
    (S : Iut.SplitFrobenioidPresentation.{u}) : Prop :=
  Nonempty (OtrianglerightCandidate (l := l) S)

#check otrianglerightOfSections
#check OtrianglerightCandidate
#check otrianglerightOfCandidate

end LeanFormal.IUT.XiFPaper.S672OtrianglerightConstructionActual

end