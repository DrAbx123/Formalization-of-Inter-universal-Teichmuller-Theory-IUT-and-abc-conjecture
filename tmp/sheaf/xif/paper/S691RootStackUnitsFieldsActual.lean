import tmp.sheaf.xif.paper.S688OtriFromRootStackSectionMapActual
import tmp.sheaf.xif.paper.S680OtriUnitsFromLogShellSectionsActual

-- S691: Units(O^triangle) fields are frobeniusDegree=1, base=id, divisor,
-- rationalFunction.  A root/root-stack unit has no such coordinates; the
-- map needs a new carrier plus divisor-zero/inverse data.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S691RootStackUnitsFieldsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S688OtriFromRootStackSectionMapActual
open LeanFormal.IUT.XiFPaper.S680OtriUnitsFromLogShellSectionsActual
open LeanFormal.IUT.XiFPaper.S677OtriFromTauGapActual
open Iut

universe u

variable {l : PrimeGeFive}
variable (S : Iut.SplitFrobenioidPresentation.{u})
variable (A : S.frobenioid.carrier)

/-- Field-level data of an O^triangle unit at A. -/
structure OTriangleUnitCoordinates where
  unit : Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism A)
  divisor_zero : (S.frobenioid.preFrobenioid).divisor unit.1.hom = 0
  rationalFunction : Prop
  inverse_rationalFunction : Prop

/-- Exact interface needed to map a root/root-stack section monoid to
O^triangle units: a new section carrier, a monoid map, q/root sections,
and the divisor-zero coordinate data. -/
structure RootStackUnitsFieldsData where
  sectionCarrier : Type u
  [monoid : Monoid sectionCarrier]
  sectionMap : sectionCarrier →*
    Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism A)
  qSection : sectionCarrier
  rootSection : sectionCarrier
  root_pow : rootSection ^ (2 * l.value) = qSection
  q_coordinate : OTriangleUnitCoordinates (S := S) (A := A)
  q_image : sectionMap qSection = q_coordinate.unit
  root_coordinate : OTriangleUnitCoordinates (S := S) (A := A)
  root_image : sectionMap rootSection = root_coordinate.unit
  structuralSheafCondition : Prop
  structuralSheafCondition_holds : structuralSheafCondition
  qSection_reflects_qVFamily : Prop

noncomputable def otriCandidateFromRootStackUnitsFields
    (D : RootStackUnitsFieldsData (l := l) (S := S) (A := A)) :
    OtriCandidateFromTauData (l := l) S := by
  letI : Monoid D.sectionCarrier := D.monoid
  exact otriCandidateFromLogShellSections (l := l) S
    { sections :=
        { baseObject := A
          qUnit := D.q_coordinate.unit
          rootUnit := D.root_coordinate.unit
          root_pow := by
            rw [← D.root_image, ← D.q_image, ← map_pow, D.root_pow] }
      splitting := True
      structuralSheafCondition := D.structuralSheafCondition
      structuralSheafCondition_holds := D.structuralSheafCondition_holds
      qSection_reflects_qVFamily := D.qSection_reflects_qVFamily }

def RootStackUnitsFieldsRequired : Prop :=
  Nonempty (RootStackUnitsFieldsData (l := l) (S := S) (A := A))

#check OTriangleUnitCoordinates
#check RootStackUnitsFieldsData
#check otriCandidateFromRootStackUnitsFields

end LeanFormal.IUT.XiFPaper.S691RootStackUnitsFieldsActual

end