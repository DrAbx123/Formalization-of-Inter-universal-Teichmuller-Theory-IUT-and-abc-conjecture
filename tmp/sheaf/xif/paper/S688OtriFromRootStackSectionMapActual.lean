import tmp.sheaf.xif.paper.S392RootStackSectionMonoidActual
import tmp.sheaf.xif.paper.S680OtriUnitsFromLogShellSectionsActual
import tmp.sheaf.xif.paper.S681OtriQSectionReflectionNoGoActual

-- S688: no actual map from S392 SectionCarrier to Units(O^triangle) exists.
-- Given such a monoid map, S680 constructs the O_tri candidate conditionally.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S688OtriFromRootStackSectionMapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S392RootStackSectionMonoidActual
open LeanFormal.IUT.XiFPaper.S680OtriUnitsFromLogShellSectionsActual
open LeanFormal.IUT.XiFPaper.S677OtriFromTauGapActual
open LeanFormal.IUT.XiFPaper.S681OtriQSectionReflectionNoGoActual
open Iut

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (S : Iut.SplitFrobenioidPresentation.{u})
variable (A : S.frobenioid.carrier)

/-- A monoid map from the S392 root-stack section carrier to O^triangle units. -/
abbrev RootStackSectionUnitsMap : Type u :=
  SectionCarrier T b →* Units
    (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism A)

/-- Conditional q/root units from a section map. -/
noncomputable def otriUnitsSectionsOfRootStackMap
    (φ : RootStackSectionUnitsMap (T := T) (b := b) (S := S) (A := A)) :
    OtriUnitsSections (l := l) S where
  baseObject := A
  qUnit := φ (qSectionCandidate T b)
  rootUnit := φ (rootSectionCandidate T b)
  root_pow := by
    rw [← map_pow, rootSectionCandidate_pow]

/-- Conditional S680 minimal data from a section map plus structural data. -/
structure RootStackSectionStructuralData
    (φ : RootStackSectionUnitsMap (T := T) (b := b) (S := S) (A := A)) where
  splitting : Prop
  structuralSheafCondition : Prop
  structuralSheafCondition_holds : structuralSheafCondition
  qSection_reflects_qVFamily : Prop

noncomputable def otriFromRootStackSectionMap
    (φ : RootStackSectionUnitsMap (T := T) (b := b) (S := S) (A := A))
    (D : RootStackSectionStructuralData (T := T) (b := b) (S := S) (A := A) φ) :
    OtriCandidateFromTauData (l := l) S :=
  otriCandidateFromLogShellSections (l := l) S
    { sections := otriUnitsSectionsOfRootStackMap (T := T) (b := b) (S := S) (A := A) φ
      splitting := D.splitting
      structuralSheafCondition := D.structuralSheafCondition
      structuralSheafCondition_holds := D.structuralSheafCondition_holds
      qSection_reflects_qVFamily := D.qSection_reflects_qVFamily }

/-- Exact minimal datum: a section-map plus its structural fields. -/
structure RootStackSectionUnitsMapGap where
  sectionMap : RootStackSectionUnitsMap (T := T) (b := b) (S := S) (A := A)
  structural : RootStackSectionStructuralData (T := T) (b := b) (S := S) (A := A) sectionMap

def RootStackSectionUnitsMapGapRequired : Prop :=
  Nonempty (RootStackSectionUnitsMapGap (T := T) (b := b) (S := S) (A := A))

#check RootStackSectionUnitsMap
#check otriUnitsSectionsOfRootStackMap
#check otriFromRootStackSectionMap
#check RootStackSectionUnitsMapGap

end LeanFormal.IUT.XiFPaper.S688OtriFromRootStackSectionMapActual

end