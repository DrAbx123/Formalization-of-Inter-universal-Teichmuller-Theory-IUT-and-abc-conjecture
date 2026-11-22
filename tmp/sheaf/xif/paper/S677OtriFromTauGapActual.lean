import tmp.sheaf.xif.paper.S672OtrianglerightConstructionActual
import tmp.sheaf.xif.paper.S369OtriSplitFrobenioidActual
import tmp.sheaf.xif.paper.S373NativeStageSplittingActual
import tmp.sheaf.xif.paper.S379NativeStageTauExactMissingActual

-- S677: existing tau/splitting supplies tau submonoids of O^triangle, but
-- not the O_tri units submonoid or q/root sections.  Exact split gap.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S677OtriFromTauGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S369OtriSplitFrobenioidActual
open LeanFormal.IUT.XiFPaper.S373NativeStageSplittingActual
open LeanFormal.IUT.XiFPaper.S379NativeStageTauExactMissingActual
open LeanFormal.IUT.XiFPaper.S672OtrianglerightConstructionActual
open Iut

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Conditional actual split from an explicit stage characteristic splitting. -/
noncomputable def splitOfStageSplitting
    (C : (nativeStageFrobenioidPresentation T b).preFrobenioid.CharacteristicSplitting
      (nativeStageRationalMonoidTransport T b)) :
    Iut.SplitFrobenioidPresentation :=
  nativeStageSplitFrobenioidPresentation (l := l) T b C

/-- Exact data that tau/splitting does not supply: O_tri units submonoid and
its q/root sections, plus the structural-sheaf condition. -/
structure OtriCandidateFromTauData
    (S : Iut.SplitFrobenioidPresentation) where
  splitting : Prop
  baseObject : S.frobenioid.carrier
  Otri : Submonoid
    (Units (S.frobenioid.preFrobenioid.LinearBaseIdentityEndomorphism baseObject))
  qSection : Otri
  rootSection : Otri
  root_pow : rootSection ^ (2 * l.value) = qSection
  structuralSheafCondition : Prop
  structuralSheafCondition_holds : structuralSheafCondition
  qSection_reflects_qVFamily : Prop

noncomputable def otriCandidateOfTauData
    {S : Iut.SplitFrobenioidPresentation}
    (D : OtriCandidateFromTauData (l := l) S) :
    OtrianglerightCandidate (l := l) S where
  baseObject := D.baseObject
  Otri := D.Otri
  qSection := D.qSection
  rootSection := D.rootSection
  root_pow := D.root_pow
  structuralSheafCondition := D.structuralSheafCondition
  structuralSheafCondition_holds := D.structuralSheafCondition_holds
  qSection_reflects_qVFamily := D.qSection_reflects_qVFamily

def OtriCandidateFromTauDataRequired
    (S : Iut.SplitFrobenioidPresentation) : Prop :=
  Nonempty (OtriCandidateFromTauData (l := l) S)

#check splitOfStageSplitting
#check OtriCandidateFromTauData
#check otriCandidateOfTauData

end LeanFormal.IUT.XiFPaper.S677OtriFromTauGapActual

end