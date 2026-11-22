import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2708MultiQSourcePilotActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper

universe ua uv upi umon ui uL uC uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Minimal multi-q compatibility layer: a finite family of actual finite-place
q candidates whose total local log magnitude is explicitly identified with the
source bad-q absolute log.  It does not change SourcePilotRegionData or its
single-q field. -/
structure MultiQSourcePilotData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  index : Type
  [fintype : Fintype index]
  place : index -> NumberField.FinitePlace (I.initial.arithmetic.Fmod)
  q : (i : index) -> FinitePlaceQCandidate (place i)
  logVolume : Real
  logVolume_eq : logVolume = ∑ i : index, localLogMagnitude (q i)
  logVolume_eq_source : logVolume = sourceBadQAbsLog I.initial

attribute [instance] MultiQSourcePilotData.fintype

noncomputable def multiQLogVolume
    (Q : MultiQSourcePilotData (I := I)) : Real :=
  Q.logVolume

theorem multiQLogVolume_eq_sourceBadQAbsLog
    (Q : MultiQSourcePilotData (I := I)) :
    multiQLogVolume Q = sourceBadQAbsLog I.initial :=
  Q.logVolume_eq_source

noncomputable def multiQPaperQPilotLogVolume
    (Q : MultiQSourcePilotData (I := I)) : Real :=
  -multiQLogVolume Q

theorem multiQPaperQPilotLogVolume_eq_sourceQPilotSignedLog
    (Q : MultiQSourcePilotData (I := I)) :
    multiQPaperQPilotLogVolume Q = sourceQPilotSignedLog I.initial := by
  unfold multiQPaperQPilotLogVolume sourceQPilotSignedLog
  rw [multiQLogVolume_eq_sourceBadQAbsLog]

/-- Replace only the q-pilot scalar of an existing PaperQPilotObject, keeping
all structural fields untouched. -/
noncomputable def replaceQPilotLogVolume
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (v : Real) (hv : v = sourceQPilotSignedLog I.initial) :
    PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip :=
  { O with qPilotLogVolume := v, qPilotLogVolume_eq := hv }

noncomputable def multiQPaperQPilotObject
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (Q : MultiQSourcePilotData (I := I)) :
    PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip :=
  replaceQPilotLogVolume O (-multiQLogVolume Q)
    (by
      rw [multiQLogVolume_eq_sourceBadQAbsLog]
      rfl)

theorem multiQPaperQPilotObject_qPilotLogVolume
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip V}
    (O : PaperQPilotObject (l := l) (V := V) (Label := Label) (Choice := Choice)
      I G envStrip)
    (Q : MultiQSourcePilotData (I := I)) :
    (multiQPaperQPilotObject O Q).qPilotLogVolume = -sourceBadQAbsLog I.initial := by
  unfold multiQPaperQPilotObject replaceQPilotLogVolume
  simp [multiQLogVolume_eq_sourceBadQAbsLog]

#check MultiQSourcePilotData
#check multiQLogVolume_eq_sourceBadQAbsLog
#check multiQPaperQPilotLogVolume_eq_sourceQPilotSignedLog
#check multiQPaperQPilotObject
#check multiQPaperQPilotObject_qPilotLogVolume
#print axioms multiQLogVolume_eq_sourceBadQAbsLog
#print axioms multiQPaperQPilotObject_qPilotLogVolume
end LeanFormal.IUT.XiFPaper.S2708MultiQSourcePilotActual
end
