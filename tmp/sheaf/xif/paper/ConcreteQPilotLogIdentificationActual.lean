import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.PaperQPilotLogVolume
import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.paper.NativeQNormActual
import tmp.sheaf.xif.paper.ConcreteC3DonorActual

/-! # Concrete q-pilot log identifications

For a concrete PaperQPilotObject O, an actual PaperQPilotObjectActual Oa whose
line C3 is the chosen SourcePilotRegionData, this file proves the available
scalar projections:

* O.qPilotLogVolume = sourceQPilotSignedLog I.initial;
* Oa.signedQPilotLogVolume = localSignedLog C3.q;
* paperQPilotLogVolume C3 = localSignedLog C3.q.

The two requested identifications
  O.qPilotLogVolume = paperQPilotLogVolume C3
and
  O.qPilotLogVolume = Oa.signedQPilotLogVolume
reduce exactly to the source q identification

  ConcreteSourceQIdentification := sourceQPilotSignedLog I.initial = localSignedLog C3.q.

That equality is not fabricated; it is the exact missing source q component
comparison.  Conditional actual theorems prove both identifications from it.
No inequality/True/toy/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.ConcreteQPilotLogIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe ua uv upi umon ui uG uL uC uC3 uD3

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}

variable (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
variable (Oa : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I))
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)


/-- Actual projection: the concrete paper q-pilot scalar is the source
q-pilot signed log. -/
theorem concreteO_qPilotLogVolume_source :
    O.qPilotLogVolume = sourceQPilotSignedLog I.initial :=
  O.qPilotLogVolume_eq

/-- Actual projection: the source C3 paper q-pilot scalar is the local signed
completion log. -/
theorem concretePaperQPilotLogVolume_eq_localSignedLog :
    paperQPilotLogVolume C3 = localSignedLog C3.q := rfl

/-- Exact source-q identification required for both requested equalities. -/
def ConcreteSourceQIdentification : Prop :=
  sourceQPilotSignedLog I.initial = localSignedLog C3.q

/-- Actual projection: if the actual object's line C3 is the chosen C3, then
its signed q-pilot log-volume is the local signed completion log. -/
theorem concreteOa_signedQPilotLogVolume_eq_localSignedLog
    (hC3 : Oa.line.C3 = C3) :
    Oa.signedQPilotLogVolume = localSignedLog C3.q := by
  unfold PaperQPilotObjectActual.signedQPilotLogVolume
  rw [hC3]

/-- Conditional actual identification O.qPilotLogVolume = paperQPilotLogVolume C3. -/
theorem concreteO_qPilotLogVolume_eq_paper
    (h : ConcreteSourceQIdentification (I := I) C3) :
    O.qPilotLogVolume = paperQPilotLogVolume C3 := by
  rw [concreteO_qPilotLogVolume_source O, h,
    concretePaperQPilotLogVolume_eq_localSignedLog C3]

/-- Conditional actual identification O.qPilotLogVolume = Oa.signedQPilotLogVolume. -/
theorem concreteO_qPilotLogVolume_eq_signed
    (hC3 : Oa.line.C3 = C3)
    (h : ConcreteSourceQIdentification (I := I) C3) :
    O.qPilotLogVolume = Oa.signedQPilotLogVolume := by
  rw [concreteO_qPilotLogVolume_source O, h,
    ← concreteOa_signedQPilotLogVolume_eq_localSignedLog Oa C3 hC3]

/-- The exact equality obstacle: the source q-pilot scalar and the chosen C3
local signed log are not identified by the concrete data. -/
def ConcreteQPilotLogIdentificationObstruction : Prop :=
  ConcreteSourceQIdentification (I := I) C3

/-- Both requested equalities are equivalent to the source-q identification
once the actual object's C3 is fixed. -/
theorem concreteQPilotLogIdentifications_iff_sourceQ
    (hC3 : Oa.line.C3 = C3) :
    (O.qPilotLogVolume = paperQPilotLogVolume C3 ∧
      O.qPilotLogVolume = Oa.signedQPilotLogVolume) ↔
      ConcreteSourceQIdentification (I := I) C3 := by
  constructor
  · intro hpair
    have hpaper : O.qPilotLogVolume = localSignedLog C3.q :=
      hpair.1.trans (concretePaperQPilotLogVolume_eq_localSignedLog C3)
    exact (concreteO_qPilotLogVolume_source O).symm.trans hpaper
  · intro h
    exact ⟨concreteO_qPilotLogVolume_eq_paper O C3 h,
      concreteO_qPilotLogVolume_eq_signed O Oa C3 hC3 h⟩

end LeanFormal.IUT.Theorem311Source.ConcreteQPilotLogIdentificationActual

end
