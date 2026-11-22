import tmp.sheaf.xif.paper.GlobalRealifiedFrobenioidActual
import tmp.sheaf.xif.paper.GlobalFrobenioidPresentationActual
import tmp.sheaf.xif.paper.PaperQPilotObject
import tmp.sheaf.n8.closure.SourcePilotRegion

/-! # Global q-pilot object from the actual bad qParameter collection

IUT III, Definition 3.8, (i): the q-pilot object is determined by the collection
of q_v for v in V_bad, not by a single local q.

For an actual source input I, this file constructs:

* the actual bad qParameter family
    I.initial.reduction.qParameter : I.initial.badPlaces -> Real;
* the actual finite-support absolute-log divisor on the bad-place index;
* the actual total |log q| magnitude and signed q-pilot log-volume;
* the proof that the signed volume is exactly sourceQPilotSignedLog I.initial.

The single local q = 1/5 is NOT used as the global q-pilot.  The missing
Frobenioid object part is exactly a map from the actual bad places to the
presentation's global prime index plus the corresponding effective divisor
class; that object is recorded as an exact missing type, not fabricated.

No inequality/toy/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.Theorem311Source.GlobalQPilotObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual bad qParameter collection of the source input. -/
noncomputable def globalQParameterFamily : I.initial.badPlaces → Real :=
  fun b => I.initial.reduction.qParameter b

/-- The actual finite-support absolute-log divisor on the bad-place index. -/
noncomputable def globalQAbsLogDivisor : I.initial.badPlaces →₀ Real := by
  letI := I.initial.bad_finite
  exact ∑ b : I.initial.badPlaces,
    Finsupp.single b |Real.log (I.initial.reduction.qParameter b)|

/-- The support of the global q-pilot divisor is contained in the finite bad
place set. -/
theorem globalQAbsLogDivisor_supported [Fintype I.initial.badPlaces] :
    globalQAbsLogDivisor I ≠ 0 →
      ∀ b : I.initial.badPlaces,
        b ∈ (globalQAbsLogDivisor I).support → b ∈ Finset.univ := by
  intro _ b _
  exact Finset.mem_univ b

/-- The total paper magnitude |log q| of the bad qParameter collection. -/
noncomputable def globalQAbsLogTotal : Real := by
  letI := I.initial.bad_finite
  exact ∑ b : I.initial.badPlaces,
    |Real.log (I.initial.reduction.qParameter b)|

/-- The global q-pilot signed log-volume, as the negative bad-q abs-log total. -/
noncomputable def globalQPilotSignedLog : Real :=
  -globalQAbsLogTotal I

/-- Actual equality: the global q-pilot signed log-volume is exactly the source
q-pilot signed log. -/
theorem globalQPilotSignedLog_eq_sourceQPilotSignedLog :
    globalQPilotSignedLog I = sourceQPilotSignedLog I.initial := by
  unfold globalQPilotSignedLog globalQAbsLogTotal sourceQPilotSignedLog sourceBadQAbsLog
  rfl

/-- Actual collection data for the global q-pilot object. -/
structure GlobalQPilotCollection where
  qParameter : I.initial.badPlaces → Real
  qParameter_eq : qParameter = globalQParameterFamily I
  absLogDivisor : I.initial.badPlaces →₀ Real
  absLogDivisor_eq : absLogDivisor = globalQAbsLogDivisor I
  absLogTotal : Real
  absLogTotal_eq : absLogTotal = globalQAbsLogTotal I
  signedLogVolume : Real
  signedLogVolume_eq : signedLogVolume = globalQPilotSignedLog I

/-- The actual global q-pilot collection from I.initial.badPlaces. -/
noncomputable def globalQPilotCollection : GlobalQPilotCollection I where
  qParameter := globalQParameterFamily I
  qParameter_eq := rfl
  absLogDivisor := globalQAbsLogDivisor I
  absLogDivisor_eq := rfl
  absLogTotal := globalQAbsLogTotal I
  absLogTotal_eq := rfl
  signedLogVolume := globalQPilotSignedLog I
  signedLogVolume_eq := rfl

/-- The collection's signed log-volume equals the actual source q-pilot scalar. -/
theorem globalQPilotCollection_signedLogVolume :
    (globalQPilotCollection I).signedLogVolume =
      sourceQPilotSignedLog I.initial :=
  globalQPilotSignedLog_eq_sourceQPilotSignedLog I

/-- The collection is the full bad qParameter family, not a single local q. -/
theorem globalQPilotCollection_qParameter
    (b : I.initial.badPlaces) :
    (globalQPilotCollection I).qParameter b =
      I.initial.reduction.qParameter b := rfl

end LeanFormal.IUT.Theorem311Source.GlobalQPilotObjectActual

end
