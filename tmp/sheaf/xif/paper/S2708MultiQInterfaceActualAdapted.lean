import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.xif.PaperQPilotLogVolume
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual
import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataUnconditionalActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2708MultiQInterfaceActualAdapted

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Candidate multi-q carrier: one actual completion q candidate per finite
place in a finite index family.  This is the object the current
`SourcePilotRegionData` does **not** carry (it has one `q`). -/
structure S2708MultiQFamily where
  index : Type
  [indexFintype : Fintype index]
  place : index -> NumberField.FinitePlace (I.initial.arithmetic.Fmod)
  q : (i : index) -> FinitePlaceQCandidate (place i)

attribute [instance] S2708MultiQFamily.indexFintype

/-- Multi-place signed log-volume: sum of the actual completion log norms. -/
noncomputable def S2708MultiSignedLog (F : S2708MultiQFamily (I := I)) : Real :=
  ∑ i : F.index, Real.log ‖(F.q i).q‖

/-- Multi-place magnitude: negative of the signed sum. -/
noncomputable def S2708MultiMagnitude (F : S2708MultiQFamily (I := I)) : Real :=
  - S2708MultiSignedLog F

/-- Multi-place norm product. -/
noncomputable def S2708MultiNormProduct (F : S2708MultiQFamily (I := I)) : Real :=
  ∏ i : F.index, ‖(F.q i).q‖

theorem S2708MultiNormProduct_eq_exp (F : S2708MultiQFamily (I := I)) :
    S2708MultiNormProduct F = Real.exp (S2708MultiSignedLog F) := by
  unfold S2708MultiNormProduct S2708MultiSignedLog
  rw [Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact (Real.exp_log (norm_pos_iff.mpr (F.q i).q_ne_zero)).symm

/-- The current single-q C3 is the one-point special case of the multi-q
carrier.  This is the only actual embedding available from
`actualSignedC3`; it does not supply a genuine multi-place family. -/
noncomputable def S2708SingleFamily
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    S2708MultiQFamily (I := I) where
  index := PUnit
  place _ := C3.place.val
  q _ := C3.q

theorem S2708SingleFamily_signedLog
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    S2708MultiSignedLog (S2708SingleFamily C3) =
      Real.log ‖C3.q.q‖ := by
  rfl

theorem S2708SingleFamily_magnitude
    (C3 : SourcePilotRegionData (l := l) (V := V) I) :
    S2708MultiMagnitude (S2708SingleFamily C3) =
      paperQPilotLogMagnitude C3 := by
  simp [S2708MultiMagnitude, S2708SingleFamily_signedLog,
    paperQPilotLogMagnitude, paperQPilotLogVolume, localSignedLog,
    localLogMagnitude]

#print axioms S2708MultiNormProduct_eq_exp
#print axioms S2708SingleFamily_magnitude

end LeanFormal.IUT.XiFPaper.S2708MultiQInterfaceActualAdapted
end
