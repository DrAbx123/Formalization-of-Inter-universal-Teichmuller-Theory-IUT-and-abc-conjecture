import tmp.sheaf.n8.closure.P6HullActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import Mathlib

/-!
# P6 actual adm_out attempt

The exact P6 interface only requires a predicate Adm_out containing every
source output singleton and the actual source hull.  This file constructs the
minimal H-admissibility predicate

  hullAdmOut R := R.Nonempty and R subset sourcePaperHull

from the actual source U/sourceHolomorphicHull.  It is not True (the empty set
is rejected) and it satisfies ActualP6AdmOutData.

This is deliberately only H-admissibility, not the paper's full Stp4 Adm_out
condition.  The latter remains the exact source donor; no claim is made here
that H-admissibility equals Stp4 admissibility.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6AdmActualAttempt

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.C7SourceU
open LeanFormal.IUT.N8Closure.P6Hull
open LeanFormal.IUT.N8Closure.P6HullActual

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Label : Type uL} [Group Label]
variable (D : SourceWitnessedOutputData (l := l) (V := V) I Label)
variable (n : ThetaPilotCarrier l)
variable (x : I.ThetaPilotPoint D.place.v)

/-- Minimal H-admissibility: nonempty and contained in the actual source hull. -/
def hullAdmOut (R : Set (SourceCarrier (D := D))) : Prop :=
  R.Nonempty ∧ R ⊆ sourcePaperHull (D := D) n

/-- Every actual source output singleton is H-admissible. -/
theorem hullAdmOut_sourceR (w : SourceAlpha (D := D) n x) :
    hullAdmOut (D := D) n (sourceR (D := D) n x w) := by
  constructor
  · exact ⟨D.witnessOutput w, by simp [sourceR]⟩
  · intro y hy
    have hy' : y = D.witnessOutput w := by simpa [sourceR] using hy
    refine sourceU_subset_sourceHolomorphicHull (D := D) n x ⟨w.1, ?_⟩
    rw [D.witnessOutput_eq_eval] at hy'
    exact hy'.symm

/-- The actual source hull itself is H-admissible. -/
theorem hullAdmOut_sourcePaperHull :
    hullAdmOut (D := D) n (sourcePaperHull (D := D) n) := by
  constructor
  · exact ⟨I.sourceThetaPilotPoint D.place.v D.place.R n zeroSignedLabel,
      sourceThetaPilotPoint_mem_sourceHolomorphicHull
        (I := I) D.place.v D.place.R n zeroSignedLabel⟩
  · exact subset_rfl

/-- The minimal H-admissibility data satisfy the exact ActualP6AdmOutData
interface. -/
def hullAdmOutData : ActualP6AdmOutData (D := D) n x where
  adm_out := hullAdmOut (D := D) n
  sourceR_admissible := hullAdmOut_sourceR (D := D) n x
  sourceHull_admissible := hullAdmOut_sourcePaperHull (D := D) n

/-- The candidate is not the constantly-true predicate: the empty region is
rejected. -/
theorem hullAdmOut_not_true :
    ¬ ∀ R : Set (SourceCarrier (D := D)), hullAdmOut (D := D) n R := by
  intro h
  exact Set.not_nonempty_empty (h ∅).1

/-- The actual P6HullSetup obtained from the minimal H-admissibility data. -/
def actualP6HullSetupFromHullAdm : P6HullSetup :=
  actualP6HullSetup (D := D) n x (hullAdmOutData (D := D) n x)

end LeanFormal.IUT.N8Closure.P6AdmActualAttempt
