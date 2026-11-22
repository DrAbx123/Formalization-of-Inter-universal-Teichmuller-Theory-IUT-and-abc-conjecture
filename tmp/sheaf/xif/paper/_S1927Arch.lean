import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open NumberField

namespace ProbeArch

abbrev fmod (D : S1895PaperInput) : Type := (S1895PaperInput.I D).initial.arithmetic.Fmod

def archimedeanUnitBall (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (fmod D)) : Set w.Completion :=
  {x | ‖x‖ ≤ 1}

structure ArchAt (D : S1895PaperInput)
    (w : NumberField.InfinitePlace (fmod D)) where
  [moduleK : Module Real w.Completion]
  logShell : Set w.Completion
  logShell_subset_unitBall : logShell ⊆ archimedeanUnitBall D w
  zero_mem_logShell : (0 : w.Completion) ∈ logShell
  convex_logShell : Convex Real logShell
  isCompact_logShell : IsCompact logShell



def FirstMissing (D : S1895PaperInput) : Type :=
  (w : NumberField.InfinitePlace (fmod D)) -> ArchAt D w

end ProbeArch

