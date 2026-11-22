import tmp.sheaf.xif.paper.Mzk1G1ABCHeightBridgeDoneActual
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverActual
import Mathlib
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FreyHeightFromCoverActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ABCHeightBridgeDoneActual
open LeanFormal.IUT.XiFPaper.Mzk1G1Actual
/-- G1 Frey height/cover bundle: an actual ABC bridge dictionary, a Fermat
cover, and the different bound. -/
structure FreyHeightFromCover (a b c n rad : Nat) : Prop where
  bridge : ABCHeightRadicalBridge a b c
  cover : FermatCoverData ℚ
  cover_n : cover.n = n
  different : fermatLogDifferent n ≤ Real.log (rad : ℝ) + (n : ℝ)
theorem freyHeightFromCover_actual {a b c : Nat} (h : IsABCTriple a b c)
    (n rad : Nat) (hn : 0 < n) (hrad : 1 ≤ rad) :
    FreyHeightFromCover a b c n rad where
  bridge := abcHeightRadicalBridge_of_isABCTriple h
  cover := fermatCoverData (k := ℚ) (n := n) hn
  cover_n := rfl
  different := fermatLogDifferent_le_log_radical_add n rad (Nat.succ_le_of_lt hn) hrad
#print axioms freyHeightFromCover_actual
end LeanFormal.IUT.XiFPaper.Mzk1G1FreyHeightFromCoverActual
end