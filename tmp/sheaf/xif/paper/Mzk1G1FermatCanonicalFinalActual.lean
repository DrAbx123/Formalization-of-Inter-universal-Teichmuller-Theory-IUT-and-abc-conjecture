/- G1a canonical divisor degree ratio final. -/
import tmp.sheaf.xif.paper.Mzk1G1FermatCoverDataActual
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCoverDataActual
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatCanonicalFinalActual
def degOmega (n : Nat) : Rat := (n : Rat) - 3
def degOmegaE (n : Nat) : Rat := n
theorem canonical_ratio_mul (n : Nat) (hn : 3 < n) :
    (fermatCoverData n (le_of_lt hn)).canonicalRatio * degOmega n = degOmegaE n := by
  unfold fermatCoverData degOmega degOmegaE
  have h : (n : Rat) - 3 ≠ 0 := by
    have hlt : (3 : Rat) < (n : Rat) := by exact_mod_cast hn
    linarith
  field_simp [h]
theorem canonical_ratio_identity (n : Nat) (hn : 3 ≤ n) :
    (fermatCoverData n hn).canonicalRatio = (n : Rat) / ((n : Rat) - 3) := rfl
#print axioms canonical_ratio_mul
end LeanFormal.IUT.XiFPaper.Mzk1G1FermatCanonicalFinalActual
