import tmp.sheaf.xif.paper.ResidueCardBridgeAttempt
import tmp.sheaf.xif.paper.Mzk1ActualRamifiedDataActual
import tmp.sheaf.xif.paper.Node09AbsNormRatActual
import tmp.sheaf.xif.paper.NormalizedCompletionPadicBridgeActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.XiFPaper.ResidueCardBridgeAttempt
open LeanFormal.IUT.XiFPaper.Node09AbsNormRatActual
open LeanFormal.IUT.XiFPaper.NormalizedCompletionPadicBridgeActual

namespace LeanFormal.IUT.XiFPaper.Node09HresidueDegreeActual

variable {p : Nat} [Fact p.Prime]

/-- Fmod = Q: the relative local residue degree equals actualFn, by comparing
p-powers (residue norm bridge + residueNormBase_eq_lower_pow + pow injective). -/
theorem localResidueDegree_rat_eq_actualFn
    (place : FinitePlaceAtPrime ℚ p) :
    localResidueDegree (k := ℚ) place.val = actualFn place := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcardNat : logShellResidueCard (K := NormalizedCompletion place.val) =
      p ^ actualFn place := by
    simpa [place.property] using (actualFn_spec place).2
  have hresNat : residueNormBase place.val =
      ((completionRationalPrime place.val).val : ℝ) := residueNormBase_rat_eq place.val
  have hpval : (completionRationalPrime place.val).val = p := place.property
  have hresR : residueNormBase place.val = (p : ℝ) := by
    rw [hresNat, hpval]
  have hlow : residueNormBase (comap (k := ℚ) place.val) = (p : ℝ) := by
    rw [comap_self_rat place.val]
    exact hresR
  have hcardR : (logShellResidueCard (K := NormalizedCompletion place.val) : ℝ) =
      (p : ℝ) ^ actualFn place := by
    rw [hcardNat]
    push_cast
    rfl
  have hpair : (p : ℝ) ^ localResidueDegree (k := ℚ) place.val =
      (p : ℝ) ^ actualFn place := by
    have h := residueNormBase_eq_lower_pow (k := ℚ) place.val
    rw [hlow] at h
    calc (p : ℝ) ^ localResidueDegree (k := ℚ) place.val
        = residueNormBase place.val := h.symm
      _ = (logShellResidueCard (K := NormalizedCompletion place.val) : ℝ) :=
          (logShellResidueCard_eq_residueNormBase place.val).symm
      _ = (p : ℝ) ^ actualFn place := hcardR
  have hnat : p ^ localResidueDegree (k := ℚ) place.val = p ^ actualFn place := by
    exact_mod_cast hpair
  exact Nat.pow_right_injective hp hnat

end LeanFormal.IUT.XiFPaper.Node09HresidueDegreeActual
