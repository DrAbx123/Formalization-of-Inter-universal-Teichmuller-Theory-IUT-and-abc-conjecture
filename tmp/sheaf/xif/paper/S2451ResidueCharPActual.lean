import tmp.sheaf.xif.paper.S2450ResidueIsAlgClosedActual
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2442ResidueAction
namespace LeanFormal.IUT.XiFPaper.S2451ResidueCharPActual
variable (p : Nat) [Fact (Nat.Prime p)]
theorem S2451_residue_natCast_zero :
    (p : PadicResidueField p) = 0 := by
  have hnonunit : ¬ IsUnit (p : PadicValuationSubring p) := by
    let V : ValuationSubring (PadicAlgCl p) :=
      (Valued.v (R := PadicAlgCl p)).valuationSubring
    change ¬ IsUnit (p : V)
    rw [ValuationSubring.valuation_eq_one_iff]
    have heq := (Valuation.isEquiv_valuation_valuationSubring
      (v := Valued.v (R := PadicAlgCl p))).eq_one_iff_eq_one
        (x := ((p : V) : PadicAlgCl p))
    rw [← heq]
    have hpv : Valued.v (p : PadicAlgCl p) < 1 := by
      rw [PadicAlgCl.valuation_p, one_div]
      have hp1 : (1 : NNReal) < (p : NNReal) := by
        exact_mod_cast (Fact.out : Nat.Prime p).one_lt
      exact inv_lt_one_of_one_lt₀ hp1
    exact ne_of_lt hpv

  have hmem : (p : PadicValuationSubring p) ∈
      IsLocalRing.maximalIdeal (PadicValuationSubring p) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hnonunit
  have hres : IsLocalRing.residue (PadicValuationSubring p)
      (p : PadicValuationSubring p) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact hmem
  rw [← map_natCast (IsLocalRing.residue (PadicValuationSubring p)) p]
  exact hres
theorem S2451_residue_charP : CharP (PadicResidueField p) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : Nat.Prime p)).mpr
  exact S2451_residue_natCast_zero p
#check S2451_residue_charP
end LeanFormal.IUT.XiFPaper.S2451ResidueCharPActual
end
