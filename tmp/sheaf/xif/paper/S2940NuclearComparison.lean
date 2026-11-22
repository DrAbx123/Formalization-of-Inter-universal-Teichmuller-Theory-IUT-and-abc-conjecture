import tmp.sheaf.xif.paper.S2921HeightBridgeActual
import tmp.sheaf.xif.paper.S2743SupportIdealAbsNormLowerActual
import tmp.sheaf.xif.paper.S2749SupportEqualityActual
import tmp.sheaf.xif.paper.S2833S2800HregionActual
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual
import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2921HeightBridgeActual
open LeanFormal.IUT.XiFPaper.S2743SupportIdealAbsNormLowerActual
open LeanFormal.IUT.XiFPaper.S2749SupportEqualityActual
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2739FinsetSupportActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2940NuclearComparison

theorem S2940_prod_supportIndex (a b c : Nat) (habc : IsABCTriple a b c) :
    (∏ i : SupportIndex (abcRationalPoint a c), i.1) = natRadical (a * b * c) := by
  rw [← S2749_prod_support_eq_radical habc]
  exact Finset.prod_attach (s := arithmeticPrimeSupport (abcRationalPoint a c))
    (f := fun p => p)

theorem S2940_S_ge_log_rad (a b c : Nat) (habc : IsABCTriple a b c) :
    Real.log ((natRadical (a * b * c) : Nat) : Real) ≤ S2921S a b c := by
  have hle := S2743_prod_support_le_supportIdeal_absNorm
    (K := (S2735Arithmetic S2771FiveLabel).K) (abcRationalPoint a c)
  rw [S2940_prod_supportIndex a b c habc] at hle
  have hle' : ((natRadical (a * b * c) : Nat) : Real) ≤
      ((Ideal.absNorm (S2752J S2771FiveLabel a b c) : Nat) : Real) := by
    exact_mod_cast hle
  unfold S2921S
  exact Real.log_le_log (by exact_mod_cast natRadical_pos (a * b * c)) hle'

theorem S2940_S_ge_arithmeticWeight (a b c : Nat) (habc : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c) ≤ S2921S a b c := by
  rw [arithmeticWeight_abcRationalPoint habc]
  exact S2940_S_ge_log_rad a b c habc

theorem S2940_Q_eq_two_region (a b c : Nat) :
    S2921Q a b c = 2 * S2792RegionVolume a b c := by
  rw [S2921Q_eq_regionVolume]
  unfold S2792RegionVolume
  ring

theorem S2940_Q_le_twoS_add (a b c : Nat) (habc : IsABCTriple a b c) :
    S2921Q a b c ≤ 2 * S2921S a b c + 2 * S2792D := by
  have hreg := S2792_regionVolume_le_weight_add_D a b c habc
  have hw := S2940_S_ge_arithmeticWeight a b c habc
  rw [S2940_Q_eq_two_region]
  nlinarith

/-!
## S2940 conclusions

Proved:
* S2921S a b c >= log (natRadical (a*b*c)) = arithmeticWeight(abc point).
* S2921Q a b c = 2 * S2792RegionVolume a b c.
* S2921Q a b c <= 2 * S2921S a b c + 2 * S2792D.

Not proved / not available:
* S2921Q a b c vs log c.  S2921S only controls log of the radical of a*b*c;
  for a primitive triple c can have high prime powers, so log c can exceed
  log rad(a*b*c) by an unbounded amount.  There is no unconditional inequality
  in either direction between S2921Q and log c in the tree.
* S2921S a b c <= log (natRadical (a*b*c)) is false in general: the support
  ideal norm is at least the radical and can be larger (field places and
  support multiplicities are not the same as rational primes).
-/

#check S2940_prod_supportIndex
#check S2940_S_ge_log_rad
#check S2940_S_ge_arithmeticWeight
#check S2940_Q_eq_two_region
#check S2940_Q_le_twoS_add
#print axioms S2940_S_ge_log_rad
#print axioms S2940_Q_le_twoS_add

end LeanFormal.IUT.XiFPaper.S2940NuclearComparison
end
