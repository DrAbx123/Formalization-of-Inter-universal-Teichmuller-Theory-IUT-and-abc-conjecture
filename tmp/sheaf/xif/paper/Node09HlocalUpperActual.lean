import tmp.sheaf.xif.paper.Node09HresidueDegreeActual
import tmp.sheaf.xif.paper.Node09HmultReductionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime
import tmp.sheaf.n8.closure.NativeBadLiftActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.XiFPaper.ResidueCardBridgeAttempt
open LeanFormal.IUT.XiFPaper.Node09AbsNormRatActual
open LeanFormal.IUT.XiFPaper.Node09HresidueDegreeActual

namespace LeanFormal.IUT.XiFPaper.Node09HlocalUpperActual

variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

/-- Upper-place version: for a place of any number field over Q, the relative
local residue degree over Q equals actualFn. -/
theorem localResidueDegree_rat_eq_actualFn_upper
    (place : FinitePlaceAtPrime F p) :
    localResidueDegree (k := ℚ) place.val = actualFn place := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcardNat : logShellResidueCard (K := NormalizedCompletion place.val) =
      p ^ actualFn place := by
    simpa [place.property] using (actualFn_spec place).2
  have hlowprime : (completionRationalPrime (comap (k := ℚ) place.val)).val = p := by
    rw [LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime_comap (k := ℚ) place.val]
    exact place.property
  have hlowR : residueNormBase (comap (k := ℚ) place.val) = (p : ℝ) := by
    rw [residueNormBase_rat_eq (comap (k := ℚ) place.val), hlowprime]
  have h := residueNormBase_eq_lower_pow (k := ℚ) place.val
  rw [hlowR] at h
  have hcardR : (logShellResidueCard (K := NormalizedCompletion place.val) : ℝ) =
      (p : ℝ) ^ actualFn place := by
    rw [hcardNat]
    push_cast
    rfl
  have hpair : (p : ℝ) ^ localResidueDegree (k := ℚ) place.val =
      (p : ℝ) ^ actualFn place := by
    calc (p : ℝ) ^ localResidueDegree (k := ℚ) place.val
        = residueNormBase place.val := h.symm
      _ = (logShellResidueCard (K := NormalizedCompletion place.val) : ℝ) :=
          (logShellResidueCard_eq_residueNormBase place.val).symm
      _ = (p : ℝ) ^ actualFn place := hcardR
  have hnat : p ^ localResidueDegree (k := ℚ) place.val = p ^ actualFn place := by
    exact_mod_cast hpair
  exact Nat.pow_right_injective hp hnat

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- hlocal at the actual upper bad lift, once Fmod = Q and the lift agrees with
the chosen finite prime place. -/
theorem hlocal_upper_of_place_eq
    (b : FinitePlaceAtPrime X.S.arithmetic.F p → Bad (nativePlaceSelection X.S))
    (i : FinitePlaceAtPrime X.S.arithmetic.F p)
    (hplace : (nativeBadLift X.S).lift (b i) = i.val)
    (hk : (localResidueDegree (k := X.S.arithmetic.Fmod)
        ((nativeBadLift X.S).lift (b i)) : ℝ) =
      (localResidueDegree (k := ℚ) i.val : ℝ))
    (hlocal_rat : (localResidueDegree (k := ℚ) i.val : ℝ) = (actualFn i : ℝ)) :
    (localResidueDegree (k := X.S.arithmetic.Fmod)
        ((nativeBadLift X.S).lift (b i)) : ℝ) = (actualFn i : ℝ) := by
  rw [hplace] at hk ⊢
  rw [hk, hlocal_rat]

end LeanFormal.IUT.XiFPaper.Node09HlocalUpperActual
