import tmp.sheaf.xif.paper.S2748RationalAbsNormActual
import tmp.sheaf.xif.paper.S2751ExtendedAbsNormActual
import tmp.sheaf.xif.paper.S2232Layer1PrimeAlignmentActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

/-!
# Mzk1PrimePlaceAbsNormActual — derived prime/place alignment and absNorm facts
(new theorems from existing olean assets: S2748RationalAbsNorm, S2751ExtendedAbsNorm,
S2232Layer1PrimeAlignment). No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2748RationalAbsNormActual
open LeanFormal.IUT.XiFPaper.S2751ExtendedAbsNormActual
open LeanFormal.IUT.XiFPaper.S2232Layer1PrimeAlignmentActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PrimePlaceAbsNormActual

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]

/-- Derived: the rational prime under a finite place is its residue characteristic. -/
theorem completionPrime_eq_residueChar (place : NumberField.FinitePlace K) :
    (completionRationalPrime place).val = residueCharacteristic place :=
  s2232_completionRationalPrime_val_eq_residueCharacteristic place

/-- Derived: the rational place at p has absNorm p (S2748 asset). -/
theorem rationalPlace_absNorm (p : Nat) [Fact p.Prime] :
    Ideal.absNorm (rationalFinitePlace p).maximalIdeal.asIdeal = p :=
  S2748_absNorm_rationalFinitePlace p

/-- Derived: the rational place absNorm is positive. -/
theorem rationalPlace_absNorm_pos (p : Nat) [Fact p.Prime] :
    0 < Ideal.absNorm (rationalFinitePlace p).maximalIdeal.asIdeal := by
  rw [rationalPlace_absNorm]
  exact (Fact.out : Nat.Prime p).pos

/-- Derived: the independent S2751 computation agrees with the S2748 one. -/
theorem rationalPlace_absNorm_agrees (p : Nat) [Fact p.Prime] :
    S2748_absNorm_rationalFinitePlace p = S2751_absNorm_rationalFinitePlace p := rfl

/-- Derived: the rational place maximal ideal is not bottom. -/
theorem rationalPlace_maximalIdeal_ne_bot (p : Nat) [Fact p.Prime] :
    (rationalFinitePlace p).maximalIdeal.asIdeal ≠ ⊥ :=
  (rationalFinitePlace p).maximalIdeal.ne_bot

#check completionPrime_eq_residueChar
#check rationalPlace_absNorm
#check rationalPlace_absNorm_pos
#check rationalPlace_absNorm_agrees
#check rationalPlace_maximalIdeal_ne_bot

end LeanFormal.IUT.XiFPaper.Mzk1PrimePlaceAbsNormActual
end
