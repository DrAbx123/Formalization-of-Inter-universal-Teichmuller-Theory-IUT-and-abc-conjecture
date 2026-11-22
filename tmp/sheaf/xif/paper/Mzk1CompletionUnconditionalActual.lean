/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import Mathlib.Tactic
import Mathlib.Algebra.Group.TypeTags.Basic

/-! # A939 hull: unconditional completion root obstruction -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1CompletionUnconditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open scoped NormedField

variable {K : Type*} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

noncomputable instance commonPrimeCompletionValued :
    Valued (CommonPrimeCompletion (K := K) place) (WithZero (Multiplicative Int)) :=
  inferInstanceAs (Valued (Completion place.val) (WithZero (Multiplicative Int)))

/-- Additive exponent of a value-group element (0 for 0). -/
def valExpVal (z : WithZero (Multiplicative Int)) : Int :=
  if hz : z = 0 then 0 else -Multiplicative.toAdd (WithZero.unzero hz)

theorem valExpVal_mul {a b : WithZero (Multiplicative Int)} (ha : a ≠ 0) (hb : b ≠ 0) :
    valExpVal (a * b) = valExpVal a + valExpVal b := by
  unfold valExpVal
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  rw [dif_neg ha, dif_neg hb, dif_neg hab, WithZero.unzero_mul hab]
  change -Multiplicative.toAdd (WithZero.unzero ha * WithZero.unzero hb) =
    -Multiplicative.toAdd (WithZero.unzero ha) + -Multiplicative.toAdd (WithZero.unzero hb)
  rw [show Multiplicative.toAdd (WithZero.unzero ha * WithZero.unzero hb) =
      Multiplicative.toAdd (WithZero.unzero ha) + Multiplicative.toAdd (WithZero.unzero hb) from rfl]
  ring

def unitValExp (u : (CommonPrimeCompletion (K := K) place)ˣ) : Int :=
  valExpVal (Valued.v (u : CommonPrimeCompletion (K := K) place))

theorem unitValExp_one : unitValExp place (1 : (CommonPrimeCompletion (K := K) place)ˣ) = 0 := by
  unfold unitValExp valExpVal
  rw [Units.val_one, map_one]
  rfl

theorem unitValExp_mul (u v : (CommonPrimeCompletion (K := K) place)ˣ) :
    unitValExp place (u * v) = unitValExp place u + unitValExp place v := by
  unfold unitValExp
  rw [Units.val_mul, map_mul]
  apply valExpVal_mul
  · exact (Valued.v).ne_zero_iff.mpr (Units.ne_zero u)
  · exact (Valued.v).ne_zero_iff.mpr (Units.ne_zero v)

theorem unitValExp_pow (u : (CommonPrimeCompletion (K := K) place)ˣ) (n : Nat) :
    unitValExp place (u ^ n) = n * unitValExp place u := by
  induction n with
  | zero => simp [unitValExp_one]
  | succ n ih =>
      rw [pow_succ, unitValExp_mul, ih]
      push_cast
      ring

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable (placeI : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (q : FinitePlaceQCandidate placeI.val)

theorem unitValExp_candidateUnits :
    unitValExp placeI (candidateUnits placeI q) = q.exponent := by
  unfold unitValExp valExpVal candidateUnits FinitePlaceQCandidate.exponent
  rw [Units.val_mk0]
  have hne : Valued.v (q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) placeI) ≠ 0 := by
    exact (Valued.v).ne_zero_iff.mpr q.q_ne_zero
  split_ifs with h
  · exact (hne h).elim
  · rfl

theorem no_natRootSystem_of_valExp_pos (u : (CommonPrimeCompletion (K := K) place)ˣ)
    (hpos : 0 < unitValExp place u) : ¬ Nonempty (NatRootSystem u) := by
  rintro ⟨R⟩
  let e : Int := unitValExp place u
  have he : 0 < e := hpos
  let n : Nat := e.toNat + 1
  have hn : (n : Int) = e + 1 := by
    dsimp [n]
    have h0 : 0 ≤ e := le_of_lt he
    omega
  have hn0 : n ≠ 0 := by omega
  have hpow := R.pow_self n hn0
  have h2 := unitValExp_pow place (R.root n) n
  rw [hpow] at h2
  have hdiv : (n : Int) * unitValExp place (R.root n) = e := by
    rw [← h2]
  let k : Int := unitValExp place (R.root n)
  have hkpos : 0 < k := by
    by_contra hk
    have hk0 : k ≤ 0 := le_of_not_gt hk
    nlinarith [hdiv, hn, he, hk0]
  have hk1 : 1 ≤ k := by omega
  nlinarith [hdiv, hn, he, hk1]

theorem completionFirstFieldObstruction_empty :
    ¬ completionFirstFieldObstruction (I := I) placeI := by
  unfold completionFirstFieldObstruction
  exact no_natRootSystem_of_valExp_pos placeI
    (candidateUnits placeI (concreteQCandidate (I := I) placeI)) (by
      rw [unitValExp_candidateUnits]
      exact (concreteQCandidate (I := I) placeI).exponent_pos)

theorem actualCompletionRootBlock_empty :
    ¬ Nonempty (CompletionRootBlock (I := I) (actualSourcePilotRegionCore (I := I) placeI)) := by
  rw [actualCompletionRootBlock_nonempty_iff]
  exact completionFirstFieldObstruction_empty (I := I) placeI

theorem oldSourcePilotWithActualCore_empty :
    ¬ OldSourcePilotWithActualCore (I := I) placeI := by
  rw [oldSourcePilotWithActualCore_nonempty_iff]
  exact completionFirstFieldObstruction_empty (I := I) placeI

#print axioms no_natRootSystem_of_valExp_pos
#print axioms completionFirstFieldObstruction_empty
#print axioms actualCompletionRootBlock_empty
#print axioms oldSourcePilotWithActualCore_empty

end LeanFormal.IUT.XiFPaper.Mzk1CompletionUnconditionalActual

end