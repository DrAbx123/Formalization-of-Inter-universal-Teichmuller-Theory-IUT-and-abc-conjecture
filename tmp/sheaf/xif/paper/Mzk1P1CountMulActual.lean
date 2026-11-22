/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic

/-! # P1: powers/inverses of the count exponent (real proofs) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1CountMulActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual

variable {k : Type} [Field k] [NumberField k]

theorem countExponent_pow (v : NumberField.FinitePlace k)
    (I : LineBundle (k := k)) (n : Nat) :
    countExponent (k := k) v (I ^ n) = (n : Int) * countExponent (k := k) v I := by
  unfold countExponent
  rw [FractionalIdeal.count_pow]

theorem countExponent_zpow (v : NumberField.FinitePlace k)
    (I : LineBundle (k := k)) (n : Int) :
    countExponent (k := k) v (I ^ n) = n * countExponent (k := k) v I := by
  unfold countExponent
  rw [FractionalIdeal.count_zpow]

theorem countExponent_inv (v : NumberField.FinitePlace k)
    (I : LineBundle (k := k)) :
    countExponent (k := k) v I⁻¹ = -countExponent (k := k) v I := by
  unfold countExponent
  rw [FractionalIdeal.count_inv]

theorem countExponent_self (v : NumberField.FinitePlace k) :
    countExponent (k := k) v ((v.maximalIdeal.asIdeal : LineBundle (k := k))) = 1 := by
  unfold countExponent
  exact FractionalIdeal.count_self k v.maximalIdeal

theorem countExponent_pow_self (v : NumberField.FinitePlace k) (n : Nat) :
    countExponent (k := k) v ((v.maximalIdeal.asIdeal : LineBundle (k := k)) ^ n) =
      (n : Int) := by
  unfold countExponent
  exact FractionalIdeal.count_pow_self k v.maximalIdeal n

def countMulRows : List (String × String × String) :=
  [ ("countExponent_pow", "count(I^n) = n*count(I)", "PROVED"),
    ("countExponent_zpow", "count(I^z) = z*count(I)", "PROVED"),
    ("countExponent_inv", "count(I^-1) = -count(I)", "PROVED"),
    ("countExponent_self", "count(p) = 1", "PROVED"),
    ("countExponent_pow_self", "count(p^n) = n", "PROVED") ]

theorem countMulRows_length : countMulRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1CountMulActual

end
