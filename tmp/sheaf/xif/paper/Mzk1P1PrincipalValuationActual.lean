/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic

/-! # P1: valuation of a principal ideal vs Associates count (statement) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1PrincipalValuationActual

open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume

variable {k : Type} [Field k] [NumberField k]

/-- Statement: the local valuation of the image of `a` is minus the `v`-count of the
principal ideal `span {a}`. -/
def PrincipalValuationStatement : Prop :=
  ∀ (a : NumberField.RingOfIntegers k) (_ : a ≠ 0) (v : NumberField.FinitePlace k),
    localValuation (k := k) v (algebraMap k (LocalField (k := k) v) a) =
      - (((Associates.mk v.maximalIdeal.asIdeal).count
          (Associates.mk (Ideal.span {a})).factors : Nat) : Int)

def principalValuationRows : List (String × String × String) :=
  [ ("PrincipalValuationStatement", "localValuation (algebraMap a) = -count_v(span{a})", "GAP (Associates.count <-> valuation API)"),
    ("missing Mathlib", "HeightOneSpectrum.intValuation_eq_multiplicity / count_ne_zero_iff_dvd + power decomposition", "GAP list") ]

theorem principalValuationRows_length : principalValuationRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1PrincipalValuationActual

end