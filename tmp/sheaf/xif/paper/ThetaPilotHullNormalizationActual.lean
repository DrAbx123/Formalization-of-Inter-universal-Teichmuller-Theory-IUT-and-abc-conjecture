import tmp.sheaf.xif.paper.ThetaPilotHullProcessionActual
import LeanFormal.IUT.Foundations.Arithmetic.FiniteLabels

/-! # Theta-pilot hull normalization: F_l^x versus ThetaPilotCarrier stages

The actual Theta-pilot hull procession candidate of ThetaPilotHullProcessionActual
is indexed by the project's ThetaPilotCarrier = Fin (lStar l.value + 1).

The paper's procession normalization in Theorem 3.11/Corollary 3.12 is over
the label product indexed by F_l^x (the units of F_l), not by ThetaPilotCarrier
stages.  This file constructs the actual F_l^x uniform-average object and proves
the cardinal obstruction to identifying the two index types: no arbitrary
Fintype equivalence is used.

No inequality is asserted.  No sorry, axiom, True, or PUnit is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ThetaPilotHullNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual F_l^x index type: the units of ZMod l. -/
abbrev FlUnits : Type := (ZMod l.value)ˣ

/-- The actual cardinality of the ThetaPilotCarrier stages. -/
theorem thetaPilotCarrier_card :
    Fintype.card (ThetaPilotCarrier l) = lStar l.value + 1 := rfl

/-- The actual cardinality of F_l^x. -/
theorem flUnits_card : Fintype.card (FlUnits (l := l)) = l.value - 1 := by
  change Fintype.card ((ZMod l.value)ˣ) = l.value - 1
  rw [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : Nat.Prime l.value)]

/-- The ThetaPilotCarrier and F_l^x cardinalities differ for every prime l >= 5. -/
theorem thetaPilotCarrier_card_ne_flUnits_card :
    Fintype.card (ThetaPilotCarrier l) ≠ Fintype.card (FlUnits (l := l)) := by
  rw [thetaPilotCarrier_card, flUnits_card]
  have hl5 : 5 ≤ l.value := l.ge_five
  have hodd : Odd l.value :=
    (Fact.out : Nat.Prime l.value).odd_of_ne_two (by omega)
  have hstar := two_mul_lStar_add_one l.value hodd
  omega

/-- Exact index obstruction: there is no actual equivalence between the
ThetaPilotCarrier stages and F_l^x. -/
theorem not_nonempty_thetaPilotCarrier_equiv_flUnits :
    ¬ Nonempty (ThetaPilotCarrier l ≃ FlUnits (l := l)) := by
  rintro ⟨e⟩
  exact thetaPilotCarrier_card_ne_flUnits_card
    (Fintype.card_congr e)

/-- The actual uniform average over the paper label set F_l^x. -/
noncomputable def flUnitsUniformAverage (f : FlUnits (l := l) -> Real) : Real :=
  (Fintype.card (FlUnits (l := l)) : Real)⁻¹ *
    ∑ x : FlUnits (l := l), f x

/-- The F_l^x average weight is exactly one over its cardinality. -/
theorem flUnitsUniformAverage_const (c : Real) :
    flUnitsUniformAverage (l := l) (fun _ => c) = c := by
  unfold flUnitsUniformAverage
  have hcard : (Fintype.card (FlUnits (l := l)) : Real) ≠ 0 := by
    have hpos : 0 < Fintype.card (FlUnits (l := l)) := Fintype.card_pos_iff.mpr
      ⟨(1 : FlUnits (l := l))⟩
    exact_mod_cast (ne_of_gt hpos)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  field_simp [hcard]

/-- Exact normalization obstruction: the ThetaPilotCarrier procession average
cannot be transported to an F_l^x average by a cardinality equivalence; a new
actual source map/index construction is required. -/
def ThetaPilotCarrierFlUnitsIndexObstruction : Prop :=
  ¬ Nonempty (ThetaPilotCarrier l ≃ FlUnits (l := l))

theorem thetaPilotCarrierFlUnitsIndexObstruction_holds :
    ThetaPilotCarrierFlUnitsIndexObstruction (l := l) :=
  not_nonempty_thetaPilotCarrier_equiv_flUnits

end LeanFormal.IUT.XiFPaper.ThetaPilotHullNormalizationActual

end
