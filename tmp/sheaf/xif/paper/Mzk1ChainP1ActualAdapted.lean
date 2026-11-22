import tmp.sheaf.xif.paper.Mzk1P1CardinalityActual
import tmp.sheaf.xif.paper.Mzk1P1MeasureTransferStatementsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainP1ActualAdapted (adapted copy, A475 reuse) — P1 special-set + measure-transfer chain bundle

Chains EXIT0 P1 assets into one bundle: the finite special set {∞,0,1} with
membership and the three P1 measure-transfer statements.  The measure statements
remain named/hypothesis fields; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainP1ActualAdapted

open LeanFormal.IUT.XiFPaper.Mzk1P1CardinalityActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MeasureTransferStatementsActual

structure P1ChainBundle : Prop where
  finite : specialSet.Finite
  infty_mem : (none : Option ℂ) ∈ specialSet
  zero_mem : (some (0 : ℂ)) ∈ specialSet
  one_mem : (some (1 : ℂ)) ∈ specialSet
  maxDegNonIncrease : P1MaxDegNonIncrease
  strictDecrease : P1MeasureStrictDecrease
  finiteNonIncrease : FiniteMaxDegNonIncrease

theorem p1Chain_finite (B : P1ChainBundle) : specialSet.Finite :=
  B.finite

theorem p1Chain_members (B : P1ChainBundle) :
    (none : Option ℂ) ∈ specialSet ∧ (some (0 : ℂ)) ∈ specialSet ∧
      (some (1 : ℂ)) ∈ specialSet :=
  ⟨B.infty_mem, B.zero_mem, B.one_mem⟩

theorem p1Chain_measure (B : P1ChainBundle) : P1MaxDegNonIncrease :=
  B.maxDegNonIncrease

def p1ChainRows : List (String × String × String) :=
  [ ("bundle", "P1ChainBundle", "DEF (reuses EXIT0 P1 assets)"),
    ("special set", "p1Chain_finite / p1Chain_members", "PROVED (projection)"),
    ("measure", "p1Chain_measure", "PROVED (projection; statement remains named)"),
    ("scope", "statements only; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem p1ChainRows_length : p1ChainRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ChainP1ActualAdapted

end
