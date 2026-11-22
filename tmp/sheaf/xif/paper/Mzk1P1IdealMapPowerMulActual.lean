/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1CountIdealMapPowerActual
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic

/-! # P1: multiplicativity of IdealMapPowerStatement (towards general I) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerMulActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {k : Type} [Field k] [NumberField k]

/-- Multiplicative step: statements for I and J give the statement for I*J, provided the
`Associates` counts add. -/
theorem idealMapPowerStatement_mul (v : NumberField.FinitePlace k)
    (I J : Ideal (NumberField.RingOfIntegers k)) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hIJ : I * J ≠ 0)
    (hmapI : IdealMapPowerStatement (k := k) I hI v)
    (hmapJ : IdealMapPowerStatement (k := k) J hJ v)
    (hcount : (Associates.mk (underlyingPrime v).asIdeal).count
        (Associates.mk (I * J)).factors =
      (Associates.mk (underlyingPrime v).asIdeal).count (Associates.mk I).factors +
        (Associates.mk (underlyingPrime v).asIdeal).count (Associates.mk J).factors) :
    IdealMapPowerStatement (k := k) (I * J) hIJ v := by
  unfold IdealMapPowerStatement at hmapI hmapJ ⊢
  rw [Ideal.map_mul, hmapI, hmapJ, hcount, pow_add]

def idealMapPowerMulRows : List (String × String × String) :=
  [ ("idealMapPowerStatement_mul", "map-statement multiplicative step", "PROVED (conditional on count add)"),
    ("idealMapPowerStatement_mul_count_hyp", "count additivity supplied as hypothesis", "GAP (Mathlib count_mul coercion)") ]

theorem idealMapPowerMulRows_length : idealMapPowerMulRows.length = 2 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerMulActual

end