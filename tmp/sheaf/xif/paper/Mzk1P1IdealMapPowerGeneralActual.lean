/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountProofActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerGeneralActual
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open LeanFormal.IUT.NumberFieldFinitePlace
variable {k : Type} [Field k] [NumberField k]
theorem ideal_map_pow_general
    (I : Ideal (NumberField.RingOfIntegers k)) (v : NumberField.FinitePlace k)
    (n : Nat) :
    Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
      (I ^ n) =
      (Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
        I) ^ n :=
  Ideal.map_pow _ _ _
theorem idealMapPowerStatement_of_count_map
    (I : Ideal (NumberField.RingOfIntegers k)) (hI : I ≠ 0)
    (v : NumberField.FinitePlace k) (n : Nat)
    (hcount : (Associates.mk (underlyingPrime v).asIdeal).count
        (Associates.mk I).factors = n)
    (hmap : Ideal.map (algebraMap (NumberField.RingOfIntegers k)
        (LocalRing (k := k) v)) I = (completionIdealOf (k := k) v) ^ n) :
    IdealMapPowerStatement (k := k) I hI v := by
  unfold IdealMapPowerStatement
  rw [hcount, hmap]
end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerGeneralActual
