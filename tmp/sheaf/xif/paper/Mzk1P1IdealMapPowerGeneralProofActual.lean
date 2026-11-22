/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P1IdealLocalizedCountProofActual
import tmp.sheaf.xif.paper.Mzk1P1IdealMapFactorActual
import tmp.sheaf.xif.paper.Mzk1P1IdealMapFinprodExpandActual
import Mathlib.Tactic

/-! # P1: general IdealMapPowerStatement (all nonzero ideals) -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerGeneralProofActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealLocalizedCountProofActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapFactorActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapFinprodExpandActual
open LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapFinsetProdActual
open IsDedekindDomain

variable {k : Type} [Field k] [NumberField k]

/-- General `IdealMapPowerStatement`: `Ideal.map I = completionIdeal^count` for every
nonzero ideal `I`. The proof expands `I` into its finite-support prime-power product,
collapses the product via `prod_eq_single`, and evaluates the two factor types. -/
theorem idealMapPowerStatement_general (I : Ideal (NumberField.RingOfIntegers k))
    (hI : I ≠ 0) (v : NumberField.FinitePlace k) :
    IdealMapPowerStatement (k := k) I hI v := by
  unfold IdealMapPowerStatement
  rw [ideal_map_eq_finset_prod_map (f := algebraMap (NumberField.RingOfIntegers k)
    (LocalRing (k := k) v)) hI]
  classical
  have hf := Ideal.hasFiniteMulSupport (R := NumberField.RingOfIntegers k) hI
  have hsingle :
      ∏ i ∈ hf.toFinset,
        Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
          (i.maxPowDividing I) =
      Ideal.map (algebraMap (NumberField.RingOfIntegers k) (LocalRing (k := k) v))
        ((underlyingPrime v).maxPowDividing I) := by
    refine Finset.prod_eq_single (underlyingPrime v) ?_ ?_
    · intro b hb hne
      rw [map_maxPowDividing_ne_self (k := k) v b hne I, Ideal.one_eq_top]
    · intro hv
      have hval : (underlyingPrime v).maxPowDividing I = 1 := by
        by_contra hne
        exact hv (hf.mem_toFinset.mpr hne)
      rw [hval, Ideal.one_eq_top, Ideal.map_top, Ideal.one_eq_top]
  rw [hsingle]
  simpa [Mzk1P1IdealLocalizedCountProofActual.completionIdealOf,
    Mzk1P1IdealMapCompletionIdealActual.completionIdealOf] using
    map_maxPowDividing_self (k := k) v I

def generalRows : List (String × String × String) :=
  [ ("idealMapPowerStatement_general", "general IdealMapPowerStatement (all nonzero I)", "PROVED") ]

theorem generalRows_length : generalRows.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P1IdealMapPowerGeneralProofActual

end