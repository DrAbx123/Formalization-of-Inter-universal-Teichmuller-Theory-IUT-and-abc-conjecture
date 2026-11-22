/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual
import tmp.sheaf.xif.paper.S2701GaussianPrimeIdealsActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol
import Mathlib.Tactic

/-! # A1104: qPilotIdeal = (10805) and log-volume

| field | value |
|---|---|---|
| Status | PARTIAL: the 5-factorization is imported (`gaussianFieldFive_ideal_factorization`); the 2161-factorization and qPilotIdeal=(10805) are attempted; the base log-volume `2 log 10805` is attempted from `qPilotFractional_absNorm`. |
| Source | `S2701GaussianPrimeIdealsActual` (`gaussianInt2161_ideal_factorization`, `gaussianField2161Plus/Minus`), `Example36GaussianSplitPlaceArithmetic:378` (`gaussianFieldFive_ideal_factorization`), `S2735` (`qPilotIdeal`, `qPilotFractional_absNorm`), `S2736` (`S2736QPilotLineBundleLogVolume`) |
| GAP | No existing `gaussianField2161_ideal_factorization`; it is derived here from `gaussianInt2161_ideal_factorization` + the `comap/map` definitions. The log-volume base needs `qPilotLineBundleExtended 1 = qPilotLineBundle` and `Real.log` arithmetic. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotPrincipalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2701GaussianPrimeIdealsActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}

/-- Factorization of (2161) in the Gaussian ring of integers, transported from
the Gaussian-integer factorization. -/
theorem gaussianField2161_ideal_factorization :
    Ideal.span {(2161 : gaussianRingOfIntegers)} =
      gaussianField2161Plus * gaussianField2161Minus := by
  rw [gaussianField2161Plus_eq_map, gaussianField2161Minus_eq_map,
    ← Ideal.map_mul, ← gaussianInt2161_ideal_factorization, Ideal.map_span]
  have h : gaussianIntEquivRingOfIntegers.toRingHom (2161 : GaussianInt) =
      (2161 : gaussianRingOfIntegers) := map_natCast _ _
  rw [Set.image_singleton, h]

/-- `qPilotIdeal l = (10805)` as an ideal of the Gaussian ring of integers. -/
theorem qPilotIdeal_eq_span_10805 :
    qPilotIdeal l = Ideal.span {(10805 : gaussianRingOfIntegers)} := by
  rw [qPilotIdeal_factorization]
  calc
    gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus *
        gaussianField2161Plus * gaussianField2161Minus =
      (gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus) *
        (gaussianField2161Plus * gaussianField2161Minus) := by ac_rfl
    _ = Ideal.span {(5 : gaussianRingOfIntegers)} *
        Ideal.span {(2161 : gaussianRingOfIntegers)} := by
      rw [← gaussianFieldFive_ideal_factorization,
        ← gaussianField2161_ideal_factorization]
    _ = Ideal.span {(5 * 2161 : gaussianRingOfIntegers)} := by
      rw [Ideal.span_singleton_mul_span_singleton]
    _ = Ideal.span {(10805 : gaussianRingOfIntegers)} := by norm_num

/-- The q-pilot fractional ideal has norm `10805^2`. -/
theorem qPilotFractional_absNorm_eq_10805_sq :
    FractionalIdeal.absNorm (qPilotLineBundle (l := l)) = (10805 ^ 2 : ℚ) := by
  rw [qPilotFractional_absNorm]
  norm_num

/-- Base log-volume of the q-pilot line bundle: `log(10805^2) = 2 log 10805`. -/
theorem S2736_base_logVolume_eq :
    S2736QPilotLineBundleLogVolume (l := l) (1 : Ideal (S2735O l)) =
      2 * Real.log (10805 : Real) := by
  rw [S2736QPilotLineBundleLogVolume]
  have h1 : qPilotLineBundleExtended (l := l) (1 : Ideal (S2735O l)) =
      qPilotLineBundle (l := l) := by
    unfold qPilotLineBundleExtended qPilotIdealExtended qPilotLineBundle
    simp
  rw [h1, qPilotFractional_absNorm_eq_10805_sq]
  rw [show ((10805 ^ 2 : ℚ) : Real) = (10805 : Real) ^ 2 by norm_num]
  rw [Real.log_pow]
  norm_num

def rows : List (String × String × String) :=
  [ ("gaussianField2161_ideal_factorization", "(2161)=P2161+*P2161-", "ATTEMPT"),
    ("qPilotIdeal_eq_span_10805", "qPilotIdeal=(10805)", "ATTEMPT"),
    ("qPilotFractional_absNorm_eq_10805_sq", "absNorm=10805^2", "PROVED from qPilotFractional_absNorm"),
    ("S2736_base_logVolume_eq", "logVolume(1)=2 log10805", "ATTEMPT") ]

theorem rows_length : rows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1QPilotPrincipalActual

end