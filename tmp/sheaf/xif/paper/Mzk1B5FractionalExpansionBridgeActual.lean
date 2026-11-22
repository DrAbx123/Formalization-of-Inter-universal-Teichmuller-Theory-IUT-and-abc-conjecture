/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1B5FractionalAbsNormFormulaActual
import tmp.sheaf.xif.paper.Mzk1B5FractionalCountNumDenActual
import tmp.sheaf.xif.paper.Mzk1B5RelativeDetLogExpansionActual
import tmp.sheaf.xif.paper.Mzk1B5CountLocalValuationBridgeActual
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic
import tmp.sheaf.xif.paper.DeterminantLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.sheaf.xif.paper.Mzk1P1LocalGeneratorFromIsPrincipalActual
import tmp.sheaf.xif.paper.Mzk1P1LocalizedFractionalIdealActual
import tmp.sheaf.xif.paper.Mzk1P1PlaceVolumeSignActual
import tmp.sheaf.xif.paper.Mzk1Ob33B5AssemblyActual
import tmp.sheaf.xif.paper.Mzk1B5AssemblyNoHproductAttemptActual

/-!
# B5: replace FractionalLogVolumeExpansion by the qpilot fractional formula
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1B5FractionalExpansionBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1B5FractionalAbsNormFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1B5FractionalCountNumDenActual
open LeanFormal.IUT.XiFPaper.Mzk1B5RelativeDetLogExpansionActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual

variable {k : Type} [Field k] [NumberField k]

theorem fractionalLogVolumeExpansion_of_qpilot
    (hsumH : ∀ (I : LineBundle (k := k)) (_ : I ≠ 0),
      Function.HasFiniteSupport (fun w : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers k) =>
        ((Associates.mk w.asIdeal).count (Associates.mk I.num).factors : Real) *
          Real.log ((Ideal.absNorm w.asIdeal : Nat) : Real)))
    (hsumO : ∀ (I : LineBundle (k := k)) (_ : I ≠ 0),
      Function.HasFiniteSupport (fun w : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers k) =>
        ((Associates.mk w.asIdeal).count
          (Associates.mk (Ideal.span {(I.den : NumberField.RingOfIntegers k)})).factors : Real) *
          Real.log ((Ideal.absNorm w.asIdeal : Nat) : Real))) :
    FractionalLogVolumeExpansion (k := k) := by
  intro I hI
  have hq := Mzk1B5FractionalAbsNormFormulaActual.log_absNorm_fractional_eq_sum_diff k I hI
  have hdet : globalLogVolume (k := k) I = Real.log (FractionalIdeal.absNorm I : Real) := rfl
  rw [hdet, hq]
  rw [← finsum_sub_distrib (hsumH I hI) (hsumO I hI)]
  rw [show (∑ᶠ v : NumberField.FinitePlace k,
        (countExponent (k := k) v I : Real) * Real.log (residueNormBase v))
      = ∑ᶠ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k),
          (FractionalIdeal.count k w I : Real) *
            Real.log ((Ideal.absNorm w.asIdeal : Nat) : Real) from by
    rw [← finsum_comp_equiv (e := NumberField.FinitePlace.equivHeightOneSpectrum (K := k))]
    apply finsum_congr
    intro v
    simp [countExponent, residueNormBase]
  ]
  apply finsum_congr
  intro w
  rw [count_eq_count_num_sub_count_den k I hI w]
  push_cast
  ring

def fractionalExpansionBridgeRows : List (String × String × String) :=
  [ ("FractionalLogVolumeExpansion", "derived from qpilot fractional formula", "PROVED (conditional on finite support)"),
    ("hsumH / hsumO", "Function.HasFiniteSupport of the num/den count-weighted sums", "GAP (to close via Ideal.finite_factors)"),
    ("count_eq_count_num_sub_count_den", "qpilot green", "GREEN"),
    ("log_absNorm_fractional_eq_sum_diff", "qpilot green", "GREEN") ]

theorem fractionalExpansionBridgeRows_length : fractionalExpansionBridgeRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1B5FractionalExpansionBridgeActual

end