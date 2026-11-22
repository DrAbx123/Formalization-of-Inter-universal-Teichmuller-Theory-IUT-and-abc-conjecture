/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import tmp.external.ported.flt.FLT.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic

/-! # Route B #3 step 3: principal generator of the localized line (count + uniformizer)

Attempt: construct the generator `x = (pi : K_v)^e` with `e = FractionalIdeal.count k v I`
and `pi` the uniformizer from `adicCompletion.exists_uniformizer K v`, and prove
`localizedLine I v = span O_v {x}`.

Available green API used here:
* `FractionalIdeal.count` (Factorization.lean:309) with multiplicative laws;
* `adicCompletion.exists_uniformizer` (ported FLT AdicValuation:472);
* `localizedLine` (DeterminantLogVolumeActual:108).

Precise Mathlib gaps (recorded, not assumed):
1. no lemma `localizedLine I v = span O_v (FractionalIdeal.map ...)`;
2. no lemma linking `FractionalIdeal.count` to a principal span at the localization
   (`Factorization.lean` only provides the multiplicative API).
Hence the span identity is kept as the explicit named input `CountLocalizationBridge`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual

open LeanFormal.IUT.PaperDeterminantLogVolume
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
open scoped Multiplicative

variable {k : Type} [Field k] [NumberField k]

/-- The `v`-adic exponent of a fractional ideal (Mathlib `FractionalIdeal.count`). -/
noncomputable def countExponent (v : NumberField.FinitePlace k)
    (I : LineBundle (k := k)) : Int :=
  FractionalIdeal.count k v.maximalIdeal I

/-- Additivity of the exponent (re-export of `FractionalIdeal.count_mul`). -/
theorem countExponent_mul (v : NumberField.FinitePlace k)
    (I J : LineBundle (k := k)) (hI : I ≠ 0) (hJ : J ≠ 0) :
    countExponent (k := k) v (I * J) =
      countExponent (k := k) v I + countExponent (k := k) v J :=
  FractionalIdeal.count_mul k v.maximalIdeal hI hJ

/-- The unit exponent is zero (re-export of `FractionalIdeal.count_one`). -/
theorem countExponent_one (v : NumberField.FinitePlace k) :
    countExponent (k := k) v (1 : LineBundle (k := k)) = 0 :=
  FractionalIdeal.count_one k v.maximalIdeal

/-- A uniformizer of the completed valuation ring exists (FLT ported API). -/
theorem exists_uniformizer_local (v : NumberField.FinitePlace k) :
    ∃ pi : LocalRing (k := k) v,
      Valued.v (pi : LocalField (k := k) v) = Multiplicative.ofAdd (-1 : Int) :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer
    (A := NumberField.RingOfIntegers k) (K := k) v.maximalIdeal

/-- **Named bridge (precise Mathlib gap)**: the count exponent gives a principal
generator of the localized line. -/
def CountLocalizationBridge : Prop :=
  ∀ (I : LineBundle (k := k)) (_ : I ≠ 0) (v : NumberField.FinitePlace k),
    ∃ (e : Int) (pi : LocalRing (k := k) v),
      Valued.v (pi : LocalField (k := k) v) = Multiplicative.ofAdd (-1 : Int)
      ∧ localizedLine (k := k) I v =
        Submodule.span (LocalRing (k := k) v)
          {((pi : LocalField (k := k) v) ^ e)}

/-- Under the named bridge, the principal generator exists for every nonzero line bundle
and every finite place. -/
theorem localPrincipalGenerator_of_bridge
    (h : CountLocalizationBridge (k := k)) :
    ∀ (I : LineBundle (k := k)) (_ : I ≠ 0) (v : NumberField.FinitePlace k),
      LocalPrincipalGenerator (k := k) I v := by
  intro I hI v
  obtain ⟨e, pi, _hpi, hspan⟩ := h I hI v
  exact ⟨⟨((pi : LocalField (k := k) v) ^ e), hspan⟩⟩

def principalGeneratorRows : List (String × String × String) :=
  [ ("countExponent", "FractionalIdeal.count k v I", "GREEN (Factorization.lean:309)"),
    ("countExponent_mul/one", "multiplicative laws re-exported", "GREEN"),
    ("exists_uniformizer_local", "adicCompletion.exists_uniformizer", "GREEN (FLT AdicValuation:472)"),
    ("CountLocalizationBridge", "count exponent -> principal span of localizedLine", "GAP (named input)"),
    ("gap 1", "no localizedLine = span O_v (FractionalIdeal.map ...) lemma", "MATHLIB GAP"),
    ("gap 2", "no count -> principal-span lemma in Factorization.lean", "MATHLIB GAP"),
    ("localPrincipalGenerator_of_bridge", "bridge => LocalPrincipalGenerator", "PROVED (conditional)") ]

theorem principalGeneratorRows_length : principalGeneratorRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual

end