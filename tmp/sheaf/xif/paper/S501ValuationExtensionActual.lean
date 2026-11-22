import tmp.sheaf.xif.paper.S495DvSmallValuationActual
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.ExtendToLocalization
/-! # S501: normalized valuation extension to finite etale field covers
Mathlib provides Valuation.HasExtension and extendToLocalization, but no
existence/uniqueness theorem for extending a normalized complete-DVR valuation
along a finite separable field extension, and no ramification normalization.
This file records the exact required data/theorems; it constructs a valuation
family only from an explicit witness.  No valuation is faked. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S501ValuationExtensionActual
open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S495DvSmallValuationActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual
universe u
variable (K : Type u) [Field K]
/-- A normalized Z-valued valuation on the base field K^×. -/
structure DvNormalizedBaseValuation where
  valuation : Kˣ →* Multiplicative ℤ
  valuation_surjective : Function.Surjective
    (fun x : Kˣ => Multiplicative.toAdd (valuation x))
/-- Compatibility of a cover valuation with the base normalized valuation. -/
structure DvNormalizedValuationExtension
    (vK : DvNormalizedBaseValuation K)
    (X : Example32SmallBase K)
    (V : DvCoverNormalizedValuationData K (coverField (K := K) X)) : Prop where
  extends_base : ∀ u : Kˣ,
    V.valuation (Units.map (algebraMap K (coverField (K := K) X)).toMonoidHom u) =
      vK.valuation u
/-- Explicit extension witness for every finite etale cover. -/
structure DvNormalizedValuationExtensionWitness
    (vK : DvNormalizedBaseValuation K) where
  extension : ∀ X : Example32SmallBase K,
    DvCoverNormalizedValuationData K (coverField (K := K) X)
  compatibility : ∀ X : Example32SmallBase K,
    DvNormalizedValuationExtension (K := K) vK X (extension X)
/-- Conditional existence statement from an explicit extension witness. -/
def DvSmallValuationExtensionExistsFrom
    (vK : DvNormalizedBaseValuation K) : Prop :=
  Nonempty (DvNormalizedValuationExtensionWitness (K := K) vK)
/-- The paper's existence statement, with the base valuation made explicit. -/
def DvSmallValuationExtensionExistsWithBase : Prop :=
  ∃ vK : DvNormalizedBaseValuation K,
    Nonempty (DvNormalizedValuationExtensionWitness (K := K) vK)
/-- Uniqueness of the extension on each cover, for a fixed base valuation and
fixed extension family. -/
def DvSmallValuationExtensionUniqueWithBase
    (vK : DvNormalizedBaseValuation K)
    (W : DvNormalizedValuationExtensionWitness (K := K) vK) : Prop :=
  ∀ (X : Example32SmallBase K)
    (V : DvCoverNormalizedValuationData K (coverField (K := K) X)),
    DvNormalizedValuationExtension (K := K) vK X V →
      V.valuation = (W.extension X).valuation
/-- The qValuation normalization gap: qValuation must be the ramification index
times the base q order. -/
def DvSmallQValuationRamificationFormula
    (vK : DvNormalizedBaseValuation K)
    (ramificationIndex : Example32SmallBase K → ℤ)
    (qOrder : Example32SmallBase K → ℤ) : Prop :=
  ∀ (X : Example32SmallBase K)
    (W : DvNormalizedValuationExtensionWitness (K := K) vK),
      (W.extension X).qValuation = ramificationIndex X * qOrder X
/-- Exact Mathlib/theory gap: the three statements not supplied by the repo or
Mathlib for the normalized finite-etale extension. -/
structure DvValuationExtensionMathlibGap where
  existence_of_extension : Prop
  uniqueness_of_extension : Prop
  ramification_normalization : Prop
  mathlib_has_HasExtension_class : Prop
  mathlib_has_extendToLocalization : Prop
/-- Exact missing datum as a Prop. -/
def DvValuationExtensionMathlibGapRequired : Prop :=
  Nonempty (DvValuationExtensionMathlibGap)
/-- Conditional family construction from an explicit witness; this is the
only construction here, and it does not fabricate a valuation. -/
noncomputable def dvSmallValuationFamilyOfWitness
    {vK : DvNormalizedBaseValuation K}
    (W : DvNormalizedValuationExtensionWitness (K := K) vK) :
    DvSmallValuationFamily (K := K) :=
  fun X => W.extension X
end LeanFormal.IUT.XiFPaper.S501ValuationExtensionActual
