import tmp.sheaf.xif.paper.S468DivisorNaturalityActual
import tmp.sheaf.xif.paper.S432SmallModelActual
import tmp.sheaf.xif.paper.S412DvTriangleTauActual

/-! # S495: DvSmallValuationFamily via unique valuation extension — exact needs

For each finite etale field cover L/K, the normalized valuation of the complete
DVR K should extend uniquely to L, with value group normalized so that qValuation
is `e * order(q_v)` (e the ramification index).  Mathlib has
`Valuation.HasExtension` but no theorem asserting existence/uniqueness of the
extension for a finite extension of complete DVRs, and no formula for the
normalization.  This file records exactly those missing lemmas and builds the
family only from an explicit witness; it does not fake the valuation.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S495DvSmallValuationActual

open LeanFormal.IUT.XiFPaper.S412DvTriangleTauActual
open LeanFormal.IUT.XiFPaper.S456RationalInclusionActual
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S468DivisorNaturalityActual

universe u
variable (K : Type u) [Field K]

/-- Exact missing existence: every finite etale cover of `Spec K` carries an
extension of the normalized valuation. -/
def DvSmallValuationExtensionExists : Prop :=
  ∀ X : Example32SmallBase K,
    Nonempty (DvCoverNormalizedValuationData K (coverField X))

/-- Exact missing uniqueness: the normalized extension is unique on each cover. -/
def DvSmallValuationExtensionUnique : Prop :=
  ∀ (X : Example32SmallBase K)
    (V W : DvCoverNormalizedValuationData K (coverField X)),
      V.valuation = W.valuation

/-- Exact missing qValuation normalization: qValuation is the ramification index
times the q_v order. -/
def DvSmallQValuationEqRamificationMulOrder
    (ramificationIndex : Example32SmallBase K → ℤ)
    (qOrder : Example32SmallBase K → ℤ) : Prop :=
  ∀ (X : Example32SmallBase K)
    (V : DvCoverNormalizedValuationData K (coverField X)),
      V.qValuation = ramificationIndex X * qOrder X

/-- Conditional family from an explicit existence proof. -/
noncomputable def dvSmallValuationFamilyOfExists
    (h : DvSmallValuationExtensionExists K) :
    DvSmallValuationFamily (K := K) :=
  fun X => Classical.choice (h X)

end LeanFormal.IUT.XiFPaper.S495DvSmallValuationActual
end
