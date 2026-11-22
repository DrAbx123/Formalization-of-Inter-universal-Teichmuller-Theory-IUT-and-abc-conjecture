import tmp.sheaf.n8.closure.EtaPAdicLatticeBasisExtension
import Mathlib.RingTheory.Localization.Integer

/-!
# Eta localization basis manual: exact blockers

The manual basis-extension proof needs two local steps:

1. COMMON DENOMINATORS: for every finite family c : n -> Q_p there is
   q : Z_p, q != 0, with q * c i integral for all i.
2. FULL-LATTICE SPAN: every x : E is a Z_p-multiple of an element of L.

Then:
* independence: multiply sum_i c_i b_i = 0 by q; get a Z_p-relation among b_i;
  basis independence gives q*c_i = 0, hence c_i = 0;
* spanning: q*x in L = Z_p-span(b), so x is in the Q_p-span(b).

This file isolates the common-denominator lemma, which is the exact missing
localization theorem; no arbitrary basis is used.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open Module
open LeanFormal.IUT.N8Closure.EtaPAdicLatticeBasisExtension

namespace LeanFormal.IUT.N8Closure.EtaLocalizationBasisManual

variable {p : Nat} [Fact p.Prime]
variable {n : Type*} [Fintype n]

/-- Exact missing common-denominator lemma for Q_p over Z_p. -/
def MissingCommonDenominatorLemma : Prop :=
  ∀ c : n → ℚ_[p], ∃ q : ℤ_[p], q ≠ 0 ∧
    ∀ i, ∃ r : ℤ_[p], (r : ℚ_[p]) = (q : ℚ_[p]) * c i

/-- Exact missing full-lattice localization/span lemma. -/
def MissingFullLatticeSpanLemma : Prop :=
  ∀ {E : Type*} [AddCommGroup E] [Module ℚ_[p] E] [Module ℤ_[p] E]
    [IsScalarTower ℤ_[p] ℚ_[p] E]
    {L : Type*} [AddCommGroup L] [Module ℤ_[p] L]
    (ι : L →ₗ[ℤ_[p]] E), Function.Injective ι →
    (∀ x : E, ∃ (y : L) (q : ℤ_[p]), q ≠ 0 ∧ q • x = ι y)

end LeanFormal.IUT.N8Closure.EtaLocalizationBasisManual
