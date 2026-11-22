import tmp.sheaf.n8.closure.EtaLatticeBasisRealizationActual
import Mathlib.RingTheory.Localization.Integer

/-!
# Eta p-adic lattice basis extension: exact gap

Exact missing theorem: a full Z_p-lattice L inside a Q_p-vector space E, with a
Z_p-basis b, has the same family as a Q_p-basis of E.  Equivalently, the
localization/span argument (common denominators + full lattice span) is not
assembled in production/Mathlib for the p-adic case; Mathlib has
Submodule.basisOfPid over Z_p and real ZLattice basis conversion, but no
Q_p basis-extension theorem.

No arbitrary basis is introduced.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open Module
open scoped BigOperators
open LeanFormal.IUT.N8Closure.EtaLatticeBasisRealizationActual

namespace LeanFormal.IUT.N8Closure.EtaPAdicLatticeBasisExtension

variable {p : Nat} [Fact p.Prime]
variable {E : Type*} [AddCommGroup E] [Module ℚ_[p] E] [Module ℤ_[p] E]
  [IsScalarTower ℤ_[p] ℚ_[p] E]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Exact missing p-adic lattice-basis extension theorem. -/
def MissingPAdicLatticeBasisExtension : Prop :=
  ∀ {L : Type*} [AddCommGroup L] [Module ℤ_[p] L]
    (b : Basis n ℤ_[p] L) (ι : L →ₗ[ℤ_[p]] E),
    Function.Injective ι →
    (∀ x : E, ∃ (y : L) (q : ℤ_[p]), q ≠ 0 ∧ q • x = ι y) →
    ∃ bE : Basis n ℚ_[p] E, ∀ i, bE i = ι (b i)

end LeanFormal.IUT.N8Closure.EtaPAdicLatticeBasisExtension
