import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Arithmetic.LogarithmicBoundEquivalence
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC

/-!
# ShehddInterfaceRadicalPowerChainActual — interface => radical-power ABC form chain

Chain theorems: the compiled `cor312ToABCBridge_abcConjecture` is composed with the
proved log-form/radical-power equivalence to derive the radical-power estimate directly
from a Cor 3.12 -> ABC bridge interface.  New consequences; no new assumptions, no
sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddInterfaceRadicalPowerChainActual

open LeanFormal.IUT

/-- **PROVED chain:** a Cor 3.12 -> ABC bridge interface yields the per-epsilon
radical-power estimate. -/
theorem radicalPowerBound_of_interface (D : Cor312ToABCBridgeInterface) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ K : ℝ, 0 < K ∧
        ∀ a b c : Nat, IsABCTriple a b c →
          (c : ℝ) ≤ K * (radical (a * b * c) : ℝ) ^ (1 + epsilon) := by
  intro epsilon hepsilon
  have hlog : ABCLogConjecture :=
    abcConjecture_iff_abcLogConjecture.mp (cor312ToABCBridge_abcConjecture D)
  exact (abcLogBound_exists_iff_rpow_exists epsilon hepsilon).mp (hlog epsilon hepsilon)

/-- **PROVED chain:** a Cor 3.12 -> ABC bridge interface yields the log-form estimate. -/
theorem logBound_of_interface (D : Cor312ToABCBridgeInterface) :
    ABCLogConjecture :=
  abcConjecture_iff_abcLogConjecture.mp (cor312ToABCBridge_abcConjecture D)

/-- **PROVED chain:** the interface's height bound and the radical-power estimate are
both consequences of the same ABC conclusion. -/
theorem heightBound_and_radicalPower_of_interface
    (D : Cor312ToABCBridgeInterface) :
    (∀ epsilon : ℝ, 0 < epsilon → ∃ A : ℝ,
        ∀ a b c : Nat, IsABCTriple a b c →
          Height.logHeight₁ (abcRationalPoint a c) ≤
            (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) ∧
      (∀ epsilon : ℝ, 0 < epsilon →
        ∃ K : ℝ, 0 < K ∧
          ∀ a b c : Nat, IsABCTriple a b c →
            (c : ℝ) ≤ K * (radical (a * b * c) : ℝ) ^ (1 + epsilon)) :=
  ⟨cor312ToABCBridge_heightBound D, radicalPowerBound_of_interface D⟩

end LeanFormal.IUT.XiFPaper.ShehddInterfaceRadicalPowerChainActual
end