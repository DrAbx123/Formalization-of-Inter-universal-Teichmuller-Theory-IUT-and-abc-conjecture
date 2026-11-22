import tmp.sheaf.xif.paper.S3180ConditionalAssemblyActual
import LeanFormal.IUT.ABCBridge.Bridge.IUTToABC
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison

/-! Mainline (T0/T1): package all accepted ABC forms from the S3180 conditional
  assembly inputs (new composition over the audited green assembly). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1S3180FormsPackageActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3180ConditionalAssemblyActual

universe u

theorem abc_forms_of_cor312AssemblyInputs {X : Type u}
    {W : IQHullLogVolumeInterface X} {pt : Nat → Nat → Nat → X}
    (H : Cor312AssemblyInputs W pt) :
    (ABCConjecture ∧ ABCLogConjecture) ∧
      ((∀ epsilon : Real, 0 < epsilon → ∃ A : Real, ∀ a b c : Nat, IsABCTriple a b c → Height.logHeight₁ (abcRationalPoint a c) ≤ (1 + epsilon) * arithmeticWeight (abcRationalPoint a c) + A) ∧ ABCHeightWeightAdditiveBoundV2) := by
  have h : ABCConjecture := abcConjecture_conditional H
  exact ⟨⟨h, abcConjecture_iff_abcLogConjecture.mp h⟩,
    ⟨abcConjecture_iff_abcArithmeticWeightHeightBound.mp h,
     abcConjecture_iff_ABCHeightWeightAdditiveBoundV2.mp h⟩⟩

end LeanFormal.IUT.XiFPaper.Mzk1S3180FormsPackageActual