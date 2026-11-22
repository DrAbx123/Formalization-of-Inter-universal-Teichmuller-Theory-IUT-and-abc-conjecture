import Mathlib

/-! # S3131 [GenEll] Theorem 2.1 equivalence shape + reduction direction -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3131GenEllEquivalenceShapeActual

/-- Theorem 2.1 shape: equivalence of the general and compactly bounded statements. -/
def EquivalenceShape (generalCase compactlyBoundedCase : Prop) : Prop :=
  generalCase ↔ compactlyBoundedCase

/-- The reduction direction actually used: (ii) compactly bounded => (i) general. -/
theorem reduction_of_equivalence {A B : Prop} (h : A ↔ B) : B → A :=
  h.mpr

/-- The reverse direction as stated by the paper (kept for fidelity). -/
theorem general_of_compactlyBounded {A B : Prop} (h : A ↔ B) : A → B :=
  h.mp

#check reduction_of_equivalence
#check EquivalenceShape

end LeanFormal.IUT.XiFPaper.S3131GenEllEquivalenceShapeActual
end