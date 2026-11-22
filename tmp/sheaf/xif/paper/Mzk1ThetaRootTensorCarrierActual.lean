/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # #10 second wave status record -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaRootTensorCarrierActual
def rows : List (String × String) :=
  [    ("carrier", "product of root extensions over Bad"),
    ("S1902Carrier", "= RootExtensionProductCarrier T (function product)"),
    ("tensor vs function", "GAP: FinitePadicTensor is tensor product, not pi-product")]
theorem rows_length : rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1ThetaRootTensorCarrierActual
