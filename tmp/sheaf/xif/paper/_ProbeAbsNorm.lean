import LeanFormal.IUT.ABCBridge.Geometry.FreyTateAnalyticInput
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
#check Ideal.absNorm_span_singleton
#check NumberField.RingOfIntegers
example (p : Nat) : Ideal.absNorm (Ideal.span {(p : NumberField.RingOfIntegers ℚ)}) = (Algebra.norm ℤ (p : NumberField.RingOfIntegers ℚ)).natAbs := rfl