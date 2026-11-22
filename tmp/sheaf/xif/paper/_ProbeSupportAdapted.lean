import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
open LeanFormal.IUT
#synth Fintype {p : Nat // p ∈ arithmeticPrimeSupport (4:ℚ)}
#check Finset.attach