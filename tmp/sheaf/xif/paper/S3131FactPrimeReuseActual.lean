import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

/-! # S3131 Fact-prime instance reuse (prior art) -/

namespace LeanFormal.IUT.XiFPaper.S3131FactPrimeReuseActual

def S3131FactPrimeReuse : List (String × String) :=
  [ ("FinitePlacePadicScalarStructure.lean:25/28/29", "completionRationalPrime and its Fact (...Prime) instance -> REUSE (do not re-prove)") ]

theorem S3131FactPrimeReuse_length : S3131FactPrimeReuse.length = 1 := rfl

end LeanFormal.IUT.XiFPaper.S3131FactPrimeReuseActual