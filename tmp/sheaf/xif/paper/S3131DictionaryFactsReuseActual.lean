import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

/-! # S3131 dictionary facts reuse (prior art) -/

namespace LeanFormal.IUT.XiFPaper.S3131DictionaryFactsReuseActual

open LeanFormal.IUT

def S3131DictionaryFacts : List (String × String) :=
  [ ("RationalPointDictionary.lean:28-34", "Height.logHeight₁ (abcRationalPoint a c) = log c dictionary fact -> REUSE"),
    ("RationalPrimeSupport.lean:34-41", "arithmeticWeight (abcRationalPoint a c) = log(radical (a*b*c)) -> REUSE"),
    ("Cor312ToABCBridgeInterface.lean:113", "arithmeticWeight_nonneg -> REUSE") ]

theorem S3131DictionaryFacts_length : S3131DictionaryFacts.length = 3 := rfl

#check Height.logHeight₁
#check abcRationalPoint
#check arithmeticWeight

end LeanFormal.IUT.XiFPaper.S3131DictionaryFactsReuseActual