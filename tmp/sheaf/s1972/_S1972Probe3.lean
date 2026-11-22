import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

open LeanFormal.IUT

namespace Scratch

def honestCKTors (l : PrimeGeFive) : Iut.OrbicurveSignature where
  genus := 0
  stackyOrders := [2, 2, 2]
  punctures := (l.value + 1) / 2
  stackyOrders_ge_two := by
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> decide

example (l : PrimeGeFive) :
    (honestCKTors l).eulerCharacteristic < 0 := by
  have h5 : 5 ≤ l.value := l.ge_five
  have h3 : (3 : ℕ) ≤ (l.value + 1) / 2 := by omega
  simp only [honestCKTors, Iut.OrbicurveSignature.eulerCharacteristic]
  norm_num
  trace_state
  sorry

end Scratch
