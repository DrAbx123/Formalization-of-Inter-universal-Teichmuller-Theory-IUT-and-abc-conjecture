import tmp.sheaf.xif.paper.S2578Prime613Actual

noncomputable section

namespace S2578Consumer

open LeanFormal.IUT.XiFPaper.S2578Prime613Actual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual

example (h : S2578TameIndex) :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(613 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 613) :=
  S2578_prime613_exists h

example (h : S2578RootOrder = ⊤) :
    ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(613 : ℤ)}) ∧
      Nonempty (S ⧸ P ≃+* ZMod 613) :=
  S2578_prime613_exists_of_rootOrder_top h

example : ∃ P : Ideal S, P.IsPrime ∧ P.LiesOver (Ideal.span {(613 : ℤ)}) :=
  S2578_exists_prime_over613

#check @S2578_root_residue
#check @S2578_mem_primeField
#check @S2578_not_dvd_Cden

#print axioms S2578_prime613_exists

end S2578Consumer

end
