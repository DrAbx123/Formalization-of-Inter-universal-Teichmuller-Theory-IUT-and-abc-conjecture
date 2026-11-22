import tmp.sheaf.xif.paper.S2584PrimeDegreeOneActual

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2586PrimeMaximalActual

open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual

instance : Fact (Nat.Prime 613) := ⟨by norm_num⟩

theorem S2586_P_isMaximal (W : S2584PrimeDegreeOneWitness) : W.P.IsMaximal := by
  haveI : IsField (S ⧸ W.P) := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨W.residueEquivS.symm 0, W.residueEquivS.symm 1, by
        intro h
        have h2 := congrArg W.residueEquivS h
        exact (zero_ne_one : (0 : ZMod 613) ≠ 1) (by simpa using h2)⟩
    · intro x y; exact mul_comm x y
    · intro a ha
      have hz : W.residueEquivS a ≠ 0 := by
        intro h
        apply ha
        have h2 := congrArg W.residueEquivS.symm h
        simpa using h2
      refine ⟨W.residueEquivS.symm ((W.residueEquivS a)⁻¹), ?_⟩
      apply W.residueEquivS.injective
      simpa using mul_inv_cancel₀ hz
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient W.P).mpr ‹IsField (S ⧸ W.P)›

#print axioms S2586_P_isMaximal

end LeanFormal.IUT.XiFPaper.S2586PrimeMaximalActual
end
