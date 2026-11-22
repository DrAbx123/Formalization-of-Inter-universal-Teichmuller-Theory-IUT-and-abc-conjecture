import Mathlib

noncomputable section
open Polynomial

namespace LeanFormal.IUT.XiFPaper.S2583FactorDegreeActual

/-- An irreducible monic polynomial over a finite field divides X ^ (q ^ d) - X,
where q is the field cardinality and d is its degree. -/
theorem irreducible_dvd_X_pow_card_pow_sub_X
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {g : K[X]} (hg : Irreducible g) (hmonic : g.Monic) :
    g ∣ X ^ (Fintype.card K ^ g.natDegree) - X := by
  let L := AdjoinRoot g
  letI : Fact (Irreducible g) := ⟨hg⟩
  letI : Field L := AdjoinRoot.instField
  let α : L := AdjoinRoot.root g
  let hpb := AdjoinRoot.powerBasis hg.ne_zero
  have hdim : hpb.dim = g.natDegree := AdjoinRoot.powerBasis_dim hg.ne_zero
  letI : Fintype L := Fintype.ofEquiv (Fin hpb.dim → K) hpb.basis.equivFun.symm
  have hfin : Module.finrank K L = g.natDegree := by
    rw [hpb.finrank, hdim]
  have hcard : Fintype.card L = Fintype.card K ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K) (V := L), hfin]
  have hroot : α ^ (Fintype.card L) = α := by
    simpa using (FiniteField.pow_card_pow (K := L) 1 α)
  have hroot' : α ^ (Fintype.card K ^ g.natDegree) = α := by
    rwa [← hcard]
  have hzero : aeval α ((X : K[X]) ^ (Fintype.card K ^ g.natDegree) - X) = 0 := by
    simp [hroot']
  have hmin : minpoly K α = g := by
    rw [AdjoinRoot.minpoly_root hg.ne_zero, hmonic.leadingCoeff]
    simp
  have hdvd : minpoly K α ∣ X ^ (Fintype.card K ^ g.natDegree) - X :=
    minpoly.dvd K α hzero
  simpa [hmin] using hdvd

end LeanFormal.IUT.XiFPaper.S2583FactorDegreeActual
end
