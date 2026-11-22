import tmp.sheaf.xif.paper.S2056Psi5RootsPairsActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsPairsActual
open Polynomial
example : Fintype.card S2056Psi5Roots = 12 := by
  let q : (AlgebraicClosure ℚ)[X] := S2056Psi5.map (algebraMap ℚ (AlgebraicClosure ℚ))
  have hq : q.Splits := by
    simpa using (IsAlgClosed.splits_domain (f := RingHom.id (AlgebraicClosure ℚ)) q)
  have hsplit : (S2056Psi5.map (algebraMap ℚ (AlgebraicClosure ℚ))).Splits := by
    simpa [q] using hq
  have h := Polynomial.card_rootSet_eq_natDegree (p := S2056Psi5) (K := AlgebraicClosure ℚ) S2056Psi5_separable hsplit
  rw [h, S2056Psi5_natDegree]
