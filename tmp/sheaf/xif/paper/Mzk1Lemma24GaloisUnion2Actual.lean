import tmp.sheaf.xif.paper.Mzk1Lemma24GaloisUnionActual

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnion2Actual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnionActual

/-- The conjugate set is FINITE: it is the set of roots of the minimal polynomial
(nonzero, monic) mapped to the algebraic closure.  This discharges the registered
class-B statement ConjugateSetFiniteStatement (paper [Mzk1] Lemma 2.4 lines 166-169:
the union of all Galois conjugates of an algebraic point is finite). -/
theorem s3135_conjugateSet_finite (α : Qbar) : (conjugateSet α).Finite := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic (k := ℚ)
  have hInt : IsIntegral ℚ α :=
    IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic α)
  have hmonic : (minpoly ℚ α).Monic := minpoly.monic hInt
  have hne : (minpoly ℚ α).map (algebraMap ℚ Qbar) ≠ 0 :=
    Polynomial.map_monic_ne_zero hmonic
  have h1 : ∀ x : Qbar,
      ((minpoly ℚ α).map (algebraMap ℚ Qbar)).eval x = Polynomial.aeval x (minpoly ℚ α) := by
    intro x
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hfin := Polynomial.finite_setOf_isRoot (p := (minpoly ℚ α).map (algebraMap ℚ Qbar)) hne
  convert hfin using 1
  ext x
  simp only [conjugateSet, Set.mem_setOf_eq, Polynomial.IsRoot]
  rw [← h1 x]

/-- The discharged class-B statement: finiteness of the conjugate set. -/
theorem s3135_conjugateSetFiniteStatement (α : Qbar) : ConjugateSetFiniteStatement α :=
  s3135_conjugateSet_finite α

/-- (G) upgraded status: finiteness now PROVED; remaining is the union-over-S and the
m/d monotonicity used by the induction step (paper lines 179-206). -/
def s3135Mzk1GaloisUnionStatus2 : Audit.Obligation :=
  { id := "MZK1.lemma24.galois-conjugate-union.2"
    source :=
      "papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.4 lines " ++
        "166-169 and 179-206"
    status := Audit.VerificationStatus.interface
    note :=
      "PROVED: conjugateSet defs + self-membership + stability (previous file); " ++
        "NEW: s3135_conjugateSet_finite = the conjugate set is finite (roots of the " ++
        "monic mapped minimal polynomial; minpoly.monic + map_monic_ne_zero + " ++
        "Polynomial.finite_setOf_isRoot + aeval/eval_map bridge).  REMAINING: union " ++
        "over a finite S and the m(S')/d(S') < m(S)/d(S) monotonicity for the union " ++
        "and for f0(S) (needs the reducedDegreeOfPoint layer on point sets).  No " ++
        "fake witnesses; registry frozen 14041."
    dependsOn := [ "MZK1.lemma24.galois-conjugate-union" ]
    sorryItems := [ "union over finite S and m/d monotonicity (lines 179-206)" ] }

#check s3135_conjugateSet_finite
#check s3135_conjugateSetFiniteStatement
end LeanFormal.IUT.XiFPaper.Mzk1Lemma24GaloisUnion2Actual
end
-- bump-gu2
-- bump-gu2b
-- bump-gu2c
