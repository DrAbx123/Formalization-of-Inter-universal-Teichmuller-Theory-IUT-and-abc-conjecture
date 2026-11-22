import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import tmp.sheaf.xif.paper.S2787ClauseB37Actual

noncomputable section
open AlgebraicGeometry CategoryTheory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual

open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

variable (K : Type u) [Field K]

/-- E37 affine Weierstrass curve y^2 + y = x^3 - x over an arbitrary field K. -/
def S2801E37Curve : WeierstrassCurve K where
  a₁ := 0
  a₂ := 0
  a₃ := 1
  a₄ := -1
  a₆ := 0

/-- E37 affine equation polynomial in K[x,y]. -/
noncomputable def S2801E37Polynomial : MvPolynomial (Fin 2) K :=
  weierstrassAffinePolynomial (S2801E37Curve K)

noncomputable def S2801E37Ideal : Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span {S2801E37Polynomial K}

noncomputable abbrev S2801E37CoordinateRing : Type u :=
  MvPolynomial (Fin 2) K ⧸ S2801E37Ideal K

noncomputable abbrev S2801E37AffineScheme : Scheme :=
  Spec (CommRingCat.of (S2801E37CoordinateRing K))

theorem S2801E37AffineScheme_isAffine : IsAffine (S2801E37AffineScheme K) :=
  inferInstance

noncomputable abbrev S2801E37X : S2801E37CoordinateRing K :=
  Ideal.Quotient.mk (S2801E37Ideal K) (MvPolynomial.X 0)

noncomputable abbrev S2801E37Y : S2801E37CoordinateRing K :=
  Ideal.Quotient.mk (S2801E37Ideal K) (MvPolynomial.X 1)

/-- The actual E37 relation in the coordinate ring: y^2 + y = x^3 - x. -/
theorem S2801E37_relation :
    S2801E37Y K ^ 2 + S2801E37Y K = S2801E37X K ^ 3 - S2801E37X K := by
  have hmem : S2801E37Polynomial K ∈ S2801E37Ideal K :=
    Ideal.subset_span (Set.mem_singleton _)
  have hzero : (Ideal.Quotient.mk (S2801E37Ideal K)) (S2801E37Polynomial K) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have h : S2801E37Y K ^ 2 + S2801E37Y K -
      (S2801E37X K ^ 3 + -S2801E37X K) = 0 := by
    simpa [S2801E37Polynomial, S2801E37Curve, weierstrassAffinePolynomial,
      S2801E37X, S2801E37Y, map_add, map_sub, map_pow, map_mul] using hzero
  linear_combination h

/-- Structure morphism to Spec K. -/
noncomputable abbrev S2801E37StructureMap :
    S2801E37AffineScheme K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (S2801E37CoordinateRing K)))

noncomputable abbrev S2801E37AsOver :
    Over (Spec (CommRingCat.of K)) :=
  Over.mk (S2801E37StructureMap K)

#check S2801E37Curve
#check S2801E37Polynomial
#check S2801E37AffineScheme
#check S2801E37AffineScheme_isAffine
#check S2801E37_relation
#check S2801E37AsOver
#print axioms S2801E37_relation

end LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
end
