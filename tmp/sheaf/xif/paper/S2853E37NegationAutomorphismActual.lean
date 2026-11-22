import tmp.sheaf.xif.paper.S2801D6FaithfulActual
import tmp.sheaf.xif.paper.S2814bE37ChartZOverActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme
import Mathlib.RingTheory.Localization.Away.Basic
import tmp.sheaf.xif.paper.S2801E37ProjectiveClosure
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveScheme

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual

open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual
open LeanFormal.IUT.XiFPaper.S2814bE37ChartZOverActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u
variable (K : Type u) [Field K] [DecidableEq K]

/-- Substitution x ↦ x, y ↦ -y - 1 on K[x,y]. -/
noncomputable def S2853Subst : Fin 2 → MvPolynomial (Fin 2) K
  | ⟨0, _⟩ => MvPolynomial.X 0
  | ⟨1, _⟩ => -MvPolynomial.X 1 - 1
  | ⟨n + 2, h⟩ => absurd h (by omega)

/-- The substitution read in the E37 coordinate ring. -/
noncomputable def S2853PolyHom :
    MvPolynomial (Fin 2) K →+* S2801E37CoordinateRing K :=
  (Ideal.Quotient.mk (S2801E37Ideal K)).comp
    (MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K))

theorem S2853PolyHom_relation :
    S2853PolyHom K (S2801E37Polynomial K) = 0 := by
  rw [S2853PolyHom, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  have hsub : (MvPolynomial.eval₂Hom MvPolynomial.C (S2853Subst K))
      (S2801E37Polynomial K) = S2801E37Polynomial K := by
    simp [S2801E37Polynomial, S2801E37Curve,
      LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial,
      S2853Subst]
    ring_nf
  rw [hsub]
  simp only [S2801E37Ideal]
  exact Ideal.subset_span (Set.mem_singleton _)

noncomputable def S2853RingHom :
    S2801E37CoordinateRing K →+* S2801E37CoordinateRing K :=
  Ideal.Quotient.lift (S2801E37Ideal K) (S2853PolyHom K) (by
    have hle : S2801E37Ideal K ≤ RingHom.ker (S2853PolyHom K) := by
      simp only [S2801E37Ideal]
      rw [Ideal.span_le]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      change S2853PolyHom K (S2801E37Polynomial K) = 0
      exact S2853PolyHom_relation K
    intro a ha
    exact RingHom.mem_ker.mp (hle ha))

#check S2853PolyHom
#check S2853PolyHom_relation
#check S2853RingHom
#print axioms S2853RingHom

/-- Chart-Z endomorphism induced by the negation substitution (x,y) -> (x,-y-1). -/
noncomputable def S2853ChartZSchemeEndo :
    S2801E37AffineScheme K ⟶ S2801E37AffineScheme K :=
  Spec.map (CommRingCat.ofHom (S2853RingHom K))

#check S2853ChartZSchemeEndo

end LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
end


