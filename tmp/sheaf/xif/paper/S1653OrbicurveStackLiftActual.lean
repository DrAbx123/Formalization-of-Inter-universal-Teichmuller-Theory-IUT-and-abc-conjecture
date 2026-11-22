import tmp.sheaf.xif.paper.S1555EllipticInvolutionActual
import Mathlib.Tactic

-- S1653: actual coordinate [-1] endomorphism of the S1348 affine curve and
-- the exact first missing stack lift (StrongTrans) to S1536XF.
-- No fake StrongTrans/signAction/quotient is inserted.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1653OrbicurveStackLiftActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

variable {l : PrimeGeFive}

/-- The polynomial endomorphism x |-> x, y |-> -x-y of the Gaussian affine
Weierstrass coordinate ring. -/
noncomputable def S1653PolyEndo :
    MvPolynomial (Fin 2) (S1348K l) →ₐ[S1348K l]
      MvPolynomial (Fin 2) (S1348K l) :=
  MvPolynomial.aeval (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.X 0 else -MvPolynomial.X 0 - MvPolynomial.X 1)

theorem S1653Curve_a1 : (S1348Curve l).a₁ = (1 : S1348K l) := by
  simp [S1348Curve, S1280Arithmetic, concreteGaussianInitialThetaArithmeticData,
    concreteSplitPuncturedCurve, concreteSplitCurve_a₁]
  rfl

theorem S1653Curve_a3 : (S1348Curve l).a₃ = (0 : S1348K l) := by
  simp [S1348Curve, S1280Arithmetic, concreteGaussianInitialThetaArithmeticData,
    concreteSplitPuncturedCurve, concreteSplitCurve_a₃]
  rfl

theorem S1653PolyEndo_affinePolynomial :
    S1653PolyEndo (l := l) (S1348AffinePolynomial l) =
      S1348AffinePolynomial l := by
  simp [S1653PolyEndo, S1348AffinePolynomial, weierstrassAffinePolynomial,
    S1653Curve_a1, S1653Curve_a3]
  ring

theorem S1653PolyEndo_mem_ideal :
    Ideal.span {S1348AffinePolynomial l} ≤
      Ideal.comap (S1653PolyEndo (l := l)).toRingHom
        (Ideal.span {S1348AffinePolynomial l}) := by
  rw [Ideal.span_le]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  exact Ideal.subset_span (by simp [S1653PolyEndo_affinePolynomial])

/-- Actual algebra endomorphism of the affine coordinate ring induced by [-1]. -/
noncomputable def S1653CoordEndo :
    S1348CoordinateRing l →ₐ[S1348K l] S1348CoordinateRing l :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ (S1348K l) _).comp (S1653PolyEndo (l := l)))
    (by
      intro a ha
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (S1653PolyEndo_mem_ideal ha))

/-- Exact first missing stack lift: a StrongTrans endomorphism of the S1419
stack fiber, equivalently an endomorphism of S1536XF. -/
abbrev S1653MissingStrongTrans : Type 1 :=
  (S1536XF (l := l)).Hom (S1536XF (l := l))

abbrev S1653MissingEndomorphism : Type 1 :=
  (S1536XF (l := l)).Hom (S1536XF (l := l))

theorem S1653MissingEndomorphism_eq :
    S1653MissingEndomorphism (l := l) =
      S1536FirstMissingField (l := l) := rfl

/-- The actual identity endomorphism, not the involution. -/
noncomputable def S1653IdentityHom :
    S1653MissingEndomorphism (l := l) :=
  Iut.HyperbolicOrbicurve.Hom.id (S1536XF (l := l))

/-- Missing sign action on xF. -/
abbrev S1653SignActionRequired : Type 1 :=
  Iut.OrbicurveSignAction (S1536XF (l := l))

/-- Missing sign quotient data. -/
abbrev S1653SignQuotientRequired : Type 1 :=
  Σ (action : Iut.OrbicurveSignAction (S1536XF (l := l)))
    (C : Iut.HyperbolicOrbicurve (S1280Arithmetic l).F)
    (quotient : Iut.OrbicurveSignInvariantMorphism action C),
    Iut.OrbicurveSignQuotientWitness action quotient

#check S1653PolyEndo
#check S1653PolyEndo_affinePolynomial
#check S1653CoordEndo
#check S1653MissingStrongTrans
#check S1653MissingEndomorphism
#check S1653MissingEndomorphism_eq
#check S1653IdentityHom
#check S1653SignActionRequired
#check S1653SignQuotientRequired

end LeanFormal.IUT.XiFPaper.S1653OrbicurveStackLiftActual

end