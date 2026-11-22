import tmp.sheaf.xif.paper.S2482QiInvolutionSquareActual
import tmp.sheaf.xif.paper.S2482InvolutionUniquenessAuditActual
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2482QiNontrivialActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionActual
open LeanFormal.IUT.XiFPaper.S2482QiInvolutionSquareActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open CategoryTheory

noncomputable def S2482I : F := Classical.choose S2480_hasSqrtNegOne

theorem S2482I_sq : S2482I * S2482I = -1 := Classical.choose_spec S2480_hasSqrtNegOne

theorem S2482_two_ne_zero : (2 : F) ≠ 0 := by
  norm_num

theorem S2482I_ne_one : S2482I ≠ 1 := by
  intro h
  have hsq := S2482I_sq
  rw [h] at hsq
  norm_num at hsq

noncomputable def S2482Eval : S2482CoordinateRing →ₐ[F] F :=
  Ideal.Quotient.liftₐ (Ideal.span {S2482AffinePolynomial})
    (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then S2482I else 1 - S2482I)) (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      rcases ha with ⟨q, rfl⟩
      have hp : MvPolynomial.aeval
          (fun i : Fin 2 => if i = 0 then S2482I else 1 - S2482I)
          S2482AffinePolynomial = 0 := by
        simp [S2482AffinePolynomial,
          LeanFormal.IUT.IUTII.Frobenioid.Example36.weierstrassAffinePolynomial,
          S2482Curve]
        have hI2 : S2482I ^ 2 = -1 := by
          rw [pow_two]
          exact S2482I_sq
        have hI3 : S2482I ^ 3 = -S2482I := by
          rw [pow_succ, hI2]
          ring
        ring_nf
        rw [hI2, hI3]
        ring
      rw [map_mul, hp, zero_mul])

theorem S2482Eval_X1 :
    S2482Eval (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
      (MvPolynomial.X 1)) = 1 - S2482I := by
  simp [S2482Eval]

theorem S2482_X1_ne_zero :
    (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
      (MvPolynomial.X 1) : S2482CoordinateRing) ≠ 0 := by
  intro h
  have h0 := congrArg S2482Eval h
  rw [S2482Eval_X1] at h0
  simp at h0
  exact S2482I_ne_one (by linear_combination -h0)

theorem S2482CoordinateRingInvolution_ne_id :
    S2482CoordinateRingInvolution ≠ AlgHom.id F S2482CoordinateRing := by
  intro h
  have hx := congrArg
    (fun f : S2482CoordinateRing →ₐ[F] S2482CoordinateRing =>
      f (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
        (MvPolynomial.X 1))) h
  have hinv : S2482CoordinateRingInvolution
      (Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
        (MvPolynomial.X 1)) =
      Ideal.Quotient.mk (Ideal.span {S2482AffinePolynomial})
        (-MvPolynomial.X 1) := by
    simp [S2482CoordinateRingInvolution, S2482AffineInvolutionAlgHom,
      Ideal.Quotient.liftₐ]
  rw [hinv] at hx
  have hxE := congrArg S2482Eval hx
  simp [S2482Eval, S2482Eval_X1] at hxE
  have hI1 : S2482I = 1 := by
    linear_combination (1 / 2 : F) * hxE
  exact S2482I_ne_one hI1

theorem S2482AffineInvolution_ne_id :
    S2482AffineInvolution ≠ 𝟙 S2482AffineOver := by
  intro h
  have hleft := congrArg
    (fun f : S2482AffineOver ⟶ S2482AffineOver => f.left) h
  simp only [S2482AffineInvolution, Over.id_left, Over.homMk_left] at hleft
  change AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom S2482CoordinateRingInvolution.toRingHom) =
      𝟙 (AlgebraicGeometry.Spec (CommRingCat.of S2482CoordinateRing)) at hleft
  rw [← AlgebraicGeometry.Spec.map_id] at hleft
  rw [AlgebraicGeometry.Spec.map_inj] at hleft
  have hring : S2482CoordinateRingInvolution.toRingHom =
      RingHom.id S2482CoordinateRing := by
    simpa using congrArg
      (fun f : CommRingCat.of S2482CoordinateRing ⟶
        CommRingCat.of S2482CoordinateRing => f.hom) hleft
  apply S2482CoordinateRingInvolution_ne_id
  apply AlgHom.ext
  intro x
  have hx := congrArg
    (fun f : S2482CoordinateRing →+* S2482CoordinateRing => f x) hring
  simpa using hx

theorem S2482EllipticInvolution_ne_id :
    S2482EllipticInvolution ≠
      Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve := by
  intro h
  have hleft := congrArg S1742HomOfStrongTrans h
  rw [show S1742HomOfStrongTrans S2482EllipticInvolution =
      S2482AffineInvolution from
    S1742HomOfStrongTrans_strongTransOfHom (F := F) S2482AffineInvolution] at hleft
  have hid : S1742HomOfStrongTrans
      (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve) =
      𝟙 S2482AffineOver := by
    rfl
  rw [hid] at hleft
  exact S2482AffineInvolution_ne_id hleft

theorem S2482_original_uniqueness_field_refuted
    (huniq : ∀ inv : S2482Orbicurve.Hom S2482Orbicurve,
      Iut.HyperbolicOrbicurve.Hom.TwoIso
        (Iut.HyperbolicOrbicurve.Hom.comp inv inv)
        (Iut.HyperbolicOrbicurve.Hom.id S2482Orbicurve) →
      inv = S2482EllipticInvolution) : False :=
  S2482EllipticInvolution_ne_id
    (S2482InvolutionUniquenessAuditActual.S2482_unique_elliptic_involution_forces_identity
      S2482EllipticInvolution huniq)

/-- Exact missing classification of order-two algebra automorphisms of the
coordinate ring R = F[x,y]/(y^2-x^3+x): the identity or the sign involution. -/
def S2482OrderTwoAlgAutClassification : Prop :=
  ∀ φ : S2482CoordinateRing ≃ₐ[F] S2482CoordinateRing,
    φ.toAlgHom.comp φ.toAlgHom = AlgHom.id F S2482CoordinateRing →
    φ = AlgHom.id F S2482CoordinateRing ∨
      φ.toAlgHom = S2482CoordinateRingInvolution

end LeanFormal.IUT.XiFPaper.S2482QiNontrivialActual

end