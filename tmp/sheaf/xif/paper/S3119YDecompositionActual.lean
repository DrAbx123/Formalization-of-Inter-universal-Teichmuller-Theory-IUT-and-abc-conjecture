import tmp.sheaf.xif.paper.S3119CoordinateRingForwardActual
import tmp.sheaf.xif.paper.S3119AutoClassificationTargets
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
namespace LeanFormal.IUT.XiFPaper.S3119YDecompositionActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
variable {l : PrimeGeFive}

noncomputable def S3119Kx0 (p : Polynomial (K l)) : S1348CoordinateRing l :=
  Polynomial.aeval (S3119x0 (l := l)) p

def S3119YLinearOverXTarget (l : PrimeGeFive) : Prop :=
  ∀ φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l,
    ∃ p q : Polynomial (K l),
      φ (S3119y0 (l := l)) =
        S3119Kx0 (l := l) p + S3119Kx0 (l := l) q * S3119y0 (l := l)

lemma S3119Backward_of (l : PrimeGeFive) (p : Polynomial (K l)) :
    S3119Backward l (AdjoinRoot.of (W l).polynomial p) = S3119Kx0 (l := l) p := by
  unfold S3119Backward
  rw [AdjoinRoot.liftAlgHom_of]
  rfl

lemma S3119Backward_root (l : PrimeGeFive) :
    S3119Backward l (AdjoinRoot.root (W l).polynomial) =
      S3119y0 (l := l) := by
  unfold S3119Backward
  rw [AdjoinRoot.liftAlgHom_root]

theorem S3119YLinearOverX_target (l : PrimeGeFive) :
    S3119YLinearOverXTarget (l := l) := by
  intro φ
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
    (W' := W l) (x := S3119CoordinateRingEquiv l (φ (S3119y0 (l := l))))
  refine ⟨p, q, ?_⟩
  rw [← AlgEquiv.symm_apply_apply (S3119CoordinateRingEquiv l)
    (φ (S3119y0 (l := l)))]
  rw [← hpq]
  change S3119Backward l
      (p • (1 : CR l) + q • AdjoinRoot.root (W l).polynomial) =
    S3119Kx0 (l := l) p + S3119Kx0 (l := l) q * S3119y0 (l := l)
  rw [map_add]
  congr 1
  · rw [show p • (1 : CR l) = AdjoinRoot.of (W l).polynomial p from by
      rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
      rfl]
    rw [S3119Backward_of]
  · rw [show q • AdjoinRoot.root (W l).polynomial =
        (algebraMap (Polynomial (K l)) (CR l)) q *
          AdjoinRoot.root (W l).polynomial from Algebra.smul_def q _]
    rw [AdjoinRoot.algebraMap_eq (f := (W l).polynomial)]
    rw [map_mul, S3119Backward_of, S3119Backward_root]

theorem S3119_basis_decomposition (l : PrimeGeFive)
    (z : S1348CoordinateRing l) :
    ∃ p q : Polynomial (K l),
      z = S3119Kx0 (l := l) p + S3119Kx0 (l := l) q * S3119y0 (l := l) := by
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
    (W' := W l) (x := S3119CoordinateRingEquiv l z)
  refine ⟨p, q, ?_⟩
  rw [← AlgEquiv.symm_apply_apply (S3119CoordinateRingEquiv l) z]
  rw [← hpq]
  change S3119Backward l
      (p • (1 : CR l) + q • AdjoinRoot.root (W l).polynomial) =
    S3119Kx0 (l := l) p + S3119Kx0 (l := l) q * S3119y0 (l := l)
  rw [map_add]
  congr 1
  · rw [show p • (1 : CR l) = AdjoinRoot.of (W l).polynomial p from by
      rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
      rfl]
    rw [S3119Backward_of]
  · rw [show q • AdjoinRoot.root (W l).polynomial =
        (algebraMap (Polynomial (K l)) (CR l)) q *
          AdjoinRoot.root (W l).polynomial from Algebra.smul_def q _]
    rw [AdjoinRoot.algebraMap_eq (f := (W l).polynomial)]
    rw [map_mul, S3119Backward_of, S3119Backward_root]

noncomputable def S3119Xp (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) : Polynomial (K l) :=
  Classical.choose (S3119_basis_decomposition (l := l) (φ (S3119x0 (l := l))))

noncomputable def S3119Xq (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) : Polynomial (K l) :=
  Classical.choose (Classical.choose_spec
    (S3119_basis_decomposition (l := l) (φ (S3119x0 (l := l)))))

noncomputable def S3119Yp (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) : Polynomial (K l) :=
  Classical.choose (S3119_basis_decomposition (l := l) (φ (S3119y0 (l := l))))

noncomputable def S3119Yq (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) : Polynomial (K l) :=
  Classical.choose (Classical.choose_spec
    (S3119_basis_decomposition (l := l) (φ (S3119y0 (l := l)))))

lemma S3119Xp_spec (l : PrimeGeFive) (φ) :
    φ (S3119x0 (l := l)) =
      S3119Kx0 (l := l) (S3119Xp l φ) +
        S3119Kx0 (l := l) (S3119Xq l φ) * S3119y0 (l := l) := by
  have h := Classical.choose_spec (Classical.choose_spec
    (S3119_basis_decomposition (l := l) (φ (S3119x0 (l := l)))))
  simpa [S3119Xp, S3119Xq] using h

lemma S3119Yp_spec (l : PrimeGeFive) (φ) :
    φ (S3119y0 (l := l)) =
      S3119Kx0 (l := l) (S3119Yp l φ) +
        S3119Kx0 (l := l) (S3119Yq l φ) * S3119y0 (l := l) := by
  have h := Classical.choose_spec (Classical.choose_spec
    (S3119_basis_decomposition (l := l) (φ (S3119y0 (l := l)))))
  simpa [S3119Yp, S3119Yq] using h

lemma S3119_map_Kx0 (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) :
    φ (S3119Kx0 (l := l) p) =
      Polynomial.aeval (φ (S3119x0 (l := l))) p := by
  have hcomp : (algebraMap (K l) (S1348CoordinateRing l)).comp (RingHom.id (K l)) =
      (φ : S1348CoordinateRing l →+* S1348CoordinateRing l).comp
        (algebraMap (K l) (S1348CoordinateRing l)) := by
    ext a
    simp [AlgHom.commutes]
  have h := Polynomial.map_aeval_eq_aeval_map (R := K l)
    (S := S1348CoordinateRing l) (T := K l) (U := S1348CoordinateRing l)
    (φ := RingHom.id (K l))
    (ψ := (φ : S1348CoordinateRing l →+* S1348CoordinateRing l))
    hcomp p (S3119x0 (l := l))
  simpa [S3119Kx0] using h

theorem S3119_map_Kx0_decomposition (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) :
    ∃ P Q : Polynomial (K l),
      φ (S3119Kx0 (l := l) p) =
        S3119Kx0 (l := l) P + S3119Kx0 (l := l) Q * S3119y0 (l := l) := by
  rw [S3119_map_Kx0]
  exact S3119_basis_decomposition (l := l) _

lemma S3119Equiv_Kx0 (l : PrimeGeFive) (p : Polynomial (K l)) :
    S3119CoordinateRingEquiv l (S3119Kx0 (l := l) p) =
      AdjoinRoot.of (W l).polynomial p := by
  rw [← S3119Backward_of (l := l) p]
  change (S3119CoordinateRingEquiv l)
      ((S3119CoordinateRingEquiv l).symm
        ((AdjoinRoot.of (W l).polynomial) p)) =
    (AdjoinRoot.of (W l).polynomial) p
  exact AlgEquiv.apply_symm_apply _ _

lemma S3119Equiv_y0 (l : PrimeGeFive) :
    S3119CoordinateRingEquiv l (S3119y0 (l := l)) =
      AdjoinRoot.root (W l).polynomial := by
  have hh := congrArg (S3119CoordinateRingEquiv l) (S3119Backward_root (l := l))
  change (S3119CoordinateRingEquiv l)
      ((S3119CoordinateRingEquiv l).symm
        (AdjoinRoot.root (W l).polynomial)) =
    (S3119CoordinateRingEquiv l) (S3119y0 (l := l)) at hh
  rw [AlgEquiv.apply_symm_apply] at hh
  exact hh.symm

lemma S3119Kx0_basis_unique (l : PrimeGeFive)
    (p q : Polynomial (K l))
    (h : S3119Kx0 (l := l) p + S3119Kx0 (l := l) q * S3119y0 (l := l) = 0) :
    p = 0 ∧ q = 0 := by
  have he := congrArg (S3119CoordinateRingEquiv l) h
  simp only [map_add, map_mul, S3119Equiv_Kx0, S3119Equiv_y0, map_zero] at he
  have hp1 : (AdjoinRoot.of (W l).polynomial) p = p • (1 : CR l) := by
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
    rfl
  have hq1 : (AdjoinRoot.of (W l).polynomial) q * AdjoinRoot.root (W l).polynomial =
      q • AdjoinRoot.root (W l).polynomial := by
    rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq (f := (W l).polynomial)]
  rw [hp1, hq1] at he
  exact WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero he

theorem S3119_basis_decomposition_unique (l : PrimeGeFive)
    (z : S1348CoordinateRing l) (p q P Q : Polynomial (K l))
    (h1 : z = S3119Kx0 (l := l) p + S3119Kx0 (l := l) q * S3119y0 (l := l))
    (h2 : z = S3119Kx0 (l := l) P + S3119Kx0 (l := l) Q * S3119y0 (l := l)) :
    p = P ∧ q = Q := by
  have h : S3119Kx0 (l := l) p + S3119Kx0 (l := l) q * S3119y0 (l := l) =
      S3119Kx0 (l := l) P + S3119Kx0 (l := l) Q * S3119y0 (l := l) := by
    rw [← h1, h2]
  have he := congrArg (S3119CoordinateRingEquiv l) h
  simp only [map_add, map_mul, S3119Equiv_Kx0, S3119Equiv_y0] at he
  have hesub : (AdjoinRoot.of (W l).polynomial) p +
      (AdjoinRoot.of (W l).polynomial) q * AdjoinRoot.root (W l).polynomial -
      ((AdjoinRoot.of (W l).polynomial) P +
        (AdjoinRoot.of (W l).polynomial) Q * AdjoinRoot.root (W l).polynomial) = 0 := by
    exact sub_eq_zero.mpr he
  have hsubCR : (AdjoinRoot.of (W l).polynomial) (p - P) +
      (AdjoinRoot.of (W l).polynomial) (q - Q) *
        AdjoinRoot.root (W l).polynomial = 0 := by
    rw [map_sub, map_sub]
    linear_combination hesub
  have hp1 : (AdjoinRoot.of (W l).polynomial) (p - P) = (p - P) • (1 : CR l) := by
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
    rfl
  have hq1 : (AdjoinRoot.of (W l).polynomial) (q - Q) *
      AdjoinRoot.root (W l).polynomial = (q - Q) • AdjoinRoot.root (W l).polynomial := by
    rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq (f := (W l).polynomial)]
  rw [hp1, hq1] at hsubCR
  have hu := WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero hsubCR
  exact ⟨sub_eq_zero.mp hu.1, sub_eq_zero.mp hu.2⟩

#check S3119_basis_decomposition_unique
#print axioms S3119_basis_decomposition_unique
#check S3119Equiv_Kx0
#check S3119Equiv_y0
#check S3119Kx0_basis_unique
#print axioms S3119Kx0_basis_unique
#check S3119_map_Kx0
#check S3119_map_Kx0_decomposition
#print axioms S3119_map_Kx0
#check S3119_basis_decomposition
#check S3119Kx0_basis_unique
#check S3119Xp_spec
#check S3119Yp_spec
#print axioms S3119Kx0_basis_unique
#print axioms S3119Xp_spec
#print axioms S3119Yp_spec
#check S3119Backward_of
#check S3119Backward_root
#check S3119YLinearOverX_target
#print axioms S3119YLinearOverX_target
#check S3119Kx0
#check S3119YLinearOverXTarget
end LeanFormal.IUT.XiFPaper.S3119YDecompositionActual
end
