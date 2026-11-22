import tmp.sheaf.xif.paper.S3119YDecompositionActual
import tmp.sheaf.xif.paper.S3119PowReduceActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119AutoClassificationTargets
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119YDecompositionActual
open LeanFormal.IUT.XiFPaper.S3119PowReduceActual
namespace LeanFormal.IUT.XiFPaper.S3119PhiMatrixActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
variable {l : PrimeGeFive}

noncomputable def S3119PhiP (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) : Polynomial (K l) :=
  S3119PolyP l (S3119Xp l φ) (S3119Xq l φ) p

noncomputable def S3119PhiQ (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) : Polynomial (K l) :=
  S3119PolyQ l (S3119Xp l φ) (S3119Xq l φ) p

theorem S3119Phi_spec (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) :
    φ (S3119Kx0 (l := l) p) =
      S3119Kx0 (l := l) (S3119PhiP l φ p) +
        S3119Kx0 (l := l) (S3119PhiQ l φ p) * S3119y0 (l := l) := by
  rw [S3119_map_Kx0]
  rw [show φ (S3119x0 (l := l)) =
      S3119Kx0 (l := l) (S3119Xp l φ) +
        S3119Kx0 (l := l) (S3119Xq l φ) * S3119y0 (l := l)
    from S3119Xp_spec l φ]
  exact S3119Poly_spec (l := l) _ _ p

lemma S3119_basis_mul (l : PrimeGeFive)
    (A B C D : Polynomial (K l)) :
    (S3119Kx0 (l := l) A + S3119Kx0 (l := l) B * S3119y0 (l := l)) *
        (S3119Kx0 (l := l) C + S3119Kx0 (l := l) D * S3119y0 (l := l)) =
      S3119Kx0 (l := l) (A * C + B * D * (Polynomial.X ^ 3 + Polynomial.C (5 : K l))) +
        S3119Kx0 (l := l) (A * D + B * C - B * D * Polynomial.X) *
          S3119y0 (l := l) := by
  have h5 : algebraMap (S1348K l) (S1348CoordinateRing l) (5 : S1348K l) =
      (5 : S1348CoordinateRing l) := by
    change (algebraMap (S1348K l) (S1348CoordinateRing l))
        ((5 : ℕ) : S1348K l) = ((5 : ℕ) : S1348CoordinateRing l)
    exact map_natCast (algebraMap (S1348K l) (S1348CoordinateRing l)) 5
  have hy2 : S3119y0 (l := l) ^ 2 =
      -S3119x0 (l := l) * S3119y0 (l := l) + S3119x0 (l := l) ^ 3 +
        (5 : S1348CoordinateRing l) := by
    have h := S3119_curve_relation (l := l)
    rw [h5] at h
    linear_combination h
  simp only [S3119Kx0, Polynomial.aeval_add, Polynomial.aeval_sub,
    Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    map_pow, map_one, map_zero]
  ring_nf
  rw [hy2]
  ring_nf
  rw [h5]
  ring_nf

lemma S3119_symm_Kx0 (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (q : Polynomial (K l)) :
    φ.symm (S3119Kx0 (l := l) q) =
      S3119Kx0 (l := l) (S3119PhiP l φ.symm q) +
        S3119Kx0 (l := l) (S3119PhiQ l φ.symm q) * S3119y0 (l := l) :=
  S3119Phi_spec (l := l) φ.symm q

lemma S3119_symm_y0 (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    φ.symm (S3119y0 (l := l)) =
      S3119Kx0 (l := l) (S3119Yp l φ.symm) +
        S3119Kx0 (l := l) (S3119Yq l φ.symm) * S3119y0 (l := l) :=
  S3119Yp_spec (l := l) φ.symm

noncomputable def S3119CompP (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) : Polynomial (K l) :=
  S3119PhiP l φ.symm (S3119PhiP l φ p) +
    (S3119PhiP l φ.symm (S3119PhiQ l φ p) * S3119Yp l φ.symm +
      S3119PhiQ l φ.symm (S3119PhiQ l φ p) * S3119Yq l φ.symm *
        (Polynomial.X ^ 3 + Polynomial.C (5 : K l)))

noncomputable def S3119CompQ (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) : Polynomial (K l) :=
  S3119PhiQ l φ.symm (S3119PhiP l φ p) +
    (S3119PhiP l φ.symm (S3119PhiQ l φ p) * S3119Yq l φ.symm +
      S3119PhiQ l φ.symm (S3119PhiQ l φ p) * S3119Yp l φ.symm -
      S3119PhiQ l φ.symm (S3119PhiQ l φ p) * S3119Yq l φ.symm * Polynomial.X)

theorem S3119_Phi_comp_expanded (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) :
    φ.symm (φ (S3119Kx0 (l := l) p)) =
      S3119Kx0 (l := l) (S3119CompP l φ p) +
        S3119Kx0 (l := l) (S3119CompQ l φ p) * S3119y0 (l := l) := by
  rw [show φ (S3119Kx0 (l := l) p) =
      S3119Kx0 (l := l) (S3119PhiP l φ p) +
        S3119Kx0 (l := l) (S3119PhiQ l φ p) * S3119y0 (l := l)
    from S3119Phi_spec (l := l) φ p]
  rw [map_add, map_mul]
  simp only [S3119_symm_Kx0, S3119_symm_y0]
  rw [S3119_basis_mul]
  simp only [S3119CompP, S3119CompQ, S3119Kx0, Polynomial.aeval_add,
    Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X, map_pow]
  ring_nf

theorem S3119_Phi_comp (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l)
    (p : Polynomial (K l)) :
    S3119CompP l φ p = p ∧ S3119CompQ l φ p = 0 := by
  have h1 : φ.symm (φ (S3119Kx0 (l := l) p)) = S3119Kx0 (l := l) p :=
    AlgEquiv.symm_apply_apply φ (S3119Kx0 (l := l) p)
  rw [S3119_Phi_comp_expanded] at h1
  have h1' : S3119Kx0 (l := l) p =
      S3119Kx0 (l := l) (S3119CompP l φ p) +
        S3119Kx0 (l := l) (S3119CompQ l φ p) * S3119y0 (l := l) := h1.symm
  have h2 : S3119Kx0 (l := l) p =
      S3119Kx0 (l := l) p + S3119Kx0 (l := l) (0 : Polynomial (K l)) *
        S3119y0 (l := l) := by simp [S3119Kx0]
  have hu := S3119_basis_decomposition_unique (l := l) (S3119Kx0 (l := l) p)
    p 0 (S3119CompP l φ p) (S3119CompQ l φ p) h2 h1'
  exact ⟨hu.1.symm, hu.2.symm⟩

lemma S3119PolyP_X (l : PrimeGeFive) (A B : Polynomial (K l)) :
    S3119PolyP l A B Polynomial.X = A := by
  simp [S3119PolyP, S3119PowReduce]

lemma S3119PolyQ_X (l : PrimeGeFive) (A B : Polynomial (K l)) :
    S3119PolyQ l A B Polynomial.X = B := by
  simp [S3119PolyQ, S3119PowReduce]

lemma S3119PhiP_X (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    S3119PhiP l φ Polynomial.X = S3119Xp l φ := by
  simp [S3119PhiP, S3119PolyP_X]

lemma S3119PhiQ_X (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    S3119PhiQ l φ Polynomial.X = S3119Xq l φ := by
  simp [S3119PhiQ, S3119PolyQ_X]

theorem S3119_CompP_X (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    S3119CompP l φ Polynomial.X = Polynomial.X :=
  (S3119_Phi_comp (l := l) φ Polynomial.X).1

theorem S3119_CompQ_X (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    S3119CompQ l φ Polynomial.X = 0 :=
  (S3119_Phi_comp (l := l) φ Polynomial.X).2

noncomputable def S3119CompYP (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) : Polynomial (K l) :=
  S3119PhiP l φ.symm (S3119Yp l φ) +
    (S3119PhiP l φ.symm (S3119Yq l φ) * S3119Yp l φ.symm +
      S3119PhiQ l φ.symm (S3119Yq l φ) * S3119Yq l φ.symm *
        (Polynomial.X ^ 3 + Polynomial.C (5 : K l)))

noncomputable def S3119CompYQ (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) : Polynomial (K l) :=
  S3119PhiQ l φ.symm (S3119Yp l φ) +
    (S3119PhiP l φ.symm (S3119Yq l φ) * S3119Yq l φ.symm +
      S3119PhiQ l φ.symm (S3119Yq l φ) * S3119Yp l φ.symm -
      S3119PhiQ l φ.symm (S3119Yq l φ) * S3119Yq l φ.symm * Polynomial.X)

theorem S3119_CompY_expanded (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    φ.symm (φ (S3119y0 (l := l))) =
      S3119Kx0 (l := l) (S3119CompYP l φ) +
        S3119Kx0 (l := l) (S3119CompYQ l φ) * S3119y0 (l := l) := by
  rw [show φ (S3119y0 (l := l)) =
      S3119Kx0 (l := l) (S3119Yp l φ) +
        S3119Kx0 (l := l) (S3119Yq l φ) * S3119y0 (l := l)
    from S3119Yp_spec (l := l) φ]
  rw [map_add, map_mul]
  simp only [S3119_symm_Kx0, S3119_symm_y0]
  rw [S3119_basis_mul]
  simp only [S3119CompYP, S3119CompYQ, S3119Kx0, Polynomial.aeval_add,
    Polynomial.aeval_sub, Polynomial.aeval_mul, Polynomial.aeval_C,
    Polynomial.aeval_X, map_pow]
  ring_nf

theorem S3119_CompY (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    S3119CompYP l φ = 0 ∧ S3119CompYQ l φ = 1 := by
  have h1 : φ.symm (φ (S3119y0 (l := l))) = S3119y0 (l := l) :=
    AlgEquiv.symm_apply_apply φ (S3119y0 (l := l))
  rw [S3119_CompY_expanded] at h1
  have h1' : S3119y0 (l := l) =
      S3119Kx0 (l := l) (S3119CompYP l φ) +
        S3119Kx0 (l := l) (S3119CompYQ l φ) * S3119y0 (l := l) := h1.symm
  have h2 : S3119y0 (l := l) =
      S3119Kx0 (l := l) (0 : Polynomial (K l)) +
        S3119Kx0 (l := l) (1 : Polynomial (K l)) * S3119y0 (l := l) := by
    simp [S3119Kx0]
  have hu := S3119_basis_decomposition_unique (l := l) (S3119y0 (l := l))
    0 1 (S3119CompYP l φ) (S3119CompYQ l φ) h2 h1'
  exact ⟨hu.1.symm, hu.2.symm⟩

#check S3119CompYP
#check S3119CompYQ
#check S3119_CompY_expanded
#check S3119_CompY
#print axioms S3119_CompY
theorem S3119_CompP_X_expanded (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    S3119PhiP l φ.symm (S3119Xp l φ) +
        (S3119PhiP l φ.symm (S3119Xq l φ) * S3119Yp l φ.symm +
          S3119PhiQ l φ.symm (S3119Xq l φ) * S3119Yq l φ.symm *
            (Polynomial.X ^ 3 + Polynomial.C (5 : K l))) =
      Polynomial.X := by
  simpa [S3119CompP, S3119PhiP_X, S3119PhiQ_X] using
    S3119_CompP_X (l := l) φ

theorem S3119_CompQ_X_expanded (l : PrimeGeFive)
    (φ : S1348CoordinateRing l ≃ₐ[K l] S1348CoordinateRing l) :
    S3119PhiQ l φ.symm (S3119Xp l φ) +
        (S3119PhiP l φ.symm (S3119Xq l φ) * S3119Yq l φ.symm +
          S3119PhiQ l φ.symm (S3119Xq l φ) * S3119Yp l φ.symm -
          S3119PhiQ l φ.symm (S3119Xq l φ) * S3119Yq l φ.symm * Polynomial.X) =
      0 := by
  simpa [S3119CompQ, S3119PhiP_X, S3119PhiQ_X] using
    S3119_CompQ_X (l := l) φ

#check S3119_CompP_X_expanded
#check S3119_CompQ_X_expanded
#print axioms S3119_CompP_X_expanded
#check S3119PolyP_X
#check S3119_CompP_X
#check S3119_CompQ_X
#print axioms S3119_CompP_X
#check S3119_Phi_comp
#print axioms S3119_Phi_comp
#check S3119CompP
#check S3119CompQ
#check S3119_Phi_comp_expanded
#print axioms S3119_Phi_comp_expanded
#check S3119_symm_Kx0
#check S3119_symm_y0
#check S3119_basis_mul
#print axioms S3119_basis_mul
#check S3119PhiP
#check S3119PhiQ
#check S3119Phi_spec
#print axioms S3119Phi_spec
end LeanFormal.IUT.XiFPaper.S3119PhiMatrixActual
end
