import tmp.sheaf.xif.paper.S3119NormDegreeActual
import tmp.sheaf.xif.paper.S3128CoordinateRingTransferActual
import Mathlib.Algebra.GroupWithZero.NeZero
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119YDecompositionActual
open LeanFormal.IUT.XiFPaper.S3119PhiMatrixActual
open LeanFormal.IUT.XiFPaper.S3119NormDegreeActual
open LeanFormal.IUT.XiFPaper.S3128CoordinateRingTransferActual
namespace LeanFormal.IUT.XiFPaper.S3119InfinityValuationActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
variable {l : PrimeGeFive}

noncomputable def S3119InfinityOrd (l : PrimeGeFive)
    (z : S1348CoordinateRing l) : ℤ :=
  -((S3119Norm l z).natDegree : ℤ)

lemma S3119Norm_mul (l : PrimeGeFive) (z w : S1348CoordinateRing l) :
    S3119Norm l (z * w) = S3119Norm l z * S3119Norm l w := by
  unfold S3119Norm
  rw [map_mul]
  exact map_mul (Algebra.norm (Polynomial (K l)))
    (S3119CoordinateRingEquiv l z) (S3119CoordinateRingEquiv l w)

lemma S3119Norm_ne_zero (l : PrimeGeFive) (z : S1348CoordinateRing l)
    (hz : z ≠ 0) : S3119Norm l z ≠ 0 := by
  letI : Module.Free (Polynomial (K l)) (CR l) :=
    Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis (W l))
  letI : Module.Finite (Polynomial (K l)) (CR l) :=
    Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis (W l))
  unfold S3119Norm
  intro hzero
  have hz0 : S3119CoordinateRingEquiv l z = 0 :=
    (Algebra.norm_eq_zero_iff (R := Polynomial (K l))).mp hzero
  exact hz ((S3119CoordinateRingEquiv l).injective hz0)

lemma S3119InfinityOrd_mul (l : PrimeGeFive) (z w : S1348CoordinateRing l)
    (hz : z ≠ 0) (hw : w ≠ 0) :
    S3119InfinityOrd l (z * w) =
      S3119InfinityOrd l z + S3119InfinityOrd l w := by
  unfold S3119InfinityOrd
  rw [S3119Norm_mul]
  rw [Polynomial.natDegree_mul (S3119Norm_ne_zero l z hz)
    (S3119Norm_ne_zero l w hw)]
  push_cast
  ring

def S3119InfinityOrdAddTarget (l : PrimeGeFive) : Prop :=
  ∀ z w : S1348CoordinateRing l,
    z ≠ 0 → w ≠ 0 → z + w ≠ 0 →
      min (S3119InfinityOrd l z) (S3119InfinityOrd l w) ≤
        S3119InfinityOrd l (z + w)

lemma S3119_equiv_basis_decomposition (l : PrimeGeFive)
    (z : S1348CoordinateRing l) :
    ∃ p q : Polynomial (K l),
      S3119CoordinateRingEquiv l z =
        p • (1 : CR l) + q • AdjoinRoot.root (W l).polynomial := by
  obtain ⟨p, q, hz⟩ := S3119_basis_decomposition (l := l) z
  refine ⟨p, q, ?_⟩
  rw [hz]
  rw [map_add, map_mul]
  simp only [S3119Equiv_Kx0, S3119Equiv_y0]
  congr 1
  · rw [show (AdjoinRoot.of (W l).polynomial) p = p • (1 : CR l) from by
      rw [WeierstrassCurve.Affine.CoordinateRing.smul, mul_one]
      rfl]
  · rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq (f := (W l).polynomial)]

lemma S3119_basis_add (l : PrimeGeFive)
    (p q r s : Polynomial (K l)) :
    (p • (1 : CR l) + q • AdjoinRoot.root (W l).polynomial) +
        (r • (1 : CR l) + s • AdjoinRoot.root (W l).polynomial) =
      (p + r) • (1 : CR l) +
        (q + s) • AdjoinRoot.root (W l).polynomial := by
  simp only [add_smul]
  abel

lemma S3119_degree_norm_root (l : PrimeGeFive)
    (p q : Polynomial (K l)) :
    (Algebra.norm (Polynomial (K l))
        (p • (1 : CR l) + q • AdjoinRoot.root (W l).polynomial)).degree =
      max (2 • p.degree) (2 • q.degree + 3) := by
  change (Algebra.norm (Polynomial (K l))
      (p • (1 : CR l) + q •
        (WeierstrassCurve.Affine.CoordinateRing.mk (W l)) Polynomial.X)).degree =
    max (2 • p.degree) (2 • q.degree + 3)
  rw [WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis]

#check S3119_degree_norm_root
lemma S3119_two_nsmul_max (a b : WithBot ℕ) :
    (2 : ℕ) • max a b = max ((2 : ℕ) • a) ((2 : ℕ) • b) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]
    rw [max_eq_right]
    exact nsmul_le_nsmul_right h 2
  · rw [max_eq_left h]
    rw [max_eq_left]
    exact nsmul_le_nsmul_right h 2

lemma S3119Norm_degree_add_le (l : PrimeGeFive)
    (z w : S1348CoordinateRing l) :
    (S3119Norm l (z + w)).degree ≤
      max ((S3119Norm l z).degree) ((S3119Norm l w).degree) := by
  obtain ⟨p, q, hz⟩ := S3119_equiv_basis_decomposition (l := l) z
  obtain ⟨r, s, hw⟩ := S3119_equiv_basis_decomposition (l := l) w
  have hsum : S3119CoordinateRingEquiv l (z + w) =
      (p + r) • (1 : CR l) + (q + s) • AdjoinRoot.root (W l).polynomial := by
    rw [map_add, hz, hw]
    exact S3119_basis_add (l := l) p q r s
  have hzdeg : (S3119Norm l z).degree =
      max (2 • p.degree) (2 • q.degree + 3) := by
    rw [S3119Norm, hz]
    exact S3119_degree_norm_root (l := l) p q
  have hwdeg : (S3119Norm l w).degree =
      max (2 • r.degree) (2 • s.degree + 3) := by
    rw [S3119Norm, hw]
    exact S3119_degree_norm_root (l := l) r s
  have hsumdeg : (S3119Norm l (z + w)).degree =
      max (2 • (p + r).degree) (2 • (q + s).degree + 3) := by
    rw [S3119Norm, hsum]
    exact S3119_degree_norm_root (l := l) (p + r) (q + s)
  rw [hsumdeg, hzdeg, hwdeg]
  apply max_le
  · calc
      (2 : ℕ) • (p + r).degree
          ≤ (2 : ℕ) • (max p.degree r.degree) := by
            rw [two_nsmul, two_nsmul]
            exact add_le_add (Polynomial.degree_add_le p r)
              (Polynomial.degree_add_le p r)
      _ = (max ((2 : ℕ) • p.degree) ((2 : ℕ) • r.degree)) :=
            S3119_two_nsmul_max p.degree r.degree
      _ ≤ max (max ((2 : ℕ) • p.degree) ((2 : ℕ) • q.degree + 3))
              (max ((2 : ℕ) • r.degree) ((2 : ℕ) • s.degree + 3)) := by
            apply max_le
            · exact le_trans (le_max_left _ _) (le_max_left _ _)
            · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · calc
      (2 : ℕ) • (q + s).degree + 3
          ≤ (2 : ℕ) • (max q.degree s.degree) + 3 := by
            rw [two_nsmul, two_nsmul]
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (add_le_add (Polynomial.degree_add_le q s)
                (Polynomial.degree_add_le q s)) 3
      _ = max ((2 : ℕ) • q.degree) ((2 : ℕ) • s.degree) + 3 :=
            congrArg (fun t => t + 3) (S3119_two_nsmul_max q.degree s.degree)
      _ = max ((2 : ℕ) • q.degree + 3) ((2 : ℕ) • s.degree + 3) := by
            rw [max_add_add_right]
      _ ≤ max (max ((2 : ℕ) • p.degree) ((2 : ℕ) • q.degree + 3))
              (max ((2 : ℕ) • r.degree) ((2 : ℕ) • s.degree + 3)) := by
            apply max_le
            · exact le_trans (le_max_right _ _) (le_max_left _ _)
            · exact le_trans (le_max_right _ _) (le_max_right _ _)

#check S3119Norm_degree_add_le
#print axioms S3119Norm_degree_add_le
lemma S3119InfinityOrd_add (l : PrimeGeFive)
    (z w : S1348CoordinateRing l)
    (hz : z ≠ 0) (hw : w ≠ 0) (hzw : z + w ≠ 0) :
    min (S3119InfinityOrd l z) (S3119InfinityOrd l w) ≤
      S3119InfinityOrd l (z + w) := by
  have hzn : S3119Norm l z ≠ 0 := S3119Norm_ne_zero l z hz
  have hwn : S3119Norm l w ≠ 0 := S3119Norm_ne_zero l w hw
  have hsum : S3119Norm l (z + w) ≠ 0 := S3119Norm_ne_zero l (z + w) hzw
  have hdeg := S3119Norm_degree_add_le (l := l) z w
  rw [Polynomial.degree_eq_natDegree hzn,
    Polynomial.degree_eq_natDegree hwn,
    Polynomial.degree_eq_natDegree hsum] at hdeg
  have hnat : (S3119Norm l (z + w)).natDegree ≤
      max (S3119Norm l z).natDegree (S3119Norm l w).natDegree := by
    rcases le_max_iff.mp hdeg with h | h
    · exact le_trans (WithBot.coe_le_coe.mp h) (le_max_left _ _)
    · exact le_trans (WithBot.coe_le_coe.mp h) (le_max_right _ _)
  unfold S3119InfinityOrd
  have hmin : min (-(↑(S3119Norm l z).natDegree : ℤ))
      (-(↑(S3119Norm l w).natDegree : ℤ)) =
      -((max (S3119Norm l z).natDegree (S3119Norm l w).natDegree : ℕ) : ℤ) := by
    rcases le_total (S3119Norm l z).natDegree (S3119Norm l w).natDegree with h | h
    · rw [max_eq_right h]
      apply min_eq_right
      exact neg_le_neg (by exact_mod_cast h)
    · rw [max_eq_left h]
      apply min_eq_left
      exact neg_le_neg (by exact_mod_cast h)
  rw [hmin]
  exact neg_le_neg (by exact_mod_cast hnat)

theorem S3119InfinityOrdAddTarget_proof (l : PrimeGeFive) :
    S3119InfinityOrdAddTarget (l := l) := by
  intro z w hz hw hzw
  exact S3119InfinityOrd_add (l := l) z w hz hw hzw

noncomputable def S3119InfinityOrdTop (l : PrimeGeFive)
    (z : S1348CoordinateRing l) : WithTop ℤ := by
  classical
  exact if z = 0 then ⊤ else ↑(S3119InfinityOrd l z)

noncomputable def S3119InfinityAddValuation (l : PrimeGeFive) :
    AddValuation (S1348CoordinateRing l) (WithTop ℤ) :=
  AddValuation.of (S3119InfinityOrdTop l)
    (by simp [S3119InfinityOrdTop])
    (by
      haveI : IsDomain (S1348CoordinateRing l) := S3128CoordinateRing_isDomain (l := l)
      have h1ne : (1 : S1348CoordinateRing l) ≠ 0 := one_ne_zero
      simp [S3119InfinityOrdTop, h1ne, S3119InfinityOrd, S3119Norm])
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx
        by_cases hy : y = 0
        · subst hy
          simp [S3119InfinityOrdTop]
        · simpa [S3119InfinityOrdTop, hy] using le_rfl
      by_cases hy : y = 0
      · subst hy
        by_cases hx2 : x = 0
        · subst hx2
          simp [S3119InfinityOrdTop]
        · simpa [S3119InfinityOrdTop, hx2] using le_rfl
      by_cases hxy : x + y = 0
      · simp [S3119InfinityOrdTop, hx, hy, hxy]
      have h := S3119InfinityOrd_add (l := l) x y hx hy hxy
      simp only [S3119InfinityOrdTop]
      rw [if_neg hx, if_neg hy, if_neg hxy]
      change (↑(min (S3119InfinityOrd l x) (S3119InfinityOrd l y)) : WithTop ℤ) ≤
        ↑(S3119InfinityOrd l (x + y))
      exact WithTop.coe_le_coe.mpr h)
    (by
      intro x y
      by_cases hx : x = 0
      · subst hx
        simp [S3119InfinityOrdTop]
      by_cases hy : y = 0
      · subst hy
        simp [S3119InfinityOrdTop, hx]
      have hxy : x * y ≠ 0 := by
        intro h
        have hnorm : S3119Norm l (x * y) = 0 := by
          rw [h]
          unfold S3119Norm
          letI : Module.Free (Polynomial (K l)) (CR l) :=
            Module.Free.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis (W l))
          letI : Module.Finite (Polynomial (K l)) (CR l) :=
            Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis (W l))
          letI : IsDomain (CR l) := inferInstance
          rw [map_zero, Algebra.norm_zero]
        rw [S3119Norm_mul] at hnorm
        exact mul_ne_zero (S3119Norm_ne_zero l x hx)
          (S3119Norm_ne_zero l y hy) hnorm
      simp only [S3119InfinityOrdTop]
      rw [if_neg hx, if_neg hy, if_neg hxy]
      rw [S3119InfinityOrd_mul (l := l) x y hx hy]
      exact WithTop.coe_add (S3119InfinityOrd l x) (S3119InfinityOrd l y))

#check S3119InfinityOrdTop
#check S3119InfinityAddValuation
#print axioms S3119InfinityAddValuation
end LeanFormal.IUT.XiFPaper.S3119InfinityValuationActual
end
