import tmp.sheaf.xif.paper.S3119PowReduceActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119CoordinateRingForwardActual
open LeanFormal.IUT.XiFPaper.S3119PowReduceActual
namespace LeanFormal.IUT.XiFPaper.S3119PowReduceDegreeActual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
variable {l : PrimeGeFive}

noncomputable def S3119M (l : PrimeGeFive) (A B : Polynomial (K l)) : ℕ :=
  max A.natDegree (max (B.natDegree + 3) 0)

lemma S3119_natDegree_X3_add_C5_le (l : PrimeGeFive) :
    (Polynomial.X ^ 3 + Polynomial.C (5 : K l) : Polynomial (K l)).natDegree ≤ 3 := by
  calc
    (Polynomial.X ^ 3 + Polynomial.C (5 : K l) : Polynomial (K l)).natDegree
        ≤ max (Polynomial.X ^ 3 : Polynomial (K l)).natDegree
            (Polynomial.C (5 : K l)).natDegree := Polynomial.natDegree_add_le _ _
    _ ≤ 3 := by
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
      simp

lemma S3119_natDegree_A_le_M (l : PrimeGeFive) (A B : Polynomial (K l)) :
    A.natDegree ≤ S3119M l A B := le_max_left _ _

lemma S3119_natDegree_B_add_three_le_M (l : PrimeGeFive) (A B : Polynomial (K l)) :
    B.natDegree + 3 ≤ S3119M l A B :=
  le_trans (le_max_left _ _) (le_max_right _ _)

lemma S3119_natDegree_B_le_M (l : PrimeGeFive) (A B : Polynomial (K l)) :
    B.natDegree ≤ S3119M l A B := by
  have h := S3119_natDegree_B_add_three_le_M (l := l) A B
  omega

lemma S3119PowReduce_degree_bound (l : PrimeGeFive)
    (A B : Polynomial (K l)) (n : ℕ) :
    (S3119PowReduce l A B n).1.natDegree ≤ n * S3119M l A B ∧
      (S3119PowReduce l A B n).2.natDegree ≤ n * S3119M l A B := by
  induction n with
  | zero =>
    simp [S3119PowReduce, S3119M]
  | succ n ih =>
    obtain ⟨ihP, ihQ⟩ := ih
    simp only [S3119PowReduce]
    constructor
    · calc
        ((S3119PowReduce l A B n).1 * A +
            (S3119PowReduce l A B n).2 * B *
              (Polynomial.X ^ 3 + Polynomial.C (5 : K l))).natDegree
            ≤ max ((S3119PowReduce l A B n).1 * A).natDegree
                ((S3119PowReduce l A B n).2 * B *
                  (Polynomial.X ^ 3 + Polynomial.C (5 : K l))).natDegree :=
              Polynomial.natDegree_add_le _ _
        _ ≤ max (n * S3119M l A B + A.natDegree)
              (n * S3119M l A B + B.natDegree + 3) := by
            apply max_le
            · calc
                ((S3119PowReduce l A B n).1 * A).natDegree
                    ≤ (S3119PowReduce l A B n).1.natDegree + A.natDegree :=
                  Polynomial.natDegree_mul_le
                _ ≤ n * S3119M l A B + A.natDegree := Nat.add_le_add_right ihP _
                _ ≤ max (n * S3119M l A B + A.natDegree)
                    (n * S3119M l A B + B.natDegree + 3) := le_max_left _ _
            · calc
                ((S3119PowReduce l A B n).2 * B *
                    (Polynomial.X ^ 3 + Polynomial.C (5 : K l))).natDegree
                    ≤ ((S3119PowReduce l A B n).2 * B).natDegree +
                        (Polynomial.X ^ 3 + Polynomial.C (5 : K l)).natDegree :=
                  Polynomial.natDegree_mul_le
                _ ≤ ((S3119PowReduce l A B n).2.natDegree + B.natDegree) + 3 :=
                  Nat.add_le_add Polynomial.natDegree_mul_le
                    (S3119_natDegree_X3_add_C5_le l)
                _ ≤ (n * S3119M l A B + B.natDegree) + 3 :=
                  Nat.add_le_add_right (Nat.add_le_add_right ihQ _) _
                _ ≤ max (n * S3119M l A B + A.natDegree)
                    (n * S3119M l A B + B.natDegree + 3) := le_max_right _ _
        _ ≤ (n + 1) * S3119M l A B := by
            rw [Nat.succ_mul]
            apply max_le
            · have hA := S3119_natDegree_A_le_M (l := l) A B
              omega
            · have hB := S3119_natDegree_B_add_three_le_M (l := l) A B
              omega
    · calc
        ((S3119PowReduce l A B n).1 * B +
            (S3119PowReduce l A B n).2 * A -
            (S3119PowReduce l A B n).2 * B * Polynomial.X).natDegree
            ≤ max ((S3119PowReduce l A B n).1 * B +
                (S3119PowReduce l A B n).2 * A).natDegree
                ((S3119PowReduce l A B n).2 * B * Polynomial.X).natDegree :=
              Polynomial.natDegree_sub_le _ _
        _ ≤ max (max ((S3119PowReduce l A B n).1 * B).natDegree
                  ((S3119PowReduce l A B n).2 * A).natDegree)
                ((S3119PowReduce l A B n).2 * B * Polynomial.X).natDegree := by
            apply max_le
            · exact le_trans (Polynomial.natDegree_add_le _ _) (le_max_left _ _)
            · exact le_max_right _ _
        _ ≤ (n + 1) * S3119M l A B := by
            rw [Nat.succ_mul]
            apply max_le
            · apply max_le
              · calc
                  ((S3119PowReduce l A B n).1 * B).natDegree
                      ≤ (S3119PowReduce l A B n).1.natDegree + B.natDegree :=
                    Polynomial.natDegree_mul_le
                  _ ≤ n * S3119M l A B + B.natDegree := Nat.add_le_add_right ihP _
                  _ ≤ n * S3119M l A B + S3119M l A B := by
                    have hB := S3119_natDegree_B_le_M (l := l) A B
                    omega
              · calc
                  ((S3119PowReduce l A B n).2 * A).natDegree
                      ≤ (S3119PowReduce l A B n).2.natDegree + A.natDegree :=
                    Polynomial.natDegree_mul_le
                  _ ≤ n * S3119M l A B + A.natDegree := Nat.add_le_add_right ihQ _
                  _ ≤ n * S3119M l A B + S3119M l A B := by
                    have hA := S3119_natDegree_A_le_M (l := l) A B
                    omega
            · calc
                ((S3119PowReduce l A B n).2 * B * Polynomial.X).natDegree
                    ≤ ((S3119PowReduce l A B n).2 * B).natDegree + Polynomial.X.natDegree :=
                  Polynomial.natDegree_mul_le
                _ ≤ ((S3119PowReduce l A B n).2.natDegree + B.natDegree) + 1 := by
                  rw [Polynomial.natDegree_X]
                  exact Nat.add_le_add_right Polynomial.natDegree_mul_le 1
                _ ≤ (n * S3119M l A B + B.natDegree) + 1 :=
                  Nat.add_le_add_right (Nat.add_le_add_right ihQ _) _
                _ ≤ n * S3119M l A B + S3119M l A B := by
                  have hB : B.natDegree + 3 ≤ S3119M l A B :=
                    S3119_natDegree_B_add_three_le_M (l := l) A B
                  omega

lemma S3119PolyP_degree_bound (l : PrimeGeFive)
    (A B p : Polynomial (K l)) :
    (S3119PolyP l A B p).natDegree ≤ p.natDegree * S3119M l A B := by
  rw [S3119PolyP, Polynomial.sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  calc
    (Polynomial.C (p.coeff n) * (S3119PowReduce l A B n).1).natDegree
        ≤ (S3119PowReduce l A B n).1.natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ n * S3119M l A B := (S3119PowReduce_degree_bound (l := l) A B n).1
    _ ≤ p.natDegree * S3119M l A B := by
      apply Nat.mul_le_mul_right
      exact Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.1 hn)

lemma S3119PolyQ_degree_bound (l : PrimeGeFive)
    (A B p : Polynomial (K l)) :
    (S3119PolyQ l A B p).natDegree ≤ p.natDegree * S3119M l A B := by
  rw [S3119PolyQ, Polynomial.sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  calc
    (Polynomial.C (p.coeff n) * (S3119PowReduce l A B n).2).natDegree
        ≤ (S3119PowReduce l A B n).2.natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ n * S3119M l A B := (S3119PowReduce_degree_bound (l := l) A B n).2
    _ ≤ p.natDegree * S3119M l A B := by
      apply Nat.mul_le_mul_right
      exact Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.1 hn)

#check S3119PolyP_degree_bound
#check S3119PolyQ_degree_bound
#print axioms S3119PolyP_degree_bound
#check S3119PowReduce_degree_bound
#print axioms S3119PowReduce_degree_bound
#check S3119M
#check S3119_natDegree_X3_add_C5_le
end LeanFormal.IUT.XiFPaper.S3119PowReduceDegreeActual
end
