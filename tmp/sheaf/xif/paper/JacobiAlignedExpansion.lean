import tmp.sheaf.xif.paper.TateJacobiHahnAttempt
import tmp.sheaf.xif.paper.QBinomialCommRing

set_option maxHeartbeats 1000000

noncomputable section

open LeanFormal.IUT.XiFPaper.TateJacobiHahnAttempt

namespace LeanFormal.IUT.XiFPaper.JacobiAlignedExpansion

variable {K : Type u} [Field K]

theorem alignedFirstProduct_expand (z : K) (N : Nat) :
    Finset.prod (Finset.range N) (fun m : Nat =>
        (1 : HahnSeries Int K) +
          (HahnSeries.C z * formalR ^ 2) * formalR ^ (4 * m)) =
      Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
        LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
          (K := HahnSeries Int K) N k (formalR ^ 4)
          (HahnSeries.C z * formalR ^ 2)) := by
  have hprod : Finset.prod (Finset.range N) (fun m : Nat =>
        (1 : HahnSeries Int K) +
          (HahnSeries.C z * formalR ^ 2) * formalR ^ (4 * m)) =
      Finset.prod (Finset.range N) (fun m : Nat =>
        (1 : HahnSeries Int K) +
          (HahnSeries.C z * formalR ^ 2) * (formalR ^ 4) ^ m) := by
    apply Finset.prod_congr rfl
    intro m hm
    rw [pow_mul]
  rw [hprod]
  exact LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinomialTheoremChoose
    (K := HahnSeries Int K) N (formalR ^ 4) (HahnSeries.C z * formalR ^ 2)

theorem alignedSecondProduct_expand (z : K) (N : Nat) :
    Finset.prod (Finset.range N) (fun m : Nat =>
        (1 : HahnSeries Int K) +
          (HahnSeries.C z⁻¹ * formalR ^ 2) * formalR ^ (4 * m)) =
      Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
        LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
          (K := HahnSeries Int K) N k (formalR ^ 4)
          (HahnSeries.C z⁻¹ * formalR ^ 2)) := by
  have hprod : Finset.prod (Finset.range N) (fun m : Nat =>
        (1 : HahnSeries Int K) +
          (HahnSeries.C z⁻¹ * formalR ^ 2) * formalR ^ (4 * m)) =
      Finset.prod (Finset.range N) (fun m : Nat =>
        (1 : HahnSeries Int K) +
          (HahnSeries.C z⁻¹ * formalR ^ 2) * (formalR ^ 4) ^ m) := by
    apply Finset.prod_congr rfl
    intro m hm
    rw [pow_mul]
  rw [hprod]
  exact LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinomialTheoremChoose
    (K := HahnSeries Int K) N (formalR ^ 4) (HahnSeries.C z⁻¹ * formalR ^ 2)

theorem alignedThirdProduct_expand (N : Nat) :
    Finset.prod (Finset.range N) (fun m : Nat =>
        (1 : HahnSeries Int K) - formalR ^ (4 * (m + 1))) =
      Finset.sum (Finset.range (N + 1)) (fun k : Nat =>
        LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinoTermC
          (K := HahnSeries Int K) N k (formalR ^ 4)
          (-(formalR ^ 4))) := by
  have hprod : Finset.prod (Finset.range N) (fun m : Nat =>
        (1 : HahnSeries Int K) - formalR ^ (4 * (m + 1))) =
      Finset.prod (Finset.range N) (fun m : Nat =>
        (1 : HahnSeries Int K) + (-(formalR ^ 4)) * (formalR ^ 4) ^ m) := by
    apply Finset.prod_congr rfl
    intro m hm
    rw [pow_succ]
    ring
  rw [hprod]
  exact LeanFormal.IUT.XiFPaper.QBinomialCommRing.qBinomialTheoremChoose
    (K := HahnSeries Int K) N (formalR ^ 4) (-(formalR ^ 4))

end LeanFormal.IUT.XiFPaper.JacobiAlignedExpansion
