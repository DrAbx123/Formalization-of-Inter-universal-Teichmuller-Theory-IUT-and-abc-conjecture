import tmp.sheaf.xif.paper.S3128SurjHa0Actual
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128SurjHtermActual

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]
variable {A : Type} [CommRing A] [MulSemiringAction G A]

/-- P = product of (g • f)^n over g ≠ 1. -/
noncomputable def S3128SurjP (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (A : Type) [CommRing A] [MulSemiringAction G A] (f : A) (n : Nat) : A :=
  ((Finset.univ : Finset G).erase 1).prod (fun g => (g • f) ^ n)

/-- b = a0 * P. -/
noncomputable def S3128SurjB (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (A : Type) [CommRing A] [MulSemiringAction G A] (a0 f : A) (n : Nat) : A :=
  a0 * S3128SurjP G A f n

/-- h • b expands to (h • a0) times the h-shifted product. -/
theorem S3128Surj_hb (a0 f : A) (n : Nat) (h : G) :
    h • S3128SurjB (G := G) (A := A) a0 f n =
      (h • a0) * ((Finset.univ : Finset G).erase 1).prod
        (fun g => ((h * g) • f) ^ n) := by
  rw [S3128SurjB, S3128SurjP, smul_mul']
  congr 1
  change (MulSemiringAction.toRingHom G A h)
      (((Finset.univ : Finset G).erase 1).prod (fun g => (g • f) ^ n)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro g hg
  rw [map_pow]
  congr 1
  rw [mul_smul]
  rfl

#check S3128SurjP
#check S3128SurjB
#check S3128Surj_hb

end LeanFormal.IUT.XiFPaper.S3128SurjHtermActual
end