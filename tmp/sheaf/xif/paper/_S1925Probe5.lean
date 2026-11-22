import Mathlib.RingTheory.MvPolynomial.Homogeneous

open MvPolynomial

noncomputable section
set_option maxHeartbeats 1000000

namespace ProbeH

variable {K : Type} [Field K]

#check @MvPolynomial.isHomogeneous_X
#check @MvPolynomial.isHomogeneous_C
#check @MvPolynomial.isHomogeneous_C_mul_X_pow
#check @MvPolynomial.IsHomogeneous.mul
#check @MvPolynomial.IsHomogeneous.sub
#check @MvPolynomial.IsHomogeneous.add
#check @MvPolynomial.IsHomogeneous.pow

def Wang : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
    (MvPolynomial.X 0 ^ 3 + (MvPolynomial.C (61 / 64 : K) * MvPolynomial.X 0 ^ 2 *
      MvPolynomial.X 2 + MvPolynomial.C (-125 / 64 : K) * MvPolynomial.X 0 *
        MvPolynomial.X 2 ^ 2))

example : Wang.IsHomogeneous 3 := by
  unfold Wang
  have hX : ∀ i : Fin 3, (MvPolynomial.X i : MvPolynomial (Fin 3) K).IsHomogeneous 1 :=
    fun i => MvPolynomial.isHomogeneous_X i
  have h1 : (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 :
      MvPolynomial (Fin 3) K).IsHomogeneous 3 := by
    simpa using (hX 1).pow 2 |>.mul (hX 2)
  have h2 : (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 3) K).IsHomogeneous 3 := by
    simpa using (hX 0).pow 3
  have h3 : (MvPolynomial.C (61 / 64 : K) * MvPolynomial.X 0 ^ 2 *
      MvPolynomial.X 2 : MvPolynomial (Fin 3) K).IsHomogeneous 3 :=
    ((MvPolynomial.isHomogeneous_C (61 / 64 : K)).mul ((hX 0).pow 2)).mul (hX 2)
  have h4 : (MvPolynomial.C (-125 / 64 : K) * MvPolynomial.X 0 *
      MvPolynomial.X 2 ^ 2 : MvPolynomial (Fin 3) K).IsHomogeneous 3 :=
    ((MvPolynomial.isHomogeneous_C (-125 / 64 : K)).mul (hX 0)).mul ((hX 2).pow 2)
  exact h1.sub (h2.add (h3.add h4))

end ProbeH
