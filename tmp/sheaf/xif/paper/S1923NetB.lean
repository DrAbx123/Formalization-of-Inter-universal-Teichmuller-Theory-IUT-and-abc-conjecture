import tmp.sheaf.xif.paper.S1923NetA
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation

universe u
namespace S1923Net
open IsEllipticNet
variable {R : Type u} [CommRing R] (W : ℤ → R)

lemma atom_mul_atomRel (a b c d e f : ℤ) {u v w x y z : R} (h : u + v + w + x + y + z = 0) :
    (u + v) * atom W a b * atomRel W c d e f - (u + w) * atom W a c * atomRel W b d e f +
    (u + x) * atom W a d * atomRel W b c e f - (u + y) * atom W a e * atomRel W b c d f +
    (u + z) * atom W a f * atomRel W b c d e + (v + w) * atom W b c * atomRel W a d e f -
    (v + x) * atom W b d * atomRel W a c e f + (v + y) * atom W b e * atomRel W a c d f -
    (v + z) * atom W b f * atomRel W a c d e + (w + x) * atom W c d * atomRel W a b e f -
    (w + y) * atom W c e * atomRel W a b d f + (w + z) * atom W c f * atomRel W a b d e +
    (x + y) * atom W d e * atomRel W a b c f - (x + z) * atom W d f * atomRel W a b c e +
    (y + z) * atom W e f * atomRel W a b c d = 0 := by
  simp only [atomRel]
  grind only

variable {W} in
lemma atomRel_perm (odd : W.Odd) (σ : Equiv.Perm <| Fin 4) (a b c d : ℤ) :
    σ.sign • atomRel W (![a, b, c, d] <| σ 0) (![a, b, c, d] <| σ 1) (![a, b, c, d] <| σ 2)
      (![a, b, c, d] <| σ 3) = atomRel W a b c d := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap σ x y _ _ => fin_cases x <;> fin_cases y <;> simp [Equiv.swap_apply_def] <;>
      grind only [neg_atomRel₁₂, neg_atomRel₂₃, neg_atomRel₃₄, smul_neg]

end S1923Net
