import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerInjection

/-!
# ShehddChosenRootValChainActual — chosen Kummer root value chain

New chain consequence of the compiled `chosenRoot_spec` at the field level: the chosen
root's underlying field element is an actual n-th root of the base unit image, and any
absolute-Galois-fixed root lies in the base image.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddChosenRootValChainActual

open LeanFormal.IUT

variable {K : Type*} [Field K] [CharZero K] {n : Nat} [NeZero n]

/-- **PROVED chain:** the chosen Kummer root's field element is an n-th root of the
base unit image. -/
theorem chosenRoot_val_pow (a : Kˣ) :
    (((AbsoluteKummerInjection.chosenRoot (K := K) (n := n) a :
        (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ^ n =
      algebraMap K (AlgebraicClosure K) (a : K) := by
  have h := congrArg (fun u : (AlgebraicClosure K)ˣ => (u : AlgebraicClosure K))
    (AbsoluteKummerInjection.chosenRoot_spec (K := K) (n := n) a)
  simpa using h

/-- **PROVED chain:** a root fixed by the whole absolute Galois group is a base element
(and a unit root of a base unit is therefore determined by the base value). -/
theorem root_fixed_mem_base_chain (x : AlgebraicClosure K)
    (hx : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ x = x) :
    x ∈ Set.range (algebraMap K (AlgebraicClosure K)) :=
  fixed_by_absoluteGalois_mem_base x hx

end LeanFormal.IUT.XiFPaper.ShehddChosenRootValChainActual
end
