import LeanFormal.IUT.IUTII.Kummer.AlgebraicClosureKummerRoots
import LeanFormal.IUT.IUTII.Kummer.AbsoluteKummerInjection

/-!
# ShehddKummerRootsConsumerActual — Kummer roots / absolute-Galois fixed points consumer

STEP 0 prior-art (reuse only; A475 search: algebraic closure Kummer roots found):
* IUTII/Kummer/AlgebraicClosureKummerRoots.lean:
  exists_root_algebraicClosure (n-th root in the algebraic closure),
  fixed_by_absoluteGalois_mem_base (absolute-Galois fixed points lie in the base);
* IUTII/Kummer/AbsoluteKummerInjection.lean: chosenRoot + chosenRoot_spec.

This file packages the root-existence, chosen-root and fixed-point facts as one consumer
for the absolute Kummer layer.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddKummerRootsConsumerActual

open LeanFormal.IUT

variable {K : Type*} [Field K]

/-- **PROVED consumer:** every unit of the base has an n-th root in the algebraic
closure, and the chosen root satisfies the defining power relation. -/
theorem kummer_root_and_chosenRoot_consumer (n : ℕ) [NeZero n] (a : Kˣ) :
    (∃ α : (AlgebraicClosure K)ˣ,
        α ^ n = Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a) ∧
      AbsoluteKummerInjection.chosenRoot (K := K) (n := n) a ^ n =
        Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a :=
  ⟨exists_root_algebraicClosure n a,
    AbsoluteKummerInjection.chosenRoot_spec a⟩

/-- **PROVED consumer:** absolute-Galois fixed points in characteristic zero lie in the
base field image. -/
theorem absoluteGalois_fixed_mem_base_consumer [CharZero K] (x : AlgebraicClosure K)
    (hx : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ x = x) :
    x ∈ Set.range (algebraMap K (AlgebraicClosure K)) :=
  fixed_by_absoluteGalois_mem_base x hx

/-- Row record: reused Kummer-root assets vs the consumer interface. -/
def kummerRootsRows : List (String × String × String) :=
  [ ("n-th root existence in algebraic closure", "REUSED PROVED", "exists_root_algebraicClosure")
  , ("chosen root power spec", "REUSED PROVED", "AbsoluteKummerInjection.chosenRoot_spec")
  , ("absolute-Galois fixed points lie in base", "REUSED PROVED", "fixed_by_absoluteGalois_mem_base")
  , ("consumer bundle", "COMPOSED PROVED", "kummer_root_and_chosenRoot_consumer, absoluteGalois_fixed_mem_base_consumer")
  , ("Kummer map / roots-of-unity fixedness conditions", "REUSED/NAMED", "AbsoluteKummerInjection.RootsOfUnityFixed (hypothesis form)") ]

theorem kummerRootsRows_length : kummerRootsRows.length = 5 := rfl

#check kummer_root_and_chosenRoot_consumer
#check absoluteGalois_fixed_mem_base_consumer
#check kummerRootsRows_length

end LeanFormal.IUT.XiFPaper.ShehddKummerRootsConsumerActual
end
