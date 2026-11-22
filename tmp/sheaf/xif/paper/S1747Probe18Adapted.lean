import tmp.sheaf.xif.paper.S1747FiniteEtaleMonoSplitActual

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Finset

namespace S1747

variable {K : Type} [Field K]

#check @Mono.right_cancellation
#check @CategoryTheory.Mono

example (hsplit : FiniteEtaleSplit K)
    {X Y : (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ} (i : X ⟶ Y) [Mono i] :
    True := by
  let A := X.unop
  let B := Y.unop
  let φ : B.obj →ₐ[K] A.obj := i.unop.hom.hom
  have hφ : ∀ (T : Type) [CommRing T] [Algebra K T] [Module.Finite K T] [Algebra.Etale K T]
      (g h : A.obj →ₐ[K] T), g.comp φ = h.comp φ → g = h := by
    intro T _ _ _ _ g h hgh
    let W : (CommAlgCat.FiniteEtale.{0} K)ᵒᵖ := Opposite.op (CommAlgCat.FiniteEtale.of K T)
    let f : W ⟶ X := Quiver.Hom.op (ObjectProperty.homMk (CommAlgCat.ofHom g))
    let f' : W ⟶ X := Quiver.Hom.op (ObjectProperty.homMk (CommAlgCat.ofHom h))
    have hcomp : f = f' := by
      apply Mono.right_cancellation (f := i) f f'
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      apply CommAlgCat.hom_ext
      ext x
      exact AlgHom.congr_fun hgh x
    have := congrArg (fun k => k.unop.hom.hom) hcomp
    simpa [f, f'] using this
  trivial

end S1747
