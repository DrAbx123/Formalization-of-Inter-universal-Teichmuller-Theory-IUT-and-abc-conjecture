import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# S2510: lifting `F'`-automorphisms of the actual 5-division field to the
absolute Galois group

The actual odd 5-division field `S2057FiveDivisionField` of S2057 is the
splitting field over `F' = S1720Field` of the odd 5-division polynomial
`S2057Psi5F`.  In this file we

* embed it into the algebraic closure `AlgebraicClosure S1720Field` using
  `Polynomial.SplittingField.lift` (the closure is algebraically closed, so
  `S2057Psi5F` splits there), and realise the image as the intermediate field
  `S2510L` (with underlying subalgebra `S2510Subalgebra`);
* identify the splitting field with its image by the `F'`-algebra equivalence
  `S2510Equiv`;
* prove that restriction of absolute Galois automorphisms
  `Gal(Fbar/F') -> Gal(L/F')` is surjective (`S2510Restrict_surjective`),
  using that `L/F'` is finite Galois (S2057) and that the algebraic closure
  is normal over `F'` (an algebraic closure is normal), together with
  `AlgEquiv.restrictNormalHom_surjective`;
* deduce that every `F'`-automorphism of `L` is the restriction of an element
  of the literal absolute Galois group `S1725AbsoluteGalois`
  (`S2510_exists_lift`).

No `sorry`, no `axiom`, no placeholder is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2510AbsoluteLiftActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

/-- The `F'`-algebra embedding of the actual odd 5-division field into the
algebraic closure.  It is the splitting-field lift of `S2057Psi5F`, which
splits in the algebraically closed field `AlgebraicClosure S1720Field`. -/
noncomputable def S2510Embedding :
    S2057FiveDivisionField →ₐ[S1720Field] AlgebraicClosure S1720Field :=
  Polynomial.SplittingField.lift (f := S2057Psi5F) (L := AlgebraicClosure S1720Field)
    (IsAlgClosed.splits
      (S2057Psi5F.map (algebraMap S1720Field (AlgebraicClosure S1720Field))))

/-- The image of the actual 5-division field in the algebraic closure, as an
intermediate field of `AlgebraicClosure S1720Field / S1720Field`. -/
noncomputable abbrev S2510L :
    IntermediateField S1720Field (AlgebraicClosure S1720Field) :=
  S2510Embedding.fieldRange

/-- The same image, viewed as a subalgebra of the algebraic closure. -/
noncomputable abbrev S2510Subalgebra :
    Subalgebra S1720Field (AlgebraicClosure S1720Field) :=
  S2510L.toSubalgebra

/-- The actual 5-division field is `F'`-equivariantly isomorphic to its image
`S2510L` in the algebraic closure. -/
noncomputable abbrev S2510Equiv :
    S2057FiveDivisionField ≃ₐ[S1720Field] S2510L :=
  S2510Embedding.equivFieldRange

@[simp]
lemma S2510Equiv_apply_coe (x : S2057FiveDivisionField) :
    (S2510Equiv x : AlgebraicClosure S1720Field) = S2510Embedding x :=
  AlgHom.equivFieldRange_apply_coe S2510Embedding x

@[simp]
lemma S2510Equiv_symm_apply_coe (y : S2510L) :
    S2510Embedding (S2510Equiv.symm y) = (y : AlgebraicClosure S1720Field) := by
  rw [← S2510Equiv_apply_coe, AlgEquiv.apply_symm_apply]

/-- The embedding of the actual 5-division field into the algebraic closure is
injective. -/
theorem S2510Embedding_injective : Function.Injective S2510Embedding := by
  intro x y h
  exact S2510Equiv.injective (Subtype.ext (by simpa using h))

/-- `S2510L` is a Galois extension of `F'`, being isomorphic to the finite
Galois splitting field `S2057FiveDivisionField`. -/
instance S2510L_isGalois : IsGalois S1720Field S2510L :=
  IsGalois.of_algEquiv S2510Equiv

/-- Restriction of an absolute Galois automorphism to the image of the actual
5-division field, transported back to `S2057FiveDivisionField` along
`S2510Equiv`.  Concretely,
`S2510Restrict σ = S2510Equiv.symm ∘ σ|S2510L ∘ S2510Equiv`. -/
noncomputable def S2510Restrict (σ : S1725AbsoluteGalois) :
    S2057FiveDivisionField ≃ₐ[S1720Field] S2057FiveDivisionField :=
  S2510Equiv.trans
    ((AlgEquiv.restrictNormalHom (F := S1720Field)
        (K₁ := AlgebraicClosure S1720Field) (E := S2510L) σ).trans
      S2510Equiv.symm)

/-- Under `S2510Embedding`, `S2510Restrict σ` is the restriction of `σ` to
the image of the 5-division field. -/
theorem S2510Restrict_apply (σ : S1725AbsoluteGalois) (x : S2057FiveDivisionField) :
    S2510Embedding (S2510Restrict σ x) = σ (S2510Embedding x) := by
  have h : ((AlgEquiv.restrictNormalHom (F := S1720Field)
        (K₁ := AlgebraicClosure S1720Field) (E := S2510L) σ) (S2510Equiv x) :
      AlgebraicClosure S1720Field) = σ (S2510Embedding x) := by
    simpa [S2510Equiv_apply_coe, IntermediateField.algebraMap_apply] using
      (AlgEquiv.restrictNormalHom_apply (F := S1720Field)
        (K₁ := AlgebraicClosure S1720Field) S2510L σ (S2510Equiv x))
  show S2510Embedding (S2510Equiv.symm
    ((AlgEquiv.restrictNormalHom (F := S1720Field)
      (K₁ := AlgebraicClosure S1720Field) (E := S2510L) σ) (S2510Equiv x))) =
      σ (S2510Embedding x)
  rw [S2510Equiv_symm_apply_coe]
  exact h

/-- An automorphism of the 5-division field is determined by the corresponding
automorphism of the image field. -/
theorem S2510Restrict_eq_of_restrictNormalHom
    (σ : S1725AbsoluteGalois)
    (χ : S2057FiveDivisionField ≃ₐ[S1720Field] S2057FiveDivisionField)
    (hσ : AlgEquiv.restrictNormalHom (F := S1720Field)
        (K₁ := AlgebraicClosure S1720Field) (E := S2510L) σ =
      (S2510Equiv.symm.trans χ).trans S2510Equiv) :
    S2510Restrict σ = χ := by
  ext x
  show S2510Equiv.symm ((AlgEquiv.restrictNormalHom (F := S1720Field)
    (K₁ := AlgebraicClosure S1720Field) (E := S2510L) σ) (S2510Equiv x)) = χ x
  rw [hσ]
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]

/-- The restriction map `Gal(Fbar/F') -> Gal(L/F')` is surjective: every
`F'`-automorphism of the actual 5-division field comes from an element of the
literal absolute Galois group `S1725AbsoluteGalois`. -/
theorem S2510Restrict_surjective : Function.Surjective S2510Restrict := by
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := S1720Field)
      (K₁ := AlgebraicClosure S1720Field) (E := S2510L) :
      S1725AbsoluteGalois → S2510L ≃ₐ[S1720Field] S2510L) :=
    AlgEquiv.restrictNormalHom_surjective (F := S1720Field) (K₁ := S2510L)
      (E := AlgebraicClosure S1720Field)
  intro χ
  obtain ⟨σ, hσ⟩ := hsurj ((S2510Equiv.symm.trans χ).trans S2510Equiv)
  exact ⟨σ, S2510Restrict_eq_of_restrictNormalHom σ χ hσ⟩

/-- Every `F'`-automorphism of the actual 5-division field lifts to an element of
the literal absolute Galois group `S1725AbsoluteGalois`, compatibly with the
embedding of the field into the algebraic closure. -/
theorem S2510_exists_lift
    (χ : S2057FiveDivisionField ≃ₐ[S1720Field] S2057FiveDivisionField) :
    ∃ σ : S1725AbsoluteGalois, ∀ x : S2057FiveDivisionField,
      σ (S2510Embedding x) = S2510Embedding (χ x) := by
  obtain ⟨σ, hσ⟩ := S2510Restrict_surjective χ
  refine ⟨σ, fun x => ?_⟩
  calc σ (S2510Embedding x)
      = S2510Embedding (S2510Restrict σ x) := (S2510Restrict_apply σ x).symm
    _ = S2510Embedding (χ x) := by rw [hσ]

end LeanFormal.IUT.XiFPaper.S2510AbsoluteLiftActual

end
