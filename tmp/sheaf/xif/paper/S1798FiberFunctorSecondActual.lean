import tmp.sheaf.xif.paper.S1769FiberFunctorFieldsActual
import tmp.sheaf.xif.paper.S1745FiniteEtaleLimitsActual
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF / S1798 (second actual attempt)

# S1798 -- finite coproducts of the geometric fibre functor, and the remaining fields

Target: the six fields of

  `PreGaloisCategory.FiberFunctor (CommAlgCat.FiniteEtale.fiber K (AlgebraicClosure K))`.

This file is the second actual attack on S1793's remaining hypothesis (G4)--(G6).  It builds
on the first actual reduction in `S1769FiberFunctorFieldsActual`, which proves fields 1
(`preservesTerminalObjects`) and 6 (`reflectsIsos`) unconditionally (relative to the ambient
`[PreGaloisCategory (FiniteEtale K)^op]` instance), and reduces fields 2--5 to four exact
statements about Mathlib's base change functor

  `CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K) : FiniteEtale K ⥤ FiniteEtale Kbar`.

The new result of this file is an unconditional proof of

  `S1798FiberFunctor.bc_preservesFiniteProducts : PreservesFiniteProducts (baseChange K Kbar)`,

hence (through S1769's reduction) of **field 3**,

  `preservesFiniteCoproducts (fiber K Kbar) : PreservesFiniteCoproducts (fiber K Kbar)`.

The proof is the concrete product computation
`Kbar (x)_K (prod_i A_i) ~= prod_i (Kbar (x)_K A_i)`: the canonical Pi fan in
`FiniteEtale K` is a limit (proved here directly, `piFan_isLimit_finiteEtale`), its image
under base change is identified with the canonical Pi fan in `FiniteEtale Kbar` using
`Algebra.TensorProduct.piRight`, and the two fans are compared by `Fan.ext`.  No categorical
transport through the ambient `CommAlgCat` is needed.

## Status of the six fields

| field | content | status |
|---|---|---|
| 1 | preservesTerminalObjects | proved (S1769) |
| 2 | preservesPullbacks | exact missing: `BCPreservesPullbacks` |
| 3 | preservesFiniteCoproducts | **proved here** |
| 4 | preservesEpis | exact missing: `BCPreservesEpis` |
| 5 | preservesQuotientsByFiniteGroups | exact missing: `BCPreservesQuotients` |
| 6 | reflectsIsos | proved (S1769) |

The three missing statements are `Prop`-valued definitions copied verbatim from S1769; they
are not weakened and no `sorry` is used.  `fiberFunctorWithMissing` assembles the full
`FiberFunctor` from them together with the two proved fields and field 3.

## Verification

`lake env lean` on this file exits 0; the olean is written to the standard build tree.
No `sorry`, `admit`, new axiom or changed target occurs.  Every declaration below depends
only on `propext`, `Classical.choice` and `Quot.sound` (axiom audit at the end).

## References

* S1769: `tmp/sheaf/xif/paper/S1769FiberFunctorFieldsActual.lean`
* S1745: `tmp/sheaf/xif/paper/S1745FiniteEtaleLimitsActual.lean`
* Mathlib: `Mathlib/RingTheory/TensorProduct/Pi.lean` (`Algebra.TensorProduct.piRight`),
  `Mathlib/RingTheory/Etale/Finite.lean` (`FiniteEtale.baseChange`, fiber).
-/
noncomputable section
set_option linter.defProp false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1798FiberFunctor

open S1769

variable (K : Type) [Field K]

/-- The algebraic closure, used as the geometric point. -/
abbrev Om : Type := AlgebraicClosure K

/-- Mathlib's base change functor `A |-> Kbar (x)_K A`, at the exact abbreviation used by
S1769. -/
abbrev bc : CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (Om K) :=
  S1769.bc K

/-! ## 1. The canonical Pi fan in `FiniteEtale R` is a limit

This is the same computation as S1745's `piFan_isLimit`, transported to the full subcategory
`FiniteEtale R`.  We prove it directly (rather than by reflecting the ambient limit) so that
the point is definitionally the Pi algebra; this is what makes the product comparison below
transparent. -/

/-- The canonical Pi fan of a finite family of finite etale `R`-algebras is a limit fan. -/
def piFan_isLimit_finiteEtale (R : Type) [CommRing R] (n : ℕ)
    (A : Fin n → CommAlgCat.FiniteEtale.{0} R) :
    IsLimit (Fan.mk
      (CommAlgCat.FiniteEtale.of R (∀ i, (A i).obj))
      (fun i => CommAlgCat.FiniteEtale.ofHom
        (Pi.evalAlgHom R (fun i => (A i).obj) i))) := by
  let P : CommAlgCat.FiniteEtale.{0} R :=
    CommAlgCat.FiniteEtale.of R (∀ i, (A i).obj)
  let π : ∀ i, P ⟶ A i := fun i =>
    CommAlgCat.FiniteEtale.ofHom (Pi.evalAlgHom R (fun i => (A i).obj) i)
  refine Fan.IsLimit.mk (Fan.mk P π)
    (fun s => CommAlgCat.FiniteEtale.ofHom (AlgHom.pi (fun i => (s.proj i).hom.hom)))
    ?_ ?_
  · intro s i
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    rfl
  · intro s m hm
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    funext i
    have h := congrArg (fun (g : s.pt ⟶ A i) => g.hom.hom x) (hm i)
    change (m.hom.hom x) i = (s.proj i).hom.hom x at h
    exact h

/-! ## 2. Base change preserves finite products -/

/-- The projection compatibility of `Algebra.TensorProduct.piRight`: the `i`-th component
of the base-changed product is the base change of the `i`-th projection. -/
theorem piRight_comp_eval (n : ℕ) (A : Fin n → Type)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    [∀ i, Module.Finite K (A i)] [∀ i, Algebra.Etale K (A i)] (i : Fin n) :
    (Pi.evalAlgHom (Om K) (fun i => Om K ⊗[K] A i) i).comp
        (Algebra.TensorProduct.piRight K (Om K) (Om K) A) =
      Algebra.TensorProduct.map (AlgHom.id (Om K) (Om K)) (Pi.evalAlgHom K A i) := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.piRight_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

/-- **Base change preserves the canonical finite product cone.** -/
theorem bc_preservesLimit_fin (n : ℕ)
    (f : Fin n → CommAlgCat.FiniteEtale.{0} K) :
    PreservesLimit (Discrete.functor f) (bc K) := by
  let A : Fin n → Type := fun i => (f i).obj
  let P : CommAlgCat.FiniteEtale.{0} K := CommAlgCat.FiniteEtale.of K (∀ i, A i)
  let π : ∀ i, P ⟶ f i := fun i =>
    CommAlgCat.FiniteEtale.ofHom (Pi.evalAlgHom K A i)
  have hP : IsLimit (Fan.mk P π) := piFan_isLimit_finiteEtale K n f
  let Q : CommAlgCat.FiniteEtale.{0} (Om K) :=
    CommAlgCat.FiniteEtale.of (Om K) (∀ i, Om K ⊗[K] A i)
  let q : ∀ i, Q ⟶ (bc K).obj (f i) := fun i =>
    CommAlgCat.FiniteEtale.ofHom (Pi.evalAlgHom (Om K) (fun i => Om K ⊗[K] A i) i)
  have hQ : IsLimit (Fan.mk Q q) :=
    piFan_isLimit_finiteEtale (Om K) n (fun i => (bc K).obj (f i))
  let e : (bc K).obj P ≅ Q :=
    CommAlgCat.FiniteEtale.isoMk
      (Algebra.TensorProduct.piRight K (Om K) (Om K) A)
  have hfac (i : Fin n) : (bc K).map (π i) = e.hom ≫ q i := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    change (Algebra.TensorProduct.map (AlgHom.id (Om K) (Om K)) (Pi.evalAlgHom K A i)) x =
      ((Pi.evalAlgHom (Om K) (fun i => Om K ⊗[K] A i) i).comp
        (Algebra.TensorProduct.piRight K (Om K) (Om K) A).toAlgHom) x
    exact (congrArg (fun g => g x) (piRight_comp_eval K n A i)).symm
  have hfan : Fan.mk ((bc K).obj P) (fun i => (bc K).map (π i)) ≅ Fan.mk Q q :=
    Fan.ext e hfac
  have hlim : IsLimit (Fan.mk ((bc K).obj P) (fun i => (bc K).map (π i))) :=
    IsLimit.ofIsoLimit hQ hfan.symm
  have hcone : IsLimit ((bc K).mapCone (Fan.mk P π)) :=
    (isLimitMapConeFanMkEquiv (bc K) (fun i => f i) π).symm hlim
  exact preservesLimit_of_preserves_limit_cone hP hcone

/-- **Mathlib's base change functor preserves finite products.** -/
theorem bc_preservesFiniteProducts : PreservesFiniteProducts (bc K) where
  preserves n := by
    refine ⟨fun {J} => ?_⟩
    let f : Fin n → CommAlgCat.FiniteEtale.{0} K := fun i => J.obj (Discrete.mk i)
    have hdiag : J ≅ Discrete.functor f := Discrete.natIsoFunctor
    haveI : PreservesLimit (Discrete.functor f) (bc K) := bc_preservesLimit_fin K n f
    exact preservesLimit_of_iso_diagram (bc K) hdiag.symm

/-- **Field 3 of the fibre functor: finite coproducts.**  This is S1769's reduction applied to
the unconditional product preservation above. -/
theorem preservesFiniteCoproducts [PreGaloisCategory (S1769.C K)] :
    PreservesFiniteCoproducts (S1769.F K) :=
  S1769.preservesFiniteCoproducts_of K (bc_preservesFiniteProducts K)

/-! ## 3. The remaining three fields are exactly the S1769 base-change conditions -/

/-- The exact remaining statement for field 2, copied verbatim from S1769. -/
abbrev MissingPullbacks : Prop := S1769.BCPreservesPullbacks K

/-- The exact remaining statement for field 4, copied verbatim from S1769. -/
abbrev MissingEpis : Prop := S1769.BCPreservesEpis K

/-- The exact remaining statement for field 5, copied verbatim from S1769. -/
abbrev MissingQuotients : Prop := S1769.BCPreservesQuotients K

/-- **The fibre functor from the three remaining base-change conditions.**

Fields 1 and 6 are the unconditional S1769 theorems; field 3 is
`preservesFiniteCoproducts` above; fields 2, 4 and 5 are the exact missing inputs. -/
@[implicit_reducible]
def fiberFunctorWithMissing [PreGaloisCategory (S1769.C K)]
    (hPull : MissingPullbacks K) (hEpi : MissingEpis K) (hQuot : MissingQuotients K) :
    PreGaloisCategory.FiberFunctor (S1769.F K) :=
  S1769.fiberFunctorOf K hPull (bc_preservesFiniteProducts K) hEpi hQuot

/-- The missing inputs are not axioms: they are parameters of the conditional assembly. -/
theorem missing_are_hypotheses [PreGaloisCategory (S1769.C K)]
    (hPull : MissingPullbacks K) (hEpi : MissingEpis K) (hQuot : MissingQuotients K) :
    Nonempty (PreGaloisCategory.FiberFunctor (S1769.F K)) :=
  ⟨fiberFunctorWithMissing K hPull hEpi hQuot⟩

/-! ## 4. Status record -/

/-- The six field statuses of the fibre functor. -/
structure FieldStatus where
  /-- Field 1, `preservesTerminalObjects`. -/
  preservesTerminalObjects : Bool
  /-- Field 2, `preservesPullbacks`. -/
  preservesPullbacks : Bool
  /-- Field 3, `preservesFiniteCoproducts`. -/
  preservesFiniteCoproducts : Bool
  /-- Field 4, `preservesEpis`. -/
  preservesEpis : Bool
  /-- Field 5, `preservesQuotientsByFiniteGroups`. -/
  preservesQuotientsByFiniteGroups : Bool
  /-- Field 6, `reflectsIsos`. -/
  reflectsIsos : Bool

/-- Fields 1, 3 and 6 are proved; fields 2, 4 and 5 are the exact missing Props. -/
def fieldStatus : FieldStatus where
  preservesTerminalObjects := true
  preservesPullbacks := false
  preservesFiniteCoproducts := true
  preservesEpis := false
  preservesQuotientsByFiniteGroups := false
  reflectsIsos := true

/-- The exact first missing statement in the field order of the class: field 2. -/
def firstMissing : String :=
  "preservesPullbacks: S1769.BCPreservesPullbacks K (base change preserves pushouts)"

/-! ## 5. Consistency checks -/

/-- Field 3 is exactly the class field of Mathlib's `FiberFunctor`. -/
example [PreGaloisCategory (S1769.C K)] :
    PreservesFiniteCoproducts (S1769.F K) := preservesFiniteCoproducts K

/-! ## 6. Axiom audit -/

#print axioms S1798FiberFunctor.piFan_isLimit_finiteEtale
#print axioms S1798FiberFunctor.piRight_comp_eval
#print axioms S1798FiberFunctor.bc_preservesLimit_fin
#print axioms S1798FiberFunctor.bc_preservesFiniteProducts
#print axioms S1798FiberFunctor.preservesFiniteCoproducts
#print axioms S1798FiberFunctor.fiberFunctorWithMissing
#print axioms S1798FiberFunctor.missing_are_hypotheses

end S1798FiberFunctor
