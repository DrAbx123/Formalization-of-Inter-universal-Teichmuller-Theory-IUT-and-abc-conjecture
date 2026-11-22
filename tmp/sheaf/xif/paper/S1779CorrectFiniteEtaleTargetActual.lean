import tmp.sheaf.xif.paper.S1753OrbicurveEtalePiAssemblyActual
import tmp.sheaf.xif.paper.S1750FunctionFieldCoversActual
import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.Algebra.Category.CommAlgCat.Monoidal
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# S1779: the corrected finite-etale target for the S1753 transport

## The error in S1753

S1753 transports the four fields of `OrbicurveEtaleFundamentalGroup` from
the algebra category

  `S1753Alg = FiniteEtaleAlg S1753K`,  `S1753K = S1726K = F'`,

i.e. from finite etale algebras over the **base field** F'.  This is the
wrong domain.  Finite etale covers of the affine curve E' minus O correspond
to finite etale algebras over its coordinate ring

  `R' = S1726CoordinateRing = F'[x,y]/(y^2 - x^3 - (61/64)x^2 + (125/64)x)`,

equivalently to finite etale covers of `Spec R'`.  Finite etale F'-algebras
are a different category and carry no information about the curve.

## The corrected target

This file uses

  `S1779AlgR = (CommAlgCat.FiniteEtale.{0} R')^op`,

with Mathlib's category structure (objects in `Type 1`, homs in `Type`),
and records the function-field variant

  `S1779AlgK = (CommAlgCat.FiniteEtale.{0} K(E'))^op`.

Here `K(E')` is represented by S1750's actual Mathlib function field of the
affine Weierstrass model.  S1750 uses Mathlib's `Affine.CoordinateRing`
presentation, while S1726 uses the explicit `MvPolynomial (Fin 2)` quotient;
the two coordinate rings are presentations of the same curve but are not
definitionally equal, and their identification is not formalized in this
file.  The R' target is independent of that identification and is the one
used by the route below.

The old target is defined only as `S1779OldTarget` for the audit theorem
`S1779OldTarget_eq_S1753Alg`; it is **not** used by any construction below.

## What is proved unconditionally

* `(CommAlgCat.FiniteEtale R')^op` has a terminal object, pullbacks and
  finite coproducts.  The closure under finite products and tensor products
  is the general-ring form of S1745; the proofs are ported here from
  `[Field K]` to `[CommRing R]` and are kernel checked.
* The corrected target assembly: from
  (i) a `Category.{0,1}` on the actual cover type together with an
  equivalence to `S1779AlgR`, and
  (ii) a `PreGaloisCategory S1779AlgR` and a `FiberFunctor` for the actual
  geometric point based at (0,0) of `Spec R'`,
  the four target fields are constructed by the genuine transport of S1753
  (`S1753PreGaloisCategory`, `S1753GaloisCategoryOfFiber`,
  `S1753FiberFunctorTransport`).
* The exact remaining algebra-side fields for R' are isolated as
  `S1779QuotientsMissing` (G2) and `S1779MonoMissing` (G3).  The
  terminal/pullback/finite-coproduct fields are discharged, so these two are
  the complete missing content of `PreGaloisCategory S1779AlgR`.
* The geometric fibre functor is Mathlib's genuine
  `CommAlgCat.FiniteEtale.fiber R' Omega` at the separably closed field
  `Omega = AlgebraicClosure F'` with the base point (0,0) of the curve;
  the missing `FiberFunctor` structure on it is
  `S1779FiberFunctorMissing`.

## Why the function-field target is not used as the equivalence

S1750 proves, for the Mathlib coordinate-ring presentation of the same
affine model, that the generic-fibre functor
`(FiniteEtale R)^op -> (FiniteEtale K)^op` is faithful, but its essential
image is only the unramified finite etale `K`-algebras: a finite separable
extension may ramify at a closed point of the affine curve.  Hence an
equivalence with **all** finite etale `K(E')`-algebras is false.  The
`K(E')` category is recorded as the corrected field-side target for the
generic fibre, not as an equivalence with covers.

## Status of S1777

S1777 is still at the probe stage in this checkout (only
`S1777Probe*.lean`; there is no actual S1777 module at the time of writing,
2026-11-01).  The only existing completed affine Spec/Gamma equivalence is
`LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverEquivalenceFinal.specCoverEquivalence`,
stated for `[Field K]`; since R' is not a field it does not apply to R'.
S1777 is expected to supply the affine slice equivalence
`S1779AffineSliceEquivalenceMissing` below.  The corrected route also needs
the cover-to-slice comparison and the hom comparison to the raw cover maps
(S1743/S1733/S1744 R2), so the combined input is stated separately as
`S1779FirstMissing`.  When S1777 lands, its equivalence composes with that
cover-side input; `S1779TargetFields_of_route` consumes the composition
unchanged.

## Honest boundary

No `sorry`, no axiom, no `Shrink`, `ULift` or `PUnit`.  The target
`OrbicurveEtaleFundamentalGroup` is not constructed; this file reduces it to
the exact missing statements above.  The axiom audit at the end checks that
every declaration depends only on `propext`, `Classical.choice` and
`Quot.sound`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual

open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1753OrbicurveEtalePiAssemblyActual
open LeanFormal.IUT.XiFPaper.S1750FunctionFieldCoversActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual

/-! ## 1. The corrected domain: R' and K(E') -/

/-- The old (wrong) base field F' of S1726, kept only for the audit comparison. -/
abbrev S1779K : Type := S1726K

/-- The actual coordinate ring R' = F'[x,y]/(y^2 = x^3 + (61/64)x^2 - (125/64)x)
of the affine curve E' minus O. -/
abbrev S1779R : Type := S1726CoordinateRing

/-- The function field K(E') of the curve, represented by S1750's actual
Mathlib function field `FractionRing (Affine.CoordinateRing E')`.  This is a
presentation of the same function field as `Frac R'`, but the identification
of S1750's `Affine.CoordinateRing` with the explicit `MvPolynomial` quotient
`R'` is not formalized here; the R' target does not depend on it. -/
abbrev S1779FunctionField : Type := S1750FunctionField

/-- The function field is literally the fraction field of S1750's coordinate
ring, which is the Mathlib presentation of R'. -/
theorem S1779FunctionField_eq_fractionRing :
    S1779FunctionField = FractionRing S1750CoordinateRing := rfl

/-- **The corrected target**: finite etale R'-algebras, opposite. -/
abbrev S1779AlgR : Type 1 := (CommAlgCat.FiniteEtale.{0} S1779R)ᵒᵖ

instance S1779AlgR_category : Category.{0, 1} S1779AlgR := inferInstance

/-- The corrected field-side target: finite etale K(E')-algebras, opposite.
This is the generic-fibre side; it is not equivalent to all covers (S1750).
It is recorded for the function-field variant, not used by the R' route. -/
abbrev S1779AlgK : Type 1 := (CommAlgCat.FiniteEtale.{0} S1779FunctionField)ᵒᵖ

instance S1779AlgK_category : Category.{0, 1} S1779AlgK := inferInstance

/-- The **removed** S1753 target: finite etale F'-algebras, opposite.
Recorded only for the audit theorem below; never used by the corrected route. -/
abbrev S1779OldTarget : Type 1 := (CommAlgCat.FiniteEtale.{0} S1779K)ᵒᵖ

/-- The removed target is literally S1753's `S1753Alg`; this machine-checked
theorem identifies the wrong domain without reusing it. -/
theorem S1779OldTarget_eq_S1753Alg : S1779OldTarget = S1753Alg := rfl

/-- A short name for the four target fields, definitionally S1753's structure. -/
abbrev S1779TargetFields : Type 1 := S1753TargetFields


namespace S1779FiniteEtaleClosure

variable {R : Type} [CommRing R]

/-- The opposite of the category of finite etale R-algebras (Galois category of S1739). -/
abbrev FiniteEtaleAlg (R : Type) [CommRing R] : Type 1 := (CommAlgCat.FiniteEtale.{0} R)ᵒᵖ

namespace FiniteEtaleClosure

/-! ### 1. Closedness under isomorphisms -/

instance : (CommAlgCat.finiteEtale R : ObjectProperty (CommAlgCat.{0} R)).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro X Y e ⟨hf, he⟩
    exact ⟨Module.Finite.equiv (CommAlgCat.algEquivOfIso e).toLinearEquiv,
      Algebra.Etale.of_equiv (CommAlgCat.algEquivOfIso e)⟩

/-! ### 2. Finite products: the Pi algebra -/

/-- The Pi-algebra is the categorical product in CommAlgCat R. -/
noncomputable def piFan (J : Type) (A : J → CommAlgCat.{0} R) : Fan A :=
  Fan.mk (CommAlgCat.of R (∀ j, (A j : Type))) fun j =>
    CommAlgCat.ofHom (Pi.evalAlgHom R (fun j => (A j : Type)) j)

lemma piFan_proj_apply (J : Type) (A : J → CommAlgCat.{0} R) (j : J)
    (x : (piFan J A).pt) : ((piFan J A).proj j).hom x = x j := rfl

noncomputable def piFan_isLimit (J : Type) (A : J → CommAlgCat.{0} R) : IsLimit (piFan J A) := by
  refine Fan.IsLimit.mk _ (fun s => CommAlgCat.ofHom (AlgHom.pi fun j => (s.proj j).hom)) ?_ ?_
  · intro s j
    ext x
    rfl
  · intro s m hm
    ext x
    funext j
    have h := congrArg (fun f => (f : s.pt ⟶ A j).hom x) (hm j)
    simp only [CommAlgCat.hom_comp, AlgHom.comp_apply] at h
    rw [piFan_proj_apply] at h
    exact h

theorem finiteEtale_piFan_pt (J : Type) [Fintype J] (A : J → CommAlgCat.{0} R)
    (hA : ∀ j, (CommAlgCat.finiteEtale R) (A j)) :
    (CommAlgCat.finiteEtale R) (piFan J A).pt := by
  haveI : ∀ j, Module.Finite R (A j : Type) := fun j => (hA j).1
  haveI : ∀ j, Algebra.Etale R (A j : Type) := fun j => (hA j).2
  refine ⟨?_, ?_⟩
  · show Module.Finite R (∀ j, (A j : Type))
    infer_instance
  · show Algebra.Etale R (∀ j, (A j : Type))
    infer_instance

/-- finiteEtale R is closed under limits of shape Discrete J for finite J. -/
instance isClosedUnderLimitsOfShape_discrete (J : Type) [Fintype J] :
    (CommAlgCat.finiteEtale R : ObjectProperty (CommAlgCat.{0} R)).IsClosedUnderLimitsOfShape
      (Discrete J) := by
  refine ObjectProperty.IsClosedUnderLimitsOfShape.mk' ?_
  rintro X ⟨F, hF⟩
  haveI : HasLimit (Discrete.functor (fun j : J => F.obj (Discrete.mk j))) :=
    hasLimit_of_iso Discrete.natIsoFunctor
  have hpt : (CommAlgCat.finiteEtale R) (piFan J (fun j => F.obj (Discrete.mk j))).pt :=
    finiteEtale_piFan_pt J _ (fun j => hF (Discrete.mk j))
  have hc : IsLimit (piFan J (fun j => F.obj (Discrete.mk j))) := piFan_isLimit J _
  have e1 : limit F ≅ limit (Discrete.functor (fun j : J => F.obj (Discrete.mk j))) :=
    HasLimit.isoOfNatIso Discrete.natIsoFunctor
  have e2 : limit (Discrete.functor (fun j : J => F.obj (Discrete.mk j))) ≅
      (piFan J (fun j => F.obj (Discrete.mk j))).pt :=
    IsLimit.conePointUniqueUpToIso (limit.isLimit _) hc
  exact ObjectProperty.prop_of_iso _ (e1 ≪≫ e2).symm hpt

/-! ### 3. Pushouts: the tensor product B (x)_A C -/

section Pushout

variable {A B C : CommAlgCat.{0} R} (f : A ⟶ B) (g : A ⟶ C)

/-- The tensor product cocone of a span in CommAlgCat R. -/
noncomputable def tensorCocone : PushoutCocone f g :=
  letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
  letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower R (A : Type) (B : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
  haveI : IsScalarTower R (A : Type) (C : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
  PushoutCocone.mk
    (CommAlgCat.ofHom (Algebra.TensorProduct.includeLeft (R := (A : Type)) (A := (B : Type))
      (B := (C : Type)) (S := R)))
    (CommAlgCat.ofHom ((Algebra.TensorProduct.includeRight (R := (A : Type)) (A := (B : Type))
      (B := (C : Type))).restrictScalars R))
    (by
      ext x
      have h1 : f.hom x = algebraMap (A : Type) (B : Type) x := rfl
      have h2 : g.hom x = algebraMap (A : Type) (C : Type) x := rfl
      simp only [CommAlgCat.hom_comp, AlgHom.comp_apply]
      rw [h1, h2]
      simp only [CommAlgCat.hom_ofHom, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
      rw [← Algebra.TensorProduct.algebraMap_apply (S := (A : Type)) (R := (A : Type))
        (A := (B : Type)) (B := (C : Type)) (r := x)]
      rw [← Algebra.TensorProduct.algebraMap_apply' (R := (A : Type)) (A := (B : Type))
        (B := (C : Type)) (r := x)])

noncomputable def tensorCocone_isColimit : IsColimit (tensorCocone f g) := by
  letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
  letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower R (A : Type) (B : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
  haveI : IsScalarTower R (A : Type) (C : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
  letI : Algebra (C : Type) ((B : Type) ⊗[A] (C : Type)) := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower (A : Type) (C : Type) ((B : Type) ⊗[A] (C : Type)) :=
    Algebra.TensorProduct.right_isScalarTower
  have key : ∀ (s : PushoutCocone f g), ∃ (d : (tensorCocone f g).pt ⟶ s.pt),
      ((tensorCocone f g).inl ≫ d = s.inl) ∧ ((tensorCocone f g).inr ≫ d = s.inr) ∧
      (∀ (m : (tensorCocone f g).pt ⟶ s.pt), (tensorCocone f g).inl ≫ m = s.inl →
        (tensorCocone f g).inr ≫ m = s.inr → m = d) := by
    intro s
    letI : Algebra (A : Type) (s.pt : Type) :=
      (s.inl.hom.toRingHom.comp (algebraMap (A : Type) (B : Type))).toAlgebra
    have hcomp : (algebraMap (A : Type) (s.pt : Type)) =
        s.inl.hom.toRingHom.comp (algebraMap (A : Type) (B : Type)) := rfl
    haveI : IsScalarTower R (A : Type) (s.pt : Type) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext x
        rw [hcomp]
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply R (A : Type) (B : Type) x]
        exact (s.inl.hom.commutes x).symm)
    haveI hpush : Algebra.IsPushout (A : Type) (B : Type) (C : Type)
        ((B : Type) ⊗[A] (C : Type)) := inferInstance
    let f' : (B : Type) →ₐ[A] (s.pt : Type) := { s.inl.hom with commutes' := fun a => rfl }
    let g' : (C : Type) →ₐ[A] (s.pt : Type) :=
      { s.inr.hom with
        commutes' := fun a => by
          have h := congrArg (fun (φ : A ⟶ s.pt) => φ.hom a) s.condition
          exact h.symm }
    refine ⟨CommAlgCat.ofHom ((Algebra.pushoutDesc ((B : Type) ⊗[A] (C : Type)) f' g'
      (fun x y => mul_comm (f' x) (g' y))).restrictScalars R), ?_, ?_, ?_⟩
    · ext b
      have h := AlgHom.congr_fun (Algebra.lift_algHom_comp_left (S' := (B : Type) ⊗[A] (C : Type))
        f' g' (fun x y => mul_comm (f' x) (g' y))) b
      show ((Algebra.pushoutDesc ((B : Type) ⊗[A] (C : Type)) f' g'
        (fun x y => mul_comm (f' x) (g' y))).comp
          (IsScalarTower.toAlgHom (A : Type) (B : Type) ((B : Type) ⊗[A] (C : Type)))) b =
          s.inl.hom b
      rw [h]
      rfl
    · ext c
      have h := AlgHom.congr_fun (Algebra.lift_algHom_comp_right (S' := (B : Type) ⊗[A] (C : Type))
        f' g' (fun x y => mul_comm (f' x) (g' y))) c
      show ((Algebra.pushoutDesc ((B : Type) ⊗[A] (C : Type)) f' g'
        (fun x y => mul_comm (f' x) (g' y))).comp
          (IsScalarTower.toAlgHom (A : Type) (C : Type) ((B : Type) ⊗[A] (C : Type)))) c =
          s.inr.hom c
      rw [h]
      rfl
    · intro m hm1 hm2
      let m' : ((B : Type) ⊗[A] (C : Type)) →ₐ[A] (s.pt : Type) :=
        { m.hom with
          commutes' := fun a => by
            show m.hom (algebraMap (A : Type) ((B : Type) ⊗[A] (C : Type)) a) =
              algebraMap (A : Type) (s.pt : Type) a
            have h := congrArg (fun (φ : B ⟶ s.pt) =>
              φ.hom (algebraMap (A : Type) (B : Type) a)) hm1
            exact h }
      have h1 : m'.comp (IsScalarTower.toAlgHom (A : Type) (C : Type) ((B : Type) ⊗[A] (C : Type)))
          = g' := by
        ext c
        show m.hom (algebraMap (C : Type) ((B : Type) ⊗[A] (C : Type)) c) = s.inr.hom c
        have h := congrArg (fun (φ : C ⟶ s.pt) => φ.hom c) hm2
        exact h
      have h2 : m'.comp (IsScalarTower.toAlgHom (A : Type) (B : Type) ((B : Type) ⊗[A] (C : Type)))
          = f' := by
        ext b
        show m.hom (algebraMap (B : Type) ((B : Type) ⊗[A] (C : Type)) b) = s.inl.hom b
        have h := congrArg (fun (φ : B ⟶ s.pt) => φ.hom b) hm1
        exact h
      have heq : m' = Algebra.pushoutDesc ((B : Type) ⊗[A] (C : Type)) f' g'
          (fun x y => mul_comm (f' x) (g' y)) :=
        Algebra.IsPushout.algHom_ext ((B : Type) ⊗[A] (C : Type))
          (h1.trans (Algebra.lift_algHom_comp_right (S' := (B : Type) ⊗[A] (C : Type))
            f' g' (fun x y => mul_comm (f' x) (g' y))).symm)
          (h2.trans (Algebra.lift_algHom_comp_left (S' := (B : Type) ⊗[A] (C : Type))
            f' g' (fun x y => mul_comm (f' x) (g' y))).symm)
      have hm : m = CommAlgCat.ofHom (m'.restrictScalars R) := rfl
      rw [hm]
      exact congrArg (fun (ψ : ((B : Type) ⊗[A] (C : Type)) →ₐ[A] (s.pt : Type)) =>
        CommAlgCat.ofHom (ψ.restrictScalars R)) heq
  choose d hd1 hd2 hd3 using key
  refine PushoutCocone.IsColimit.mk (tensorCocone f g).condition d hd1 hd2 ?_
  intro s m hm1 hm2
  exact hd3 s m hm1 hm2

/-- The tensor product of finite etale algebras is finite etale. -/
theorem finiteEtale_tensorCocone_pt (hA : (CommAlgCat.finiteEtale R) A)
    (hB : (CommAlgCat.finiteEtale R) B) (hC : (CommAlgCat.finiteEtale R) C) :
    (CommAlgCat.finiteEtale R) (tensorCocone f g).pt := by
  letI : Algebra (A : Type) (B : Type) := f.hom.toRingHom.toAlgebra
  letI : Algebra (A : Type) (C : Type) := g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower R (A : Type) (B : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
  haveI : IsScalarTower R (A : Type) (C : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
  haveI : Module.Finite R (A : Type) := hA.1
  haveI : Module.Finite R (B : Type) := hB.1
  haveI : Module.Finite R (C : Type) := hC.1
  haveI : Algebra.Etale R (A : Type) := hA.2
  haveI : Algebra.Etale R (B : Type) := hB.2
  haveI : Algebra.Etale R (C : Type) := hC.2
  refine ⟨?_, ?_⟩
  · show Module.Finite R ((B : Type) ⊗[A] (C : Type))
    haveI : Module.Finite (A : Type) (B : Type) :=
      Module.Finite.of_restrictScalars_finite R (A : Type) (B : Type)
    haveI : Module.Finite (A : Type) (C : Type) :=
      Module.Finite.of_restrictScalars_finite R (A : Type) (C : Type)
    haveI : Module.Finite (A : Type) ((B : Type) ⊗[A] (C : Type)) :=
      Module.Finite.tensorProduct (A : Type) (B : Type) (C : Type)
    exact Module.Finite.trans (A : Type) ((B : Type) ⊗[A] (C : Type))
  · show Algebra.Etale R ((B : Type) ⊗[A] (C : Type))
    haveI : Algebra.Etale (A : Type) (C : Type) :=
      Algebra.Etale.of_restrictScalars R (A : Type) (C : Type)
    haveI : Algebra.Etale (B : Type) ((B : Type) ⊗[A] (C : Type)) :=
      Algebra.Etale.baseChange (A : Type) (C : Type) (B : Type)
    exact Algebra.Etale.comp R (B : Type) ((B : Type) ⊗[A] (C : Type))

end Pushout

/-- finiteEtale R is closed under pushouts: the pushout is the tensor product over the
common vertex. -/
instance isClosedUnderColimitsOfShape_walkingSpan :
    (CommAlgCat.finiteEtale R : ObjectProperty (CommAlgCat.{0} R)).IsClosedUnderColimitsOfShape
      WalkingSpan := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro X ⟨F, hF⟩
  let f := F.map WalkingSpan.Hom.fst
  let g := F.map WalkingSpan.Hom.snd
  letI : Algebra (F.obj WalkingSpan.zero : Type) (F.obj WalkingSpan.left : Type) :=
    f.hom.toRingHom.toAlgebra
  letI : Algebra (F.obj WalkingSpan.zero : Type) (F.obj WalkingSpan.right : Type) :=
    g.hom.toRingHom.toAlgebra
  haveI : IsScalarTower R (F.obj WalkingSpan.zero : Type) (F.obj WalkingSpan.left : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (f.hom.commutes x).symm)
  haveI : IsScalarTower R (F.obj WalkingSpan.zero : Type) (F.obj WalkingSpan.right : Type) :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (g.hom.commutes x).symm)
  have hpt : (CommAlgCat.finiteEtale R) (tensorCocone f g).pt :=
    finiteEtale_tensorCocone_pt f g (hF WalkingSpan.zero) (hF WalkingSpan.left) (hF WalkingSpan.right)
  have hc : IsColimit ((Cocone.precompose (diagramIsoSpan F).hom).obj (tensorCocone f g)) :=
    (IsColimit.precomposeHomEquiv (diagramIsoSpan F) (tensorCocone f g)).symm
      (tensorCocone_isColimit f g)
  have e : colimit F ≅ (tensorCocone f g).pt := colimit.isoColimitCocone ⟨_, hc⟩
  exact ObjectProperty.prop_of_iso _ e.symm hpt

/-! ### 4. Assembly: finite coproducts and pullbacks -/

instance hasFiniteProducts : HasFiniteProducts (CommAlgCat.FiniteEtale.{0} R) where
  out n := by
    haveI : HasLimitsOfShape (Discrete (Fin n)) (CommAlgCat.FiniteEtale.{0} R) :=
      hasLimitsOfShape_of_closedUnderLimits (Discrete (Fin n)) (CommAlgCat.finiteEtale R)
    infer_instance

instance hasColimitsOfShape_walkingSpan_finiteEtale :
    HasColimitsOfShape WalkingSpan (CommAlgCat.FiniteEtale.{0} R) :=
  hasColimitsOfShape_of_closedUnderColimits WalkingSpan (CommAlgCat.finiteEtale R)

/-- The opposite of the category of finite etale R-algebras has finite coproducts. -/
instance hasFiniteCoproducts : HasFiniteCoproducts (FiniteEtaleAlg R) where
  out n := by
    haveI h1 : HasLimitsOfShape (Discrete (Fin n)) (CommAlgCat.FiniteEtale.{0} R) :=
      HasFiniteProducts.out n
    haveI h2 : HasLimitsOfShape ((Discrete (Fin n))ᵒᵖ) (CommAlgCat.FiniteEtale.{0} R) :=
      hasLimitsOfShape_of_equivalence (Discrete.opposite (Fin n)).symm
    exact hasColimitsOfShape_op_of_hasLimitsOfShape (J := Discrete (Fin n))

/-- The opposite of the category of finite etale R-algebras has pullbacks. -/
instance hasPullbacks : HasPullbacks (FiniteEtaleAlg R) := by
  haveI : HasColimitsOfShape WalkingCospanᵒᵖ (CommAlgCat.FiniteEtale.{0} R) :=
    hasColimitsOfShape_of_equivalence walkingCospanOpEquiv.symm
  exact hasLimitsOfShape_op_of_hasColimitsOfShape (J := WalkingCospan)

end FiniteEtaleClosure

end S1779FiniteEtaleClosure

/-! ## 3. The algebra-side PreGaloisCategory of R': what is unconditional -/

namespace S1779FiniteEtaleAlg

/-- R' itself, as a finite etale R'-algebra: the terminal object of
`(FiniteEtale R')^op`. -/
abbrev self : S1779AlgR :=
  Opposite.op (CommAlgCat.FiniteEtale.of S1779R S1779R)

/-- Any two morphisms `X ⟶ self` agree: they are two R'-algebra maps out of R'. -/
theorem hom_self_subsingleton (X : S1779AlgR) : Subsingleton (X ⟶ self) where
  allEq f g := by
    have h : f.unop = g.unop := by
      apply InducedCategory.hom_ext
      apply CommAlgCat.hom_ext
      exact Subsingleton.elim _ _
    exact Quiver.Hom.unop_inj h

instance (X : S1779AlgR) : Subsingleton (X ⟶ self) := hom_self_subsingleton X

instance (X : S1779AlgR) : Unique (X ⟶ self) where
  default := (CommAlgCat.FiniteEtale.ofHom (Algebra.ofId S1779R X.unop.obj)).op
  uniq f := Subsingleton.allEq f _

/-- The terminal object of the corrected target. -/
def isTerminal_self : IsTerminal self := IsTerminal.ofUnique _

instance : HasTerminal S1779AlgR := hasTerminal_of_unique self

end S1779FiniteEtaleAlg

/-- G2 for R': colimits of shape `SingleObj G` in `(FiniteEtale R')^op`, i.e.
the invariant subalgebra of a finite-group action on a finite etale R'-algebra.
S1770 proves this for a field; for non-field R' it is not in the tree. -/
def S1779QuotientsMissing : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    HasColimitsOfShape (SingleObj G) S1779AlgR

/-- G3 for R': a monomorphism in `(FiniteEtale R')^op` induces an isomorphism
on a direct summand.  S1747 proves the algebraic core only for a field and
does not discharge its `FiniteEtaleSplit K` input. -/
def S1779MonoMissing : Prop :=
  ∀ {X Y : S1779AlgR} (i : X ⟶ Y), Mono i →
    ∃ (Z : S1779AlgR) (u : Z ⟶ Y),
      Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The exact total missing content of `PreGaloisCategory S1779AlgR` after the
unconditional terminal/pullback/coproduct fields: G2 and G3. -/
def S1779AlgPreGaloisMissing : Prop :=
  S1779QuotientsMissing ∧ S1779MonoMissing

/-- The corrected algebra-side PreGaloisCategory, from exactly G2 and G3. -/
@[reducible]
noncomputable def S1779PreGaloisCategory
    (hQuot : S1779QuotientsMissing) (hMono : S1779MonoMissing) :
    PreGaloisCategory S1779AlgR where
  hasTerminal := inferInstance
  hasPullbacks := inferInstance
  hasFiniteCoproducts := inferInstance
  hasQuotientsByFiniteGroups := hQuot
  monoInducesIsoOnDirectSummand := hMono

/-- The PreGaloisCategory from the packaged exact missing pair. -/
@[reducible]
noncomputable def S1779PreGaloisCategory_of_missing
    (h : S1779AlgPreGaloisMissing) : PreGaloisCategory S1779AlgR :=
  S1779PreGaloisCategory h.1 h.2

/-! ## 4. The actual geometric point at (0,0) and the fibre functor -/

/-- The actual F'-algebra point R' -> F' at the affine point (0,0) of E'. -/
noncomputable def S1779Point : S1779R →ₐ[S1779K] S1779K :=
  S1726PointAlgHom 0 0 S1726Equation_zero_zero

/-- The R'-algebra structure on `AlgebraicClosure F'` obtained by composing the
point (0,0) with the algebraic closure. -/
@[reducible]
noncomputable def S1779PointClosureAlgebra :
    Algebra S1779R (AlgebraicClosure S1779K) :=
  RingHom.toAlgebra
    ((algebraMap S1779K (AlgebraicClosure S1779K)).comp S1779Point.toRingHom)

/-- The geometric point Omega = algebraic closure of the residue field F' at (0,0). -/
theorem S1779GeometricPoint_isSepClosed :
    IsSepClosed (AlgebraicClosure S1779K) := inferInstance

/-- Mathlib's actual fibre functor at the geometric point (0,0):
`A ↦ (A →ₐ[R'] Omega)`.  The functor itself is unconditional; only its
`FiberFunctor` structure is missing below. -/
noncomputable def S1779GeometricFiber : S1779AlgR ⥤ FintypeCat.{0} :=
  letI : Algebra S1779R (AlgebraicClosure S1779K) := S1779PointClosureAlgebra
  CommAlgCat.FiniteEtale.fiber S1779R (AlgebraicClosure S1779K)

/-- The exact missing `FiberFunctor` structure on the genuine geometric fibre
functor at (0,0).  Its six fields are the G4--G6 content for R'; the functor
itself is Mathlib's `CommAlgCat.FiniteEtale.fiber`, not a placeholder. -/
def S1779FiberFunctorMissing (hPre : PreGaloisCategory S1779AlgR) : Prop :=
  @PreGaloisCategory.FiberFunctor S1779AlgR S1779AlgR_category hPre
    S1779GeometricFiber

/-! ## 5. The corrected S1753 route and its target assembly -/

/-- **The corrected affine route**: a `Category.{0,1}` on the actual cover type,
with homs equivalent to the actual cover maps, together with an equivalence to
the corrected target `(FiniteEtale R')^op`.

This is the exact place where S1777's affine equivalence is consumed.  The
old S1753 route used `S1753Alg = (FiniteEtale F')^op` here, which is the wrong
domain. -/
structure S1779AffineRoute where
  /-- The category structure on the actual cover type. -/
  coverCategory : Category.{0, 1} S1728Cover
  /-- Its homs are the actual cover maps (the target's
  `coverMorphism_bijective` content). -/
  coverHomEquiv : ∀ A B,
    @Quiver.Hom _ coverCategory.toQuiver A B ≃ S1728CoverMap A B
  /-- The corrected affine equivalence to finite etale R'-algebras. -/
  equivalence : @CategoryTheory.Equivalence S1728Cover S1779AlgR
    coverCategory S1779AlgR_category

/-- The algebra-side Galois data for the corrected target: a PreGaloisCategory
on `(FiniteEtale R')^op` and a fibre functor. -/
structure S1779AlgGaloisData where
  /-- The PreGaloisCategory on the corrected target. -/
  preGalois : PreGaloisCategory S1779AlgR
  /-- The fibre functor. -/
  fiber : S1779AlgR ⥤ FintypeCat.{0}
  /-- The fibre-functor structure. -/
  fiberFunctor : @PreGaloisCategory.FiberFunctor S1779AlgR
    S1779AlgR_category preGalois fiber

/-- **Assembly of the four target fields from the corrected route.**  The
category, PreGaloisCategory, GaloisCategory and fibre functor are transported
along the corrected equivalence by S1753's generic transport; no old target
appears. -/
noncomputable def S1779TargetFields_of_route
    (R : S1779AffineRoute) (D : S1779AlgGaloisData) : S1779TargetFields := by
  letI : Category.{0, 1} S1728Cover := R.coverCategory
  letI : PreGaloisCategory S1779AlgR := D.preGalois
  letI : PreGaloisCategory.FiberFunctor D.fiber := D.fiberFunctor
  letI : GaloisCategory S1779AlgR :=
    GaloisCategory.mk ⟨D.fiber, ⟨D.fiberFunctor⟩⟩
  exact
    { coverCategory := R.coverCategory
      galoisCategory := S1753GaloisCategoryOfFiber R.equivalence D.fiber
      fiber := R.equivalence.functor ⋙ D.fiber
      fiberFunctor := S1753FiberFunctorTransport R.equivalence D.fiber }

/-- The algebra-side Galois data from the exact missing G2/G3 pair and the
missing geometric-fibre `FiberFunctor` structure. -/
noncomputable def S1779AlgGaloisData_of_missing
    (hQuot : S1779QuotientsMissing) (hMono : S1779MonoMissing)
    (hFiber : S1779FiberFunctorMissing (S1779PreGaloisCategory hQuot hMono)) :
    S1779AlgGaloisData where
  preGalois := S1779PreGaloisCategory hQuot hMono
  fiber := S1779GeometricFiber
  fiberFunctor := hFiber

/-! ### 5b. The S1777 piece, named separately -/

/-- The affine finite-etale slice of S1733 over the actual base `Spec R'`. -/
abbrev S1779Slice : Type 1 := S1733Slice

/-- **The part S1777 is expected to supply**: the affine equivalence between
the corrected algebra category `(FiniteEtale R')^op` and S1733's affine
finite-etale slice over `Spec R'`.  S1777's probes construct the functor
`(FiniteEtale R')^op ⥤ S1733Slice`; this is the exact equivalence target. -/
def S1779AffineSliceEquivalenceMissing : Prop :=
  Nonempty (S1779AlgR ≌ S1779Slice)

/-- The cover-to-slice comparison of S1743 (equivalently S1733's
`S1733CoverSliceEquivalence`), including its object map and full/faithful/
essentially-surjective content. -/
def S1779CoverSliceComparisonMissing : Prop :=
  S1743CoverSliceComparisonMissing

/-- The remaining cover-side input, packaged as S1733's affine cover model:
an affine finite-etale model of every cover together with the bijection
between model morphisms and actual cover maps.  Its `homEquiv` is the
target's `coverMorphism_bijective` content; it is not implied by an
equivalence of 2-isomorphism-quotient categories alone. -/
def S1779CoverHomComparisonMissing : Prop :=
  S1733AffineCoverModelMissing

/-- The combined first input `S1779FirstMissing` is the composition of the
S1777 affine slice equivalence, the S1743/S1733 cover-slice comparison and the
hom comparison.  This file does not assert that composition as a theorem,
because the hom comparison is exactly the still-missing S1744 R2; the three
pieces are named separately so that S1777's output can be consumed without
being conflated with the cover-side geometry. -/
def S1779FirstMissingPieces : Prop :=
  S1779AffineSliceEquivalenceMissing ∧
    S1779CoverSliceComparisonMissing ∧ S1779CoverHomComparisonMissing

/-! ## 6. The exact first missing and the conditional target theorem -/

/-- **The first missing input of the corrected route**: the actual small cover
category together with an equivalence to the corrected target
`(FiniteEtale R')^op`.  This is exactly the R'-level affine equivalence that
S1777 is expected to supply; it is not present in this checkout.

The definition is S1753's `S1753CoverAlgEquivalence` with the algebra side
changed from the base field F' to the coordinate ring R'. -/
def S1779FirstMissing : Prop :=
  ∃ (C : Category.{0, 1} S1728Cover)
    (_ : ∀ A B, @Quiver.Hom _ C.toQuiver A B ≃ S1728CoverMap A B),
    Nonempty (@CategoryTheory.Equivalence S1728Cover S1779AlgR C
      S1779AlgR_category)

/-- `S1779FirstMissing` is definitionally the existence of the corrected route. -/
theorem S1779FirstMissing_iff_route :
    S1779FirstMissing ↔ Nonempty S1779AffineRoute := by
  constructor
  · rintro ⟨C, hhom, ⟨E⟩⟩
    exact ⟨⟨C, hhom, E⟩⟩
  · rintro ⟨R⟩
    exact ⟨R.coverCategory, R.coverHomEquiv, ⟨R.equivalence⟩⟩

/-- The first missing input alone supplies the target's `coverCategory` field. -/
theorem S1779Category01_of_firstMissing (h : S1779FirstMissing) :
    Nonempty (Category.{0, 1} S1728Cover) := by
  rcases h with ⟨C, _, _⟩
  exact ⟨C⟩

/-- **The conditional corrected target theorem.**  From the first missing
affine equivalence, the exact G2/G3 missing pair for R', and the missing
geometric-fibre `FiberFunctor` structure, the four target fields are obtained
by genuine transport.  No old base-field target is used. -/
theorem S1779TargetFields_of_missing
    (hAff : S1779FirstMissing)
    (hQuot : S1779QuotientsMissing) (hMono : S1779MonoMissing)
    (hFiber : S1779FiberFunctorMissing (S1779PreGaloisCategory hQuot hMono)) :
    Nonempty S1779TargetFields := by
  rcases hAff with ⟨C, hhom, ⟨E⟩⟩
  letI : Category.{0, 1} S1728Cover := C
  exact ⟨S1779TargetFields_of_route
    { coverCategory := C
      coverHomEquiv := hhom
      equivalence := E }
    (S1779AlgGaloisData_of_missing hQuot hMono hFiber)⟩

/-- The same conditional theorem with the algebra-side PreGaloisCategory and
fibre functor given separately. -/
theorem S1779TargetFields_of_missing'
    (hAff : S1779FirstMissing)
    (hPre : PreGaloisCategory S1779AlgR)
    (hFiber : S1779FiberFunctorMissing hPre) :
    Nonempty S1779TargetFields := by
  rcases hAff with ⟨C, hhom, ⟨E⟩⟩
  letI : Category.{0, 1} S1728Cover := C
  exact ⟨S1779TargetFields_of_route
    { coverCategory := C
      coverHomEquiv := hhom
      equivalence := E }
    { preGalois := hPre
      fiber := S1779GeometricFiber
      fiberFunctor := hFiber }⟩

/-! ## 7. Checks and axiom audit -/

#check S1779R
#check S1779FunctionField
#check S1779AlgR
#check S1779AlgK
#check S1779OldTarget
#check S1779OldTarget_eq_S1753Alg
#check S1779FiniteEtaleAlg.isTerminal_self
#check S1779QuotientsMissing
#check S1779MonoMissing
#check S1779AlgPreGaloisMissing
#check S1779PreGaloisCategory
#check S1779Point
#check S1779GeometricFiber
#check S1779FiberFunctorMissing
#check S1779AffineRoute
#check S1779AlgGaloisData
#check S1779TargetFields_of_route
#check S1779AlgGaloisData_of_missing
#check S1779FirstMissing
#check S1779FirstMissing_iff_route
#check S1779Category01_of_firstMissing
#check S1779TargetFields_of_missing
#check S1779Slice
#check S1779AffineSliceEquivalenceMissing
#check S1779CoverSliceComparisonMissing
#check S1779CoverHomComparisonMissing
#check S1779FirstMissingPieces
#check S1779TargetFields_of_missing'

#print axioms S1779FunctionField_eq_fractionRing
#print axioms S1779OldTarget_eq_S1753Alg
#print axioms S1779FiniteEtaleAlg.isTerminal_self
#print axioms S1779PreGaloisCategory
#print axioms S1779GeometricPoint_isSepClosed
#print axioms S1779FirstMissing_iff_route
#print axioms S1779Category01_of_firstMissing
#print axioms S1779TargetFields_of_route
#print axioms S1779AlgGaloisData_of_missing
#print axioms S1779TargetFields_of_missing
#print axioms S1779TargetFields_of_missing'

#print axioms S1779FiniteEtaleClosure.FiniteEtaleClosure.piFan_isLimit
#print axioms S1779FiniteEtaleClosure.FiniteEtaleClosure.finiteEtale_piFan_pt
#print axioms S1779FiniteEtaleClosure.FiniteEtaleClosure.isClosedUnderLimitsOfShape_discrete
#print axioms S1779FiniteEtaleClosure.FiniteEtaleClosure.tensorCocone_isColimit
#print axioms S1779FiniteEtaleClosure.FiniteEtaleClosure.finiteEtale_tensorCocone_pt
#print axioms S1779FiniteEtaleClosure.FiniteEtaleClosure.isClosedUnderColimitsOfShape_walkingSpan
#print axioms S1779FiniteEtaleClosure.FiniteEtaleClosure.hasFiniteProducts
#print axioms S1779FiniteEtaleClosure.FiniteEtaleClosure.hasFiniteCoproducts
#print axioms S1779FiniteEtaleClosure.FiniteEtaleClosure.hasPullbacks

end LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual