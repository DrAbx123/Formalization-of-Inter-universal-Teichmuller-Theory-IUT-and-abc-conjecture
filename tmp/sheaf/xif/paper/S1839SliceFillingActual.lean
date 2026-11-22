/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.xif.paper.S1812InverseModelHomActual
import tmp.sheaf.xif.paper.S1762CoverLimitsActual
import tmp.sheaf.xif.paper.S1828SliceR1Actual

/-!
# S1839: the universal slice filling S1828SliceFillsOver is false

## The question

S1828 isolated the statement

  S1828SliceFillsOver : for all covers A B and every model morphism
    g : S1733Model A ⟶ S1733Model B,  g ≫ S1733ModelOver B = S1733ModelOver A,

and derived R1 for the uncorrected target S1733ModelCategory from it
(S1828R1ModelCategory, conditional on S1755SourceRetraction,
S1766CoverMapDiscrete and S1828SliceFillsOver).  It also proved that the
filling is not a consequence of the slice comparison alone.

The question addressed here: can the concrete model-map constructions
S1755ModelHomOfCoverMap, S1816ModelMap_over, S1744ModelMapOfCoverMap,
S1812ModelHomOfCoverMap_triangle prove the filling?  After all, a cover map is
a map over the orbicurve, so its associated model morphism is over Spec R'.

## Answer: no.  The construction proves only one direction, and the universal
## filling is refuted by an explicit counterexample.

The concrete construction proves exactly

  every morphism in the image of the extraction is over Spec R'
  (S1812ModelHomOfCoverMap_triangle, restated as S1839ExtractionOverBase;
  this is the formal content of S1816ModelMap_over).

It does not prove that every model morphism is such an image.  That
surjectivity is false, and with it the filling.

## The counterexample

Take the terminal (identity) cover of the actual S1726 orbicurve, constructed
unconditionally in S1762 (S1762TerminalCover, whose finite-etaleness is
S1762IdentityFiniteEtale).  Its chosen identity-point base-change presentation
is the identity square, so

  S1733Model S1762TerminalCover      = S1726AffineOver        (rfl),
  S1733ModelOver S1762TerminalCover  = 𝟙 S1726AffineOver       (rfl)
  (S1839TerminalModel, S1839TerminalModelOver).

At this pair the filling triangle reads g ≫ 𝟙 = 𝟙, i.e. it says that every
endomorphism g of Spec R' over Spec F' is the identity.  This is false: let x
be the coordinate X 0 in R' = F'[x,y]/(y^2 - x^3 - (61/64)x^2 + (125/64)x).
The F'-point (0,0) gives an F'-algebra endomorphism S1839ConstTau of R' with
S1839ConstTau x = 0, while the F'-point (1,0) shows x ≠ 0.  Hence
S1839ConstEnd := Spec S1839ConstTau is a non-identity endomorphism of Spec R'
over Spec F', and

  S1839TerminalFilling_false : the filling triangle fails at the terminal pair,
  S1839_not_sliceFillsOver    : ¬ S1828SliceFillsOver.

## Consequences

* S1828SliceFillsOver is not merely unproven: it is false.  Consequently
  S1828R1ModelCategory has a refuted hypothesis and cannot be applied; R1 for
  S1733ModelCategory cannot be obtained from h + hd through the filling.
  The slice-corrected S1828R1 (target S1828ModelOverCategory) is unaffected.

* S1839ConstEnd is not the extraction of any cover map
  (S1839NotExtractionImage), because every extraction value is over Spec R' by
  S1812ModelHomOfCoverMap_triangle.  Hence the extraction is not surjective
  (S1839_not_modelHomSurjective) and the S1755 hom equivalence is false
  (S1839_not_modelHomEquivMissing):

    ¬ S1755ModelHomSurjective,   ¬ S1755ModelHomEquivMissing.

* With S1755SourceRetraction, S1828's dictionary S1828ModelHomEquivMissing_iff
  therefore also shows that S1828SliceFillsOver ∧ S1766CoverMapDiscrete is
  false (S1839_fillingConj_false).

## Honest boundary

No sorry, no axiom, no Shrink/ULift/PUnit, no fake data.  The terminal cover,
its finite-etaleness and the scheme Spec R' are the actual objects of the tree;
the endomorphism is the actual Spec of the actual F'-algebra map R' → R'
constant at the actual point (0,0).  Only propext, Classical.choice and
Quot.sound are used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1839SliceFillingActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1755TwoYonedaSmallnessActual
open LeanFormal.IUT.XiFPaper.S1762CoverLimitsActual
open LeanFormal.IUT.XiFPaper.S1766CanonicalModelInjectivityActual
open LeanFormal.IUT.XiFPaper.S1812InverseModelHomActual
open LeanFormal.IUT.XiFPaper.S1828SliceR1Actual

/-! ## 1. The terminal cover and the computation of its S1733 model -/

/-- The terminal (identity) cover of the S1726 orbicurve, as a cover in the
sense of the S1828 file. -/
noncomputable abbrev S1839TerminalCover : S1728Cover :=
  S1762TerminalCover

/-- The chosen finite-etaleness of the terminal cover. -/
theorem S1839TerminalCover_finiteEtale :
    S1839TerminalCover.finiteEtale = S1762IdentityFiniteEtale := rfl

/-- The S1733 model of the terminal cover is Spec R' itself.  The
identity-point base-change presentation of the identity map has pullback scheme
the test scheme itself. -/
theorem S1839TerminalModel :
    S1733Model (A := S1839TerminalCover) = S1726AffineOver := rfl

/-- The structure morphism of the model of the terminal cover is the
identity. -/
theorem S1839TerminalModelOver :
    S1733ModelOver (A := S1839TerminalCover) = 𝟙 S1726AffineOver := rfl

/-! ## 2. The coordinate x of R' and the two F'-points -/

/-- The class of the coordinate x in R' = F'[x,y]/(P). -/
noncomputable def S1839X : S1726CoordinateRing :=
  Ideal.Quotient.mk (Ideal.span {S1726AffinePolynomial}) (MvPolynomial.X 0)

/-- The F'-point (1,0) of the model sends x to 1. -/
theorem S1839X_eval_one_zero :
    S1726PointAlgHom 1 0 S1726Equation_one_zero S1839X = 1 := by
  simpa [S1839X] using
    (S1726PointAlgHom_X0 (x := 1) (y := 0) (h := S1726Equation_one_zero))

/-- The F'-point (0,0) of the model sends x to 0. -/
theorem S1839X_eval_zero_zero :
    S1726PointAlgHom 0 0 S1726Equation_zero_zero S1839X = 0 := by
  simpa [S1839X] using
    (S1726PointAlgHom_X0 (x := 0) (y := 0) (h := S1726Equation_zero_zero))

/-- x is nonzero in R', witnessed by the F'-point (1,0). -/
theorem S1839X_ne_zero : S1839X ≠ 0 := by
  intro hx
  have h1 := S1839X_eval_one_zero
  rw [hx, map_zero] at h1
  exact zero_ne_one h1

/-! ## 3. A non-identity endomorphism of the terminal model -/

/-- The F'-algebra endomorphism of R' that is constant at the F'-point (0,0):
it is the composite R' → F' → R'. -/
noncomputable def S1839ConstTau :
    S1726CoordinateRing →ₐ[S1726K] S1726CoordinateRing :=
  (Algebra.ofId S1726K S1726CoordinateRing).comp
    (S1726PointAlgHom 0 0 S1726Equation_zero_zero)

/-- The constant endomorphism kills x. -/
theorem S1839ConstTau_X : S1839ConstTau S1839X = 0 := by
  simp [S1839ConstTau, S1839X, S1726PointAlgHom_X0]

/-- The non-identity endomorphism of Spec R' over Spec F' induced by the
constant F'-algebra endomorphism S1839ConstTau. -/
noncomputable def S1839ConstEnd : S1726AffineOver ⟶ S1726AffineOver :=
  Over.homMk (Spec.map (CommRingCat.ofHom S1839ConstTau.toRingHom)) (by
    show Spec.map (CommRingCat.ofHom S1839ConstTau.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap S1726K S1726CoordinateRing)) =
      Spec.map (CommRingCat.ofHom (algebraMap S1726K S1726CoordinateRing))
    rw [← Spec.map_comp]
    congr 1
    ext c
    simp [S1839ConstTau])

/-- The constant endomorphism is not the identity.  If it were, then by
Spec-faithfulness the ring endomorphism S1839ConstTau would be the identity,
contradicting S1839ConstTau X = 0 and X ≠ 0. -/
theorem S1839ConstEnd_ne_id : S1839ConstEnd ≠ 𝟙 S1726AffineOver := by
  intro h
  have hleft : S1839ConstEnd.left =
      (𝟙 S1726AffineOver : S1726AffineOver ⟶ S1726AffineOver).left :=
    congrArg (fun f : S1726AffineOver ⟶ S1726AffineOver => f.left) h
  rw [Over.id_left] at hleft
  have hspec : Spec.map (CommRingCat.ofHom S1839ConstTau.toRingHom) =
      𝟙 (Spec (CommRingCat.of S1726CoordinateRing)) := hleft
  have hring : CommRingCat.ofHom S1839ConstTau.toRingHom =
      𝟙 (CommRingCat.of S1726CoordinateRing) := (Spec.map_eq_id).mp hspec
  have htau : S1839ConstTau.toRingHom = RingHom.id S1726CoordinateRing := by
    have := congrArg CommRingCat.Hom.hom hring
    simpa using this
  have hx : S1839ConstTau S1839X = S1839X := by
    have := congrArg
      (fun f : S1726CoordinateRing →+* S1726CoordinateRing => f S1839X) htau
    simpa using this
  rw [S1839ConstTau_X] at hx
  exact S1839X_ne_zero hx.symm

/-! ## 4. The filling fails at the terminal pair and is false universally -/

/-- The filling triangle fails at the terminal cover.  At this pair the S1733
model is Spec R' with identity structure morphism, so the filling would force
every endomorphism of Spec R' over Spec F' to be the identity; the constant
endomorphism is a counterexample. -/
theorem S1839TerminalFilling_false :
    ¬ (∀ g : S1733Model (A := S1839TerminalCover) ⟶
          S1733Model (A := S1839TerminalCover),
        g ≫ S1733ModelOver (A := S1839TerminalCover) =
          S1733ModelOver (A := S1839TerminalCover)) := by
  intro hf
  have h := hf S1839ConstEnd
  have h' : (S1839ConstEnd : S1726AffineOver ⟶ S1726AffineOver) ≫
      (𝟙 S1726AffineOver) = 𝟙 S1726AffineOver := h
  have hg : S1839ConstEnd = 𝟙 S1726AffineOver := by
    simpa using h'
  exact S1839ConstEnd_ne_id hg

/-- S1828SliceFillsOver is false.  The universal filling is refuted by the
terminal cover and the constant endomorphism of its model. -/
theorem S1839_not_sliceFillsOver : ¬ S1828SliceFillsOver := by
  intro h
  exact S1839TerminalFilling_false
    (fun g => h S1839TerminalCover S1839TerminalCover g)

/-! ## 5. The extraction misses this endomorphism -/

/-- What the concrete model-map construction does prove: every value of the
S1742/S1755 extraction is a model morphism over Spec R' (S1812's triangle;
equivalently the scheme-level content of S1816ModelMap_over).  This is the
one-directional consequence of "cover maps are over the orbicurve"; it is not
the universal filling. -/
theorem S1839ExtractionOverBase (A B : S1728Cover) (f : S1728CoverMap A B) :
    S1755ModelHomOfCoverMap A B f ≫ S1733ModelOver B = S1733ModelOver A :=
  S1812ModelHomOfCoverMap_triangle A B f

/-- The constant endomorphism is not the extraction of any cover map.  An
extraction value is over Spec R' (S1839ExtractionOverBase), while the terminal
model has identity structure morphism, so such a value would have to be the
identity; the constant endomorphism is not. -/
theorem S1839NotExtractionImage
    (f : S1728CoverMap S1839TerminalCover S1839TerminalCover) :
    S1755ModelHomOfCoverMap S1839TerminalCover S1839TerminalCover f ≠
      S1839ConstEnd := by
  intro h
  have htri := S1839ExtractionOverBase S1839TerminalCover S1839TerminalCover f
  rw [h] at htri
  have htri' : (S1839ConstEnd : S1726AffineOver ⟶ S1726AffineOver) ≫
      (𝟙 S1726AffineOver) = 𝟙 S1726AffineOver := htri
  have hone : S1839ConstEnd = 𝟙 S1726AffineOver := by
    simpa using htri'
  exact S1839ConstEnd_ne_id hone

/-- The S1755 extraction is not surjective.  Unconditional: the terminal cover
already gives a model morphism outside the image. -/
theorem S1839_not_modelHomSurjective : ¬ S1755ModelHomSurjective := by
  intro hsur
  obtain ⟨f, hf⟩ := hsur S1839TerminalCover S1839TerminalCover S1839ConstEnd
  exact S1839NotExtractionImage f hf

/-- The S1755 hom equivalence is false.  Since the extraction is not
surjective, no two-sided inverse data can exist. -/
theorem S1839_not_modelHomEquivMissing : ¬ S1755ModelHomEquivMissing :=
  fun h => S1839_not_modelHomSurjective
    (S1755ModelHomSurjective_of_modelHomEquiv h)

/-! ## 6. The S1828 dictionary at the refuted filling -/

/-- With the source-retraction hypothesis, S1828's dictionary identifies the
S1755 hom equivalence with the conjunction of the (false) filling and
discreteness.  Hence that conjunction is also false. -/
theorem S1839_fillingConj_false (h : S1755SourceRetraction) :
    ¬ (S1828SliceFillsOver ∧ S1766CoverMapDiscrete) :=
  fun hc => S1839_not_modelHomEquivMissing
    ((S1828ModelHomEquivMissing_iff h).mpr hc)

/-- The same statement in the exact form of S1828's dictionary. -/
theorem S1839ModelHomEquivMissing_iff_false (h : S1755SourceRetraction) :
    S1755ModelHomEquivMissing ↔ (S1828SliceFillsOver ∧ S1766CoverMapDiscrete) :=
  S1828ModelHomEquivMissing_iff h

/-! ## 7. Checks and axiom footprint -/

#check S1839TerminalCover
#check S1839TerminalModel
#check S1839TerminalModelOver
#check S1839X
#check S1839X_ne_zero
#check S1839ConstTau
#check S1839ConstEnd
#check S1839ConstEnd_ne_id
#check S1839TerminalFilling_false
#check S1839_not_sliceFillsOver
#check S1839ExtractionOverBase
#check S1839NotExtractionImage
#check S1839_not_modelHomSurjective
#check S1839_not_modelHomEquivMissing
#check S1839_fillingConj_false
#check S1839ModelHomEquivMissing_iff_false

#print axioms S1839TerminalModel
#print axioms S1839X_ne_zero
#print axioms S1839ConstEnd_ne_id
#print axioms S1839TerminalFilling_false
#print axioms S1839_not_sliceFillsOver
#print axioms S1839ExtractionOverBase
#print axioms S1839NotExtractionImage
#print axioms S1839_not_modelHomSurjective
#print axioms S1839_not_modelHomEquivMissing
#print axioms S1839_fillingConj_false

end LeanFormal.IUT.XiFPaper.S1839SliceFillingActual
