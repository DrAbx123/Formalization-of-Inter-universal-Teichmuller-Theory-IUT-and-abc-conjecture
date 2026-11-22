/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.xif.paper.S1754OrbicurvePiFieldsActual
import tmp.sheaf.xif.paper.S1748FiniteEtaleFiberActual
import tmp.sheaf.xif.paper.S1740GaloisCorrespondenceActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual

/-!
# S1789: the continuous group comparison R3 for the actual cover category

## Question

S1754 reduced the two group-theoretic fields of an actual datum

  `D : Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve G`

to the single datum it calls Residual 3,

  `S1754S1726ComparisonMissing fiber = ((G : Type) ≃ₜ* Aut fiber)`,

for `G = Iut.AbsoluteGaloisProfinite S1726K` and `fiber` the fibre functor of the actual cover
category `Iut.OrbicurveFiniteEtaleCover S1726Orbicurve`.  This task asks: construct R3 for the
actual cover category (or for the `ContAction` model), using S1748 (the fibre functor of finite
etale algebras of a field), S1740 (the `ContAction` Galois correspondence) and the absolute
Galois group; and, if R3 needs a small model/category as a prerequisite, record exactly what.

## Answer: R3 is MISSING, and its exact content is recorded here

R3 is NOT constructed.  The file proves what R3 is equivalent to, so that nothing weaker can be
substituted for it, and records the exact prerequisites as types:

1. `S1789Certificate.nonempty_iff`: R3 (`G ≃ₜ* Aut fiber`) is inhabited iff the arithmetic
   certificate - an action of `G` on every fibre plus
   `PreGaloisCategory.IsFundamentalGroup fiber G` for that action - is inhabited.  Both
   directions are proved, with no sorry and no new axiom:
   * certificate -> R3 is Mathlib's `PreGaloisCategory.toAutHomeo` combined with
     `toAutMulEquiv` (`S1789Certificate.comparison`); this is the datum-wrapped construction
     of S1740 (`S1740ToAutContinuous`), here stated for a bare certificate;
   * R3 -> certificate is S1741's transport theorem with the tautological action transported
     along the comparison (`S1789Certificate.ofComparison`).

2. `S1789ActualComparison_eq_S1754`: R3 for the actual S1726 cover type is *definitionally*
   S1754's `S1754S1726ComparisonMissing` at `G = AbsoluteGaloisProfinite F'`.  So the missing
   type recorded below is exactly the one S1754 isolated, not a new variant.

3. `S1789ActualPieces.nonempty_iff_datum`: R3 plus the structural pieces (small model/category,
   Galois structure, fibre functor, geometric-fibre identification) is equivalent to the full
   S1726 datum `Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve
   (AbsoluteGaloisProfinite F')`, via S1754's `S1754Pieces.nonempty_iff`.  Hence R3 is exactly
   the last, arithmetic piece; the other pieces are recorded as `S1789SmallModelMissing`
   (S1728/S1754 R1) and `S1789FiberIdentificationMissing` (S1754 R2).  The recorded small
   model is exactly S1728's requirement: `S1789SmallModelMissing.smallRawCoverData` derives
   S1728's `S1728SmallRawCoverDataRequired` from it.

4. What S1748 gives, and why it is not R3: `s1789FiniteEtaleFiberComparison` is S1748's
   comparison `Aut (fiber K Kbar) ≃* (Kbar ≃ₐ[K] Kbar)` for the *finite etale algebra* fibre
   functor, conditional on S1748's `PostcompSurjective` (`S1789PostcompMissing`).  It is a
   group isomorphism for a *different* category and a *different* group:
   * `Aut` is taken in `(CommAlgCat.FiniteEtale K)ᵒᵖ`, not in the actual cover type;
   * the group is `AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`, whereas R3's group is
     `SeparableClosure K ≃ₐ[K] SeparableClosure K` (`S1789AbsoluteGaloisProfinite_eq`);
   * it is `≃*`, not `≃ₜ*`: R3 is a topological statement;
   * `PreGaloisCategory (FiniteEtale K)ᵒᵖ` and a `FiberFunctor` instance for that fibre are
     not in Mathlib (S1748, section 10).
   `S1789FieldModelTransfer` records the exact missing transfer datum.

5. What S1740/`ContAction` gives: S1740's Galois correspondence is conditional on the actual
   datum (hence on R3 and all of 3), and its upgrade to the literal group needs
   `S1740AllActionsContinuous (AbsoluteGaloisProfinite F')`, recorded here as
   `S1789AllActionsContinuousMissing`.  The `ContAction` model therefore does not supply R3
   either.

## Honest boundary

No `sorry`, no `admit`, no new `axiom`, no `Shrink`, `ULift`, `PLift` or `PUnit`, no
fake category, group, action or fibre functor.  Every declaration below is a real proof or a type
recording a missing datum; no inhabitant of R3, of the certificate, of the small model or of the
datum is fabricated.  In particular this file does NOT construct R3.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option autoImplicit false
set_option maxHeartbeats 2000000

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1754OrbicurvePiFieldsActual

namespace LeanFormal.IUT.XiFPaper.S1789ContinuousGroupComparisonActual

universe u v w g

/-! ## 1. R3 and the arithmetic certificate, for an abstract fibre functor -/

section General

variable {C : Type u} [Category.{v} C]

/-- **R3.**  A continuous group isomorphism between a compact topological group `G` and the
automorphism group of a fibre functor `Fib` (with Mathlib's compact totally disconnected topology
on `Aut Fib`, `Mathlib.CategoryTheory.Galois.Topology`).  This is the shape of S1754's
Residual 3 and of the group-theoretic fields of `Iut.OrbicurveEtaleFundamentalGroup`. -/
abbrev S1789Comparison (Fib : C ⥤ FintypeCat.{w}) (G : Type g) [Group G]
    [TopologicalSpace G] :=
  G ≃ₜ* Aut Fib

/-- **The arithmetic certificate** behind R3: an action of `G` on every fibre of `Fib`
together with the proof that `G`, with that action, is a fundamental group of `Fib`.  This
packages exactly the `action` and `isFundamentalGroup` fields of an actual datum, without the
categorical and geometric fields. -/
structure S1789Certificate (C : Type u) [Category.{v} C] [GaloisCategory C]
    (Fib : C ⥤ FintypeCat.{w}) [PreGaloisCategory.FiberFunctor Fib]
    (G : Type g) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] where
  /-- The action of the group on each fibre. -/
  action : ∀ X : C, MulAction G (Fib.obj X)
  /-- The certificate that the group is a fundamental group for the fibre functor. -/
  certificate :
    letI (X : C) := action X
    PreGaloisCategory.IsFundamentalGroup Fib G

namespace S1789Certificate

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
variable {Fib : C ⥤ FintypeCat.{w}} [PreGaloisCategory.FiberFunctor Fib]
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- The certificate gives R3: Mathlib's `toAutHomeo` composed with `toAutMulEquiv` is a
continuous group isomorphism.  This is the same construction as S1740's `S1740ToAutContinuous`,
without the datum wrapper. -/
noncomputable def comparison (cert : S1789Certificate C Fib G) :
    S1789Comparison Fib G := by
  letI (X : C) := cert.action X
  letI : PreGaloisCategory.IsFundamentalGroup Fib G := cert.certificate
  exact ContinuousMulEquiv.mk' (PreGaloisCategory.toAutHomeo Fib G)
    (fun x y => map_mul (PreGaloisCategory.toAutMulEquiv Fib G) x y)

/-- R3 gives the certificate: the action is the tautological `Aut Fib`-action transported
along the comparison, and the certificate is S1741's transport theorem. -/
noncomputable def ofComparison (e : S1789Comparison Fib G) :
    S1789Certificate C Fib G where
  action X := MulAction.compHom (Fib.obj X) (e : G →* Aut Fib)
  certificate := by
    letI (X : C) := MulAction.compHom (Fib.obj X) (e : G →* Aut Fib)
    exact S1741.isFundamentalGroup_of_continuousMulEquiv (F := Fib) e (fun g X x => rfl)

/-- **R3 is exactly the arithmetic certificate.**  In particular R3 cannot be weakened to a bare
group isomorphism (`≃*`) or to an action alone. -/
theorem nonempty_iff :
    Nonempty (S1789Certificate C Fib G) ↔ Nonempty (S1789Comparison Fib G) :=
  ⟨fun ⟨cert⟩ => ⟨cert.comparison⟩, fun ⟨e⟩ => ⟨ofComparison e⟩⟩

end S1789Certificate

end General

/-! ## 2. R3 for the actual S1726 cover type

The small category structure on the actual cover type, the Galois-category structure and the fibre
functor are section hypotheses here: they are exactly the prerequisites recorded in 2b below. -/

/-- **R3 for the actual cover category**: the absolute Galois group of `F'` is continuously
isomorphic to `Aut fiber`, where `fiber` is the fibre functor of the actual cover type
`Iut.OrbicurveFiniteEtaleCover S1726Orbicurve` under the given small category structure. -/
abbrev S1789ActualComparison
    [Category.{0} S1754S1726Cover] [GaloisCategory S1754S1726Cover]
    (fiber : S1754S1726Cover ⥤ FintypeCat.{0}) [PreGaloisCategory.FiberFunctor fiber] :=
  S1789Comparison fiber (Iut.AbsoluteGaloisProfinite S1726K : Type)

/-- The arithmetic certificate for the actual cover type: the absolute Galois group of `F'`
acts on every actual fibre and is the fundamental group of the fibre functor. -/
abbrev S1789ActualCertificate
    [Category.{0} S1754S1726Cover] [GaloisCategory S1754S1726Cover]
    (fiber : S1754S1726Cover ⥤ FintypeCat.{0}) [PreGaloisCategory.FiberFunctor fiber] :=
  S1789Certificate S1754S1726Cover fiber (Iut.AbsoluteGaloisProfinite S1726K : Type)

/-- **P1 (small model / category).**  A `Category.{0}` on the actual cover type together with
hom-wise equivalences to the actual cover maps, compatible with identity and composition
(S1728's smallness analysis, S1754's Residual 1).  Without it, `fiber` would be a functor on a
category unrelated to the actual covers. -/
def S1789SmallModelMissing : Type 1 :=
  { coverCategory : Category.{0} S1754S1726Cover //
    S1754S1726StrictRealizationMissing coverCategory }

/-- The recorded small-model prerequisite implies S1728's exact first missing smallness datum:
the categorical hom type is a small (`Type 0`) carrier equivalent to the actual cover-map type.
This is the sense in which the S1754 Residual 1 recorded here *is* S1728's requirement. -/
theorem S1789SmallModelMissing.smallRawCoverData (M : S1789SmallModelMissing) :
    LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper.S1728SmallRawCoverDataRequired := by
  rcases M with ⟨coverCategory, hM⟩
  letI := coverCategory
  rcases hM with ⟨realization⟩
  intro A B
  exact ⟨{ Carrier := (A ⟶ B), equiv := realization.equiv A B }⟩

/-- **P2 (geometric fibre identification).**  S1754's Residual 2: for a chosen small category
structure and fibre functor, the fibre functor is object-wise equivalent to the literal geometric
fibre at the chosen base scheme and base point. -/
abbrev S1789FiberIdentificationMissing (coverCategory : Category.{0} S1754S1726Cover)
    (fiber : letI := coverCategory; S1754S1726Cover ⥤ FintypeCat.{0}) : Type 1 :=
  S1754S1726FiberIdentificationMissing coverCategory fiber

section S1726

variable [Category.{0} S1754S1726Cover]
variable [GaloisCategory S1754S1726Cover]
variable (fiber : S1754S1726Cover ⥤ FintypeCat.{0})
variable [PreGaloisCategory.FiberFunctor fiber]

/-- R3 for the actual cover type is literally S1754's `S1754S1726ComparisonMissing`. -/
theorem S1789ActualComparison_eq_S1754 :
    S1789ActualComparison fiber =
      S1754S1726ComparisonMissing (G := Iut.AbsoluteGaloisProfinite S1726K)
        (fiber := fiber) := rfl

/-- **The exact group-theoretic content of R3 for the actual cover type**: it is equivalent to
the arithmetic certificate, i.e. to `PreGaloisCategory.IsFundamentalGroup fiber
(AbsoluteGaloisProfinite F')` for the transported action. -/
theorem S1789ActualComparison_iff_certificate :
    Nonempty (S1789ActualComparison fiber) ↔
      Nonempty (S1789ActualCertificate fiber) :=
  (S1789Certificate.nonempty_iff (C := S1754S1726Cover) (Fib := fiber)
    (G := (Iut.AbsoluteGaloisProfinite S1726K : Type))).symm

/-- **P3 (R3 itself).**  The arithmetic certificate for the actual cover type with the chosen
small category structure and fibre functor; by `S1789ActualComparison_iff_certificate` this is
equivalent to R3. -/
abbrev S1789CertificateMissing :=
  S1789ActualCertificate fiber

end S1726

/-! ## 3. Assembling the actual datum from R3 and the structural pieces

S1754's `S1754Pieces` has eleven fields: nine structural ones plus `action` and
`isFundamentalGroup`.  Here the two group fields are replaced by the single comparison R3.  The
two resulting structures are equivalent, and by S1754's `S1754Pieces.nonempty_iff` they are
equivalent to the full S1726 datum.  Hence R3 is exactly the last missing piece. -/

/-- The reduced piece list with R3 in place of the two group fields. -/
structure S1789ActualPieces where
  coverCategory : Category.{0} S1754S1726Cover
  galoisCategory :
    letI := coverCategory
    @GaloisCategory S1754S1726Cover coverCategory
  baseScheme : Iut.SchemeOverField S1726K
  basePoint :
    Pseudofunctor.StrongTrans
      (Iut.schemeRepresentableEtalePseudofunctor S1726K baseScheme)
      S1726Orbicurve.stack.fiber
  fiber :
    letI := coverCategory
    S1754S1726Cover ⥤ FintypeCat.{0}
  fiberFunctor :
    letI := coverCategory
    letI := galoisCategory
    PreGaloisCategory.FiberFunctor fiber
  real :
    letI := coverCategory
    S1754StrictCoverMapRealization S1726K S1726Orbicurve
  fiberIdentification :
    ∀ cover : S1754S1726Cover,
      (fiber.obj cover).obj ≃
        Iut.OrbicurveFiniteEtaleCover.GeometricFiber baseScheme basePoint cover
  fiberIdentification_natural :
    letI := coverCategory
    ∀ {source target : S1754S1726Cover}
      (map : source ⟶ target) (element : (fiber.obj source).obj),
      fiberIdentification target (fiber.map map element) =
        (Iut.OrbicurveFiniteEtaleCover.geometricFiberMap
          (real.map map) (real.overIso map)
          baseScheme basePoint).obj
            (fiberIdentification source element)
  /-- R3 for this fibre functor: the only arithmetic input. -/
  comparison :
    letI := coverCategory
    letI := galoisCategory
    letI := fiberFunctor
    S1789Comparison fiber (Iut.AbsoluteGaloisProfinite S1726K : Type)

namespace S1789ActualPieces

variable (P : S1789ActualPieces)

/-- R3 plus the structural pieces give S1754's reduced piece list: the action is the
tautological `Aut`-action transported along R3, and the certificate is S1741's transport. -/
noncomputable def toPieces :
    S1754Pieces S1726K S1726Orbicurve (Iut.AbsoluteGaloisProfinite S1726K) := by
  letI := P.coverCategory
  letI := P.galoisCategory
  letI := P.fiberFunctor
  letI (cover : S1754S1726Cover) :=
    MulAction.compHom (P.fiber.obj cover)
      (P.comparison : (Iut.AbsoluteGaloisProfinite S1726K : Type) →* Aut P.fiber)
  exact
    { coverCategory := P.coverCategory
      galoisCategory := P.galoisCategory
      baseScheme := P.baseScheme
      basePoint := P.basePoint
      fiber := P.fiber
      fiberFunctor := P.fiberFunctor
      real := P.real
      fiberIdentification := P.fiberIdentification
      fiberIdentification_natural := P.fiberIdentification_natural
      action := fun cover =>
        MulAction.compHom (P.fiber.obj cover)
          (P.comparison : (Iut.AbsoluteGaloisProfinite S1726K : Type) →* Aut P.fiber)
      isFundamentalGroup :=
        S1741.isFundamentalGroup_of_continuousMulEquiv (F := P.fiber)
          P.comparison (fun g X x => rfl) }

/-- The full S1726 datum obtained from R3 and the structural pieces. -/
noncomputable def toDatum :
    Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve
      (Iut.AbsoluteGaloisProfinite S1726K) :=
  P.toPieces.toDatum

/-- S1754's reduced piece list gives R3 for the actual cover type: the two group fields are
combined into the continuous comparison. -/
noncomputable def ofPieces
    (Q : S1754Pieces S1726K S1726Orbicurve (Iut.AbsoluteGaloisProfinite S1726K)) :
    S1789ActualPieces := by
  letI := Q.coverCategory
  letI := Q.galoisCategory
  letI := Q.fiberFunctor
  letI (cover : S1754S1726Cover) := Q.action cover
  letI : PreGaloisCategory.IsFundamentalGroup Q.fiber
      (Iut.AbsoluteGaloisProfinite S1726K : Type) := Q.isFundamentalGroup
  exact
    { coverCategory := Q.coverCategory
      galoisCategory := Q.galoisCategory
      baseScheme := Q.baseScheme
      basePoint := Q.basePoint
      fiber := Q.fiber
      fiberFunctor := Q.fiberFunctor
      real := Q.real
      fiberIdentification := Q.fiberIdentification
      fiberIdentification_natural := Q.fiberIdentification_natural
      comparison :=
        ContinuousMulEquiv.mk'
          (PreGaloisCategory.toAutHomeo Q.fiber (Iut.AbsoluteGaloisProfinite S1726K : Type))
          (fun x y =>
            map_mul (PreGaloisCategory.toAutMulEquiv Q.fiber
              (Iut.AbsoluteGaloisProfinite S1726K : Type)) x y) }

/-- R3 plus the structural pieces is equivalent to S1754's reduced piece list. -/
theorem nonempty_iff_pieces :
    Nonempty S1789ActualPieces ↔
      Nonempty (S1754Pieces S1726K S1726Orbicurve
        (Iut.AbsoluteGaloisProfinite S1726K)) :=
  ⟨fun ⟨P⟩ => ⟨P.toPieces⟩, fun ⟨Q⟩ => ⟨ofPieces Q⟩⟩

/-- **R3 plus the structural pieces is equivalent to the full S1726 datum.**  Hence R3 is
exactly the last (arithmetic) missing piece, and constructing it is neither weaker nor stronger
than supplying the two group-theoretic fields of the datum. -/
theorem nonempty_iff_datum :
    Nonempty S1789ActualPieces ↔
      Nonempty (Iut.OrbicurveEtaleFundamentalGroup S1726Orbicurve
        (Iut.AbsoluteGaloisProfinite S1726K)) :=
  nonempty_iff_pieces.trans
    (S1754Pieces.nonempty_iff (F := S1726K) (X := S1726Orbicurve)
      (G := Iut.AbsoluteGaloisProfinite S1726K))

end S1789ActualPieces

/-! ## 4. What S1748 supplies, and why it is not R3 -/

section FieldModel

open S1748FiniteEtaleFiber

variable (K : Type) [Field K]

/-- **S1748's comparison.**  For the fibre functor of finite etale `K`-algebras at an algebraic
closure, natural automorphisms are `K`-automorphisms of the algebraic closure, conditional on
S1748's `PostcompSurjective`.  This is a genuine theorem of S1748, reused here unchanged. -/
noncomputable def s1789FiniteEtaleFiberComparison
    (h : PostcompSurjective (K := K) (Ω := AlgebraicClosure K)) :
    Aut (absoluteFiber (K := K)) ≃* (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
  autFiberEquivOfSurjective h

/-- The exact missing statement on S1748's side. -/
def S1789PostcompMissing (K : Type) [Field K] : Prop :=
  PostcompSurjective (K := K) (Ω := AlgebraicClosure K)

/-- R3's group is the automorphism group of the *separable* closure (with the Krull topology),
not the automorphism group of the algebraic closure appearing in S1748's fibre functor. -/
theorem S1789AbsoluteGaloisProfinite_eq (K : Type) [Field K] :
    (Iut.AbsoluteGaloisProfinite K : Type) =
      (SeparableClosure K ≃ₐ[K] SeparableClosure K) := rfl

end FieldModel

/-- The exact transfer datum that S1748's comparison would need in order to become R3 for the
actual cover category.  None of its fields is available in the tree; it is recorded, never assumed
as an instance. -/
structure S1789FieldModelTransfer where
  /-- The actual cover category carries a small category structure (S1728). -/
  coverCategory : Category.{0} S1754S1726Cover
  /-- An equivalence of the actual cover category with the finite etale algebras of `F'`,
  which would give in particular that the two fibre functors have the same `Aut`. -/
  modelEquivalence :
    letI := coverCategory
    S1754S1726Cover ≌ (CommAlgCat.FiniteEtale.{0} S1726K)ᵒᵖ
  /-- The topological comparison on the group side: the Krull-topological absolute Galois group
  is the automorphism group of the finite etale fibre functor.  This is *not* S1748's `≃*`. -/
  groupComparison :
    (Iut.AbsoluteGaloisProfinite S1726K : Type) ≃ₜ*
      Aut (CommAlgCat.FiniteEtale.fiber S1726K (AlgebraicClosure S1726K))

/-! ## 5. What S1740 / the `ContAction` model supplies -/

section ContAction

open LeanFormal.IUT.XiFPaper.S1740GaloisCorrespondenceActual

/-- **The missing input of the `ContAction` route for the literal group.**  S1740's Galois
correspondence is proved for the certified arithmetic group of an actual datum; upgrading it to
the literal group `AbsoluteGaloisProfinite F'` requires that every finite action of that group
is continuous, equivalently that every finite-index subgroup is open.  Not available in the
tree. -/
abbrev S1789AllActionsContinuousMissing : Prop :=
  S1740AllActionsContinuous (Iut.AbsoluteGaloisProfinite S1726K)

end ContAction

/-! ## 6. Axiom footprint -/

#print axioms S1789Certificate.comparison
#print axioms S1789Certificate.ofComparison
#print axioms S1789Certificate.nonempty_iff
#print axioms S1789SmallModelMissing.smallRawCoverData
#print axioms S1789ActualComparison_eq_S1754
#print axioms S1789ActualComparison_iff_certificate
#print axioms S1789ActualPieces.toPieces
#print axioms S1789ActualPieces.toDatum
#print axioms S1789ActualPieces.nonempty_iff_pieces
#print axioms S1789ActualPieces.nonempty_iff_datum
#print axioms s1789FiniteEtaleFiberComparison
#print axioms S1789AbsoluteGaloisProfinite_eq

end LeanFormal.IUT.XiFPaper.S1789ContinuousGroupComparisonActual