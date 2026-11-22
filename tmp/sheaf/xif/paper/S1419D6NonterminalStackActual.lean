import tmp.sheaf.xif.paper.S1331OrbicurveClauseAudit
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
import tmp.sheaf.xif.paper.S1382OrbifoldPiActual
import tmp.sheaf.n8.closure.RepresentableStackIsStackConstructed
import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib.CategoryTheory.Sites.Sheaf
import LeanFormal.IUT.IUTI.HodgeTheater.SourceClauseAssemblyUnitsReduction

/-!
# S1419: an actual nonterminal hyperbolic orbicurve from the S1348 cover data

This file constructs the actual nonterminal stack-level object that S1319,
S1348 and S1359 isolate as the remaining D6 first field.

## Main result

The missing mathematical input of the D6 first field is the bridge

  a sheaf of types P on the etale site  ->  the discrete-category
  pseudofunctor  U |-> Discrete (P U)  is an etale stack.

The bridge is proved here, for an arbitrary Grothendieck topology and an
arbitrary sheaf of types (discretePseudo_isStack).  The proof constructs the
gluing of a descent datum from the sheaf amalgamation and uses the
subsingleton hom types of discrete categories for fullness and faithfulness.

Applied to the representable sheaf of the actual S1348 affine Gaussian scheme
Spec K[x,y]/(y^2 + xy - x^3 - 5), this gives an actual etale stack over the
S1280 Gaussian field K.  The stack is nonterminal: at the base test scheme,
the two distinct actual points (1,2) and (1,-3) of S1331 give two distinct
sections, and the representable fiber is not a subsingleton
(S1419Nonterminal).  Hence the realized hyperbolic orbicurve
S1419Orbicurve l is a literal HyperbolicOrbicurve K, not a terminal or
point fiber, with the once-punctured elliptic signature.

The non-group prefix of the D6 first field is therefore constructed:
S1419FirstField l : S1359FirstField l.  The residual field after it is
exactly the certified orbifold fundamental-group data
S1359OrbifoldPiRemainder l (S1419FirstField l); the constructor
S1419ExactFirstField and the reduction S1419OrbifoldPiData are provided.
No l-torsion sequence, terminal stack, point fiber, PUnit, arbitrary carrier,
axiom or sorry is used.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped SpecOfNotation
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1331OrbicurveClauseAudit
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1359OrbifoldPiActual
open LeanFormal.IUT.XiFPaper.S1382OrbifoldPiActual
open LeanFormal.IUT.XiFPaper.S1319OrbicurveClauseActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open LeanFormal.IUT.N8Closure.DiscreteSheafIsStack
open LeanFormal.IUT.N8Closure.RepresentableStackIsStackConstructed

universe v u

/-! ## 1. The discrete-sheaf descent functor is an equivalence -/

namespace DiscreteSheafStack

variable {C : Type u} [Category.{v} C]

/-- The compatible family of a descent datum of the discrete pseudofunctor. -/
noncomputable def fam (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)
    (D : (discretePseudo P).DescentData (fun i : S.arrows.category => i.obj.hom)) :
    Presieve.FamilyOfElements P S.arrows :=
  fun _ f hf => (D.obj ⟨Over.mk f, hf⟩).as

variable (P : Cᵒᵖ ⥤ Type v) {X : C} (S : Sieve X)

theorem fam_compatible (D : (discretePseudo P).DescentData
    (fun i : S.arrows.category => i.obj.hom)) :
    (fam P S D).Compatible := by
  rw [Presieve.compatible_iff_sieveCompatible]
  intro Y Z u g hu
  let i₁ : S.arrows.category := ⟨Over.mk u, hu⟩
  let i₂ : S.arrows.category := ⟨Over.mk (g ≫ u), S.downward_closed hu g⟩
  have hD := D.hom (Y := Z) (q := g ≫ u) (i₁ := i₁) (i₂ := i₂)
    (f₁ := g) (f₂ := 𝟙 Z) (by rfl) (by exact Category.id_comp (g ≫ u))
  have hEq := Discrete.eq_of_hom hD
  change (Discrete.mk (P.map g.op (D.obj i₁).as)).as =
    (Discrete.mk (P.map (𝟙 Z).op (D.obj i₂).as)).as at hEq
  rw [show P.map (𝟙 Z).op (D.obj i₂).as = (D.obj i₂).as by simp] at hEq
  exact hEq.symm

variable (D : (discretePseudo P).DescentData (fun i : S.arrows.category => i.obj.hom))
  (hS : Presieve.IsSheafFor P S.arrows)

/-- The sheaf amalgamation of the family of a descent datum. -/
noncomputable def glue : P.obj (Opposite.op X) :=
  hS.amalgamate (fam P S D) (fam_compatible P S D)

theorem glue_spec (i : S.arrows.category) :
    P.map i.obj.hom.op (glue P S D hS) = (D.obj i).as :=
  hS.isAmalgamation (fam_compatible P S D) i.obj.hom i.property

theorem toDescentData_glue_obj (i : S.arrows.category) :
    (((discretePseudo P).toDescentData (fun i : S.arrows.category => i.obj.hom)).obj
        (Discrete.mk (glue P S D hS))).obj i = D.obj i := by
  change Discrete.mk (P.map i.obj.hom.op (glue P S D hS)) = D.obj i
  rw [glue_spec P S D hS i, Discrete.mk_as]

/-- Essential surjectivity of the discrete descent functor, from the sheaf
amalgamation. -/
noncomputable def essSurj : ((discretePseudo P).toDescentData
    (fun i : S.arrows.category => i.obj.hom)).EssSurj where
  mem_essImage D := ⟨Discrete.mk (glue P S D hS), ⟨by
    refine Pseudofunctor.DescentData.isoMk
      (fun i => eqToIso (toDescentData_glue_obj P S D hS i)) ?_
    intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
    exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _⟩⟩

/-- Fullness of the discrete descent functor: a morphism of descent data gives
componentwise equalities of objects, and separatedness of the sheaf identifies
the two global amalgamations. -/
theorem full (hS : Presieve.IsSheafFor P S.arrows) :
    ((discretePseudo P).toDescentData (fun i : S.arrows.category => i.obj.hom)).Full where
  map_surjective {x₁ x₂} φ := by
    have hx : x₁.as = x₂.as := by
      apply (Presieve.IsSheafFor.isSeparatedFor hS).ext
      intro Y f hf
      let i : S.arrows.category := ⟨Over.mk f, hf⟩
      have h := Discrete.eq_of_hom (φ.hom i)
      change P.map f.op x₁.as = P.map f.op x₂.as at h
      exact h
    refine ⟨Discrete.eqToHom hx, ?_⟩
    haveI : Subsingleton
        (((discretePseudo P).toDescentData (fun i : S.arrows.category => i.obj.hom)).obj x₁ ⟶
          ((discretePseudo P).toDescentData (fun i : S.arrows.category => i.obj.hom)).obj x₂) := by
      constructor
      intro f g
      apply Pseudofunctor.DescentData.hom_ext
      intro i
      exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _
    exact Subsingleton.elim _ _

/-- Faithfulness: the source category is discrete. -/
theorem faithful : ((discretePseudo P).toDescentData
    (fun i : S.arrows.category => i.obj.hom)).Faithful where
  map_injective {x₁ x₂} f g h := by
    exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom x₁ x₂) f g

theorem isEquivalence (hS : Presieve.IsSheafFor P S.arrows) :
    ((discretePseudo P).toDescentData
      (fun i : S.arrows.category => i.obj.hom)).IsEquivalence :=
  { faithful := faithful P S
    full := full P S hS
    essSurj := essSurj P S hS }

theorem isStackFor (hS : Presieve.IsSheafFor P S.arrows) :
    (discretePseudo P).IsStackFor S.arrows :=
  (Pseudofunctor.isStackFor_iff _ _).2 (isEquivalence P S hS)

/-- The discrete-sheaf-to-stack bridge. -/
theorem discretePseudo_isStack {J : GrothendieckTopology C}
    (hP : Presieve.IsSheaf J P) :
    (discretePseudo P).IsStack J := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro X S hS
  exact isStackFor P S (hP.isSheafFor S.arrows (by simpa using hS))

end DiscreteSheafStack

/-! ## 2. The representable etale stack -/

/-- The actual affine Gaussian scheme of the S1348 coordinate ring. -/
noncomputable abbrev S1419AffineScheme (l : PrimeGeFive) : Scheme :=
  Spec (CommRingCat.of (S1348CoordinateRing l))

/-- The S1348 affine Gaussian scheme as a scheme over the S1280 field. -/
noncomputable abbrev S1419AffineOver (l : PrimeGeFive) :
    Iut.SchemeOverField (S1348K l) :=
  Over.mk (Spec.map (CommRingCat.ofHom
    (algebraMap (S1348K l) (S1348CoordinateRing l))))

/-- The base test scheme Spec K over Spec K. -/
noncomputable abbrev S1419Base (l : PrimeGeFive) :
    Iut.SchemeOverField (S1348K l) :=
  Over.mk (𝟙 (Spec (CommRingCat.of (S1348K l))))

/-- An algebra point R -> K gives an actual section Spec K -> Spec R over
Spec K. -/
noncomputable def S1419OverOfAlgHom (l : PrimeGeFive)
    (ψ : S1348CoordinateRing l →ₐ[S1348K l] S1348K l) :
    S1419Base l ⟶ S1419AffineOver l :=
  Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (by
    dsimp [S1419Base, S1419AffineOver]
    erw [← Spec.map_comp]
    rw [← CommRingCat.ofHom_comp]
    have h : ψ.toRingHom.comp (algebraMap (S1348K l) (S1348CoordinateRing l)) =
        RingHom.id (S1348K l) := by
      ext x
      exact ψ.commutes x
    change Spec.map (CommRingCat.ofHom
      (ψ.toRingHom.comp (algebraMap (S1348K l) (S1348CoordinateRing l)))) =
      𝟙 (Spec (CommRingCat.of (S1348K l)))
    rw [h]
    change Spec.map (𝟙 (CommRingCat.of (S1348K l))) =
      𝟙 (Spec (CommRingCat.of (S1348K l)))
    rw [Spec.map_id])

theorem S1419OverOfAlgHom_injective (l : PrimeGeFive) :
    Function.Injective (S1419OverOfAlgHom l) := by
  intro ψ₁ ψ₂ h
  have hleft : (S1419OverOfAlgHom l ψ₁).left =
      (S1419OverOfAlgHom l ψ₂).left :=
    congrArg (fun f => f.left) h
  change Spec.map (CommRingCat.ofHom ψ₁.toRingHom) =
    Spec.map (CommRingCat.ofHom ψ₂.toRingHom) at hleft
  have hringCat := Spec.map_injective hleft
  have hring : ψ₁.toRingHom = ψ₂.toRingHom :=
    congrArg CommRingCat.Hom.hom hringCat
  ext x
  exact congrArg (fun φ : S1348CoordinateRing l →+* S1348K l => φ x) hring

/-- The representable fiber at the base test scheme has two distinct actual
sections, coming from the two distinct punctured points of S1331 and the
surjectivity of the S1348 algebra-point map. -/
theorem S1419Nonterminal (l : PrimeGeFive) :
    ¬ Subsingleton (S1419Base l ⟶ S1419AffineOver l) := by
  intro hsub
  let P₁ : S1331ClausePuncturedCurve l :=
    ⟨S1331Point l, S1331Point_ne_puncture l⟩
  let P₂ : S1331ClausePuncturedCurve l :=
    ⟨S1331PointNeg l, S1331PointNeg_ne_puncture l⟩
  obtain ⟨ψ₁, h₁⟩ := S1348PointAlgHom_surjective l P₁
  obtain ⟨ψ₂, h₂⟩ := S1348PointAlgHom_surjective l P₂
  have hP : P₁ ≠ P₂ := by
    intro h
    exact S1331Point_ne_S1331PointNeg l (congrArg Subtype.val h)
  have hψ : ψ₁ ≠ ψ₂ := by
    intro h
    apply hP
    rw [← h₁, ← h₂, h]
  have hover : S1419OverOfAlgHom l ψ₁ ≠ S1419OverOfAlgHom l ψ₂ :=
    fun h => hψ (S1419OverOfAlgHom_injective l h)
  exact hover (Subsingleton.elim _ _)

/-- The representable pseudofunctor of the actual S1348 affine scheme is an
etale stack. -/
theorem S1419RepresentableIsStack (l : PrimeGeFive) :
    (Iut.schemeRepresentableEtalePseudofunctor (S1348K l) (S1419AffineOver l)).IsStack
      (Iut.SchemeOverField.etaleTopology (S1348K l)) := by
  have hP : Presieve.IsSheaf (Iut.SchemeOverField.etaleTopology (S1348K l))
      (yoneda.obj (S1419AffineOver l)) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (representableEtalePresheaf_isSheaf
        (F := S1348K l) (S1419AffineOver l))
  change (discretePseudo (C := Iut.SchemeOverField (S1348K l))
    (yoneda.obj (S1419AffineOver l))).IsStack
      (Iut.SchemeOverField.etaleTopology (S1348K l))
  exact DiscreteSheafStack.discretePseudo_isStack (P := yoneda.obj (S1419AffineOver l)) hP

/-- The actual nonterminal hyperbolic orbicurve. -/
noncomputable def S1419Orbicurve (l : PrimeGeFive) :
    Iut.HyperbolicOrbicurve (S1348K l) :=
  realizedHyperbolicOrbicurve (S1348K l)
    (Iut.schemeRepresentableEtalePseudofunctor (S1348K l) (S1419AffineOver l))
    (S1419RepresentableIsStack l)
    Iut.OrbicurveSignature.oncePuncturedElliptic
    Iut.OrbicurveSignature.oncePuncturedElliptic_isHyperbolic

theorem S1419Orbicurve_signature (l : PrimeGeFive) :
    (S1419Orbicurve l).signature = Iut.OrbicurveSignature.oncePuncturedElliptic :=
  rfl

/-- The actual orbicurve is nonterminal. -/
theorem S1419NonterminalFiber (l : PrimeGeFive) :
    S1319NonterminalFiber (S1419Orbicurve l) := by
  refine ⟨Opposite.op (S1419Base l), ?_⟩
  intro hsub
  apply S1419Nonterminal l
  have hsub' : Subsingleton
      (Discrete (S1419Base l ⟶ S1419AffineOver l)) := hsub
  haveI := hsub'
  constructor
  intro f g
  have h : (Discrete.mk f : Discrete (S1419Base l ⟶ S1419AffineOver l)) =
      Discrete.mk g := Subsingleton.elim _ _
  exact congrArg Discrete.as h

/-- The non-group prefix of the D6 first field: the actual nonterminal
hyperbolic orbicurve with the once-punctured elliptic signature. -/
noncomputable def S1419FirstField (l : PrimeGeFive) : S1359FirstField l where
  X := S1419Orbicurve l
  nonterminal := S1419NonterminalFiber l
  signature := S1419Orbicurve_signature l

/-- The full exact first field: the non-group prefix together with the
certified orbifold fundamental-group data.  This is the exact residual field. -/
noncomputable def S1419ExactFirstField (l : PrimeGeFive)
    (groups : S1359OrbifoldPiRemainder l (S1419FirstField l)) :
    S1382OrbifoldPiExactFirstField l :=
  ⟨S1419FirstField l, groups⟩

/-- The exact first field of the source exact-sequence slot: the actual
nonterminal X together with the residual certified orbifold group data. -/
noncomputable def S1419D6FirstMissingFieldOfGroups (l : PrimeGeFive)
    (groups : Iut.OrbicurveFundamentalGroupData (S1419Orbicurve l)
      (Iut.AbsoluteGaloisProfinite (S1348K l))) :
    S1348D6FirstMissingField l :=
  ⟨S1419Orbicurve l, groups⟩

@[simp] theorem S1419D6FirstMissingFieldOfGroups_fst (l : PrimeGeFive)
    (groups : Iut.OrbicurveFundamentalGroupData (S1419Orbicurve l)
      (Iut.AbsoluteGaloisProfinite (S1348K l))) :
    (S1419D6FirstMissingFieldOfGroups l groups).1 = S1419Orbicurve l := rfl

/-- The corresponding frozen D6 orbifold-Pi data, from the actual first field
and the residual group data. -/
noncomputable def S1419OrbifoldPiData (l : PrimeGeFive)
    (groups : S1359OrbifoldPiRemainder l (S1419FirstField l)) :
    S1319OrbifoldPiData l :=
  S1359OrbifoldPiDataOf l (S1419FirstField l) groups

@[simp] theorem S1419FirstField_X (l : PrimeGeFive) :
    (S1419FirstField l).X = S1419Orbicurve l := rfl

theorem S1419FirstField_signature (l : PrimeGeFive) :
    (S1419FirstField l).X.signature =
      Iut.OrbicurveSignature.oncePuncturedElliptic := rfl

theorem S1419FirstField_not_pointFiber (l : PrimeGeFive) :
    ¬ IsPointFiber (S1419FirstField l).X.stack.fiber :=
  (S1359NonterminalFiber_iff_notPointFiber l (S1419FirstField l).X).mp
    (S1419FirstField l).nonterminal

/-! ## 3. Axiom footprint -/

#print axioms S1419Nonterminal
#print axioms S1419RepresentableIsStack
#print axioms S1419Orbicurve
#print axioms S1419NonterminalFiber
#print axioms S1419FirstField
#print axioms S1419ExactFirstField
#print axioms S1419D6FirstMissingFieldOfGroups
#print axioms S1419FirstField_not_pointFiber

end LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual

end
