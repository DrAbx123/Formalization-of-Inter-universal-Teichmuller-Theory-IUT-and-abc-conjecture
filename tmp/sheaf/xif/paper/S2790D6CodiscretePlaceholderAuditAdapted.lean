import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31OrbicurveInstance
import LeanFormal.IUT.IUTII.Frobenioid.Example36OrbicurveFeasibility

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.OrbicurveFeasibility
open CategoryTheory
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2790D6CodiscretePlaceholderAuditAdapted

universe u v

/-- A codiscrete category with hom types lifted to `Type u`, so that it lives
in `Cat.{u,u}` (the universe expected by `EtaleStackPseudofunctor`). -/
structure S2790CodiscreteCat (A : Type u) where
  as : A

namespace S2790CodiscreteCat

instance : Category (S2790CodiscreteCat A) where
  Hom _ _ := ULift.{u} Unit
  id _ := ULift.up ()
  comp _ _ := ULift.up ()

instance uniqueHom (A : Type u) (x y : S2790CodiscreteCat A) : Unique (x ⟶ y) where
  default := ULift.up ()
  uniq _ := by cases ‹x ⟶ y›; rfl

instance subsingletonHom (A : Type u) (x y : S2790CodiscreteCat A) :
    Subsingleton (x ⟶ y) :=
  ⟨fun _ _ => by cases ‹x ⟶ y›; rfl⟩

def iso (x y : S2790CodiscreteCat A) : x ≅ y where
  hom := ULift.up ()
  inv := ULift.up ()

end S2790CodiscreteCat

noncomputable def codiscreteConstantFiberFunctor
    (F : Type u) [CommRing F] (A : Type u) :
    (Iut.SchemeOverField F)ᵒᵖ ⥤ Cat.{u, u} where
  obj _ := Cat.of (S2790CodiscreteCat A)
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def codiscreteConstantFiber
    (F : Type u) [CommRing F] (A : Type u) :
    LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{u, u} :=
  (codiscreteConstantFiberFunctor F A).toPseudofunctor'

instance codiscreteConstantFiberDescentDataHomSubsingleton
    (F : Type u) [CommRing F] (A : Type u)
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S)
    (D₁ D₂ : (codiscreteConstantFiber F A).DescentData f) :
    Subsingleton (D₁ ⟶ D₂) :=
  ⟨fun φ ψ =>
    Pseudofunctor.DescentData.hom_ext fun i => Subsingleton.elim _ _⟩

theorem codiscreteConstantFiber_toDescentData_faithful
    (F : Type u) [CommRing F] (A : Type u)
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) :
    ((codiscreteConstantFiber F A).toDescentData f).Faithful :=
  ⟨fun {U V} _ _ _ => Subsingleton.elim _ _⟩

theorem codiscreteConstantFiber_toDescentData_full
    (F : Type u) [CommRing F] (A : Type u)
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) :
    ((codiscreteConstantFiber F A).toDescentData f).Full :=
  ⟨fun {U V} _ => ⟨ULift.up (), Subsingleton.elim _ _⟩⟩

theorem codiscreteConstantFiber_toDescentData_essSurj
    (F : Type u) [CommRing F] (A : Type u) [Nonempty A]
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) :
    ((codiscreteConstantFiber F A).toDescentData f).EssSurj where
  mem_essImage _ := by
    refine ⟨S2790CodiscreteCat.mk (Classical.choice (inferInstance : Nonempty A)), ?_⟩
    exact { hom := { hom := fun _ => ULift.up (),
                     comm := fun _ _ _ _ _ _ _ _ => Subsingleton.elim _ _ },
            inv := { hom := fun _ => ULift.up (),
                     comm := fun _ _ _ _ _ _ _ _ => Subsingleton.elim _ _ },
            hom_inv_id := Subsingleton.elim _ _,
            inv_hom_id := Subsingleton.elim _ _ }

theorem codiscreteConstantFiber_toDescentData_isEquivalence
    (F : Type u) [CommRing F] (A : Type u) [Nonempty A]
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) :
    ((codiscreteConstantFiber F A).toDescentData f).IsEquivalence :=
  ⟨codiscreteConstantFiber_toDescentData_faithful F A f,
   codiscreteConstantFiber_toDescentData_full F A f,
   codiscreteConstantFiber_toDescentData_essSurj F A f⟩

theorem codiscreteConstantFiber_isStackFor_ofArrows
    (F : Type u) [CommRing F] (A : Type u) [Nonempty A]
    {ι : Type v} {S : Iut.SchemeOverField F} {X : ι → Iut.SchemeOverField F}
    (f : ∀ i, X i ⟶ S) :
    (codiscreteConstantFiber F A).IsStackFor (Presieve.ofArrows X f) :=
  (Pseudofunctor.isStackFor_ofArrows_iff (F := codiscreteConstantFiber F A) f).2
    (codiscreteConstantFiber_toDescentData_isEquivalence F A f)

theorem codiscreteConstantFiber_isStack
    (F : Type u) [CommRing F] (A : Type u) [Nonempty A] :
    (codiscreteConstantFiber F A).IsStack
      (Iut.SchemeOverField.etaleTopology F) :=
  Pseudofunctor.IsStack.of_isStackFor fun S R hR => by
    rw [← Presieve.ofArrows_category R.arrows]
    exact codiscreteConstantFiber_isStackFor_ofArrows F A
      (fun (f : R.arrows.category) => f.obj.hom)

/-- Structural candidate: the current `MissingD6GeometricRealization` structure
is inhabited by a codiscrete constant fibre over the curve points.  This is a
placeholder, not a faithful curve stack. -/
noncomputable def S2790PlaceholderD6
    (F : Type u) [Field F] (X : PuncturedEllipticCurve F)
    (h2 : ∃ a b : X.curve.toProjective.Point, a ≠ b) :
    MissingD6GeometricRealization F where
  curve := X
  fiber := codiscreteConstantFiber F X.curve.toProjective.Point
  isStack :=
    letI : Nonempty X.curve.toProjective.Point := ⟨0⟩
    codiscreteConstantFiber_isStack F X.curve.toProjective.Point
  nondegenerate := by
    intro hpoint
    obtain ⟨a, b, hab⟩ := h2
    have hsub : Subsingleton (S2790CodiscreteCat X.curve.toProjective.Point) :=
      hpoint (Opposite.op (baseSchemeObject F))
    exact hab (congrArg S2790CodiscreteCat.as (Subsingleton.elim
      (S2790CodiscreteCat.mk a) (S2790CodiscreteCat.mk b)))
  curvePointRealization :=
    letI : Nonempty X.curve.toProjective.Point := ⟨0⟩
    ⟨fun P => P.as, fun p => ⟨S2790CodiscreteCat.mk p, rfl⟩⟩

#check codiscreteConstantFiber
#check codiscreteConstantFiber_isStack
#check S2790PlaceholderD6

end LeanFormal.IUT.XiFPaper.S2790D6CodiscretePlaceholderAuditAdapted
end
