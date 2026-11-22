
/-! ## 3. A^G as the limit of the action

Let F : (SingleObj G)^op ⥤ CommAlgCat.FiniteEtale K be a G-action on a finite etale
K-algebra A (a functor out of the one-object groupoid (SingleObj G)^op whose hom
types are G^op).  We show that the cone with point A^G and structural maps the
inclusions A^G -> A is a limit cone.  Consequently (FiniteEtale K)^op has colimits of
shape SingleObj G: the quotient of A by G. -/

section Limit

variable {K : Type u} [Field K] {G : Type u} [Group G]

/-- The single object of the action shape (SingleObj G)^op. -/
def shapePoint (G : Type u) : (SingleObj G)ᵒᵖ := Opposite.op (SingleObj.star G)

/-- The finite etale K-algebra carrying the action. -/
abbrev actionAlgebra (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) : Type u :=
  F.obj (shapePoint G)

/-- The action of g : G on A = actionAlgebra F. -/
def actionMap (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) (g : G) :
    actionAlgebra F →ₐ[K] actionAlgebra F :=
  (F.map (Opposite.op g)).hom.hom

/-- The invariant subalgebra A^G. -/
def invariants (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    Subalgebra K (actionAlgebra F) :=
  fixedSubalgebra (K := K) (A := actionAlgebra F) G (actionMap F)

instance invariantsFinite (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    Module.Finite K ↥(invariants F) :=
  inferInstance

/-- A^G is etale over K: it is a subalgebra of the finite etale algebra A. -/
instance invariantsEtale (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    Algebra.Etale K ↥(invariants F) :=
  etale_subalgebra (invariants F)

/-- The invariant subalgebra A^G, as an object of the category of finite etale
K-algebras. -/
def invariantsObject (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    CommAlgCat.FiniteEtale.{u} K :=
  CommAlgCat.FiniteEtale.of K ↥(invariants F)

/-- The structural map A^G -> A of the cone over the action. -/
def invariantsMap (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K)
    (j : (SingleObj G)ᵒᵖ) : invariantsObject F ⟶ F.obj j :=
  { hom := CommAlgCat.ofHom
      (Subalgebra.val (invariants F) : ↥(invariants F) →ₐ[K] (F.obj j).obj) }

/-- The quotient map A -> A^G, viewed in the opposite category (FiniteEtale K)^op. -/
def quotientMap (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    Opposite.op (F.obj (shapePoint G)) ⟶ Opposite.op (invariantsObject F) :=
  Quiver.Hom.op (invariantsMap F (shapePoint G))

/-- The structural maps are compatible with the action: this is the defining property
of A^G. -/
theorem invariantsMap_naturality (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K)
    {j j' : (SingleObj G)ᵒᵖ} (f : j ⟶ j') :
    invariantsMap F j' = invariantsMap F j ≫ F.map f := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  show (Subalgebra.val (invariants F) : ↥(invariants F) →ₐ[K] (F.obj j').obj) =
    ((F.map f).hom.hom).comp
      (Subalgebra.val (invariants F) : ↥(invariants F) →ₐ[K] (F.obj j).obj)
  apply AlgHom.ext
  intro x
  show (Subalgebra.val (invariants F)) x =
    ((F.map f).hom.hom) ((Subalgebra.val (invariants F)) x)
  have hf : f = Opposite.op (Opposite.unop f) := (Opposite.op_unop f).symm
  rw [hf]
  exact (x.2 (Opposite.unop f)).symm

/-- The cone over a G-action with point A^G and structural maps the inclusions
A^G -> A. -/
def invariantsCone (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) : Cone F where
  pt := invariantsObject F
  π :=
    { app := invariantsMap F
      naturality := by
        intro j j' f
        exact invariantsMap_naturality F f }

/-- The factorisation of an arbitrary cone over the action through A^G. -/
def invariantsLift (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) (c : Cone F) :
    c.pt ⟶ (invariantsCone F).pt :=
  { hom := CommAlgCat.ofHom
      (AlgHom.codRestrict ((c.π.app (shapePoint G)).hom.hom) (invariants F) (by
        intro x
        show ∀ g : G, actionMap F g ((c.π.app (shapePoint G)).hom.hom x) =
          (c.π.app (shapePoint G)).hom.hom x
        intro g
        exact congrArg (fun (m : c.pt ⟶ F.obj (shapePoint G)) => m.hom.hom x)
          (Cone.w (j := shapePoint G) (j' := shapePoint G) c (Opposite.op g)))) }

/-- The factorisation given by invariantsLift makes the triangles commute. -/
theorem invariantsLift_fac (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K)
    (c : Cone F) (j : (SingleObj G)ᵒᵖ) :
    invariantsLift F c ≫ (invariantsCone F).π.app j = c.π.app j := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  rfl

/-- Universal property of A^G. The cone invariantsCone F is a limit cone: every
cone over the G-action factors uniquely through A^G = invariants F. -/
def invariantsIsLimit (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    IsLimit (invariantsCone F) where
  lift := invariantsLift F
  fac := invariantsLift_fac F
  uniq c m hm := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    have h3 : m ≫ (invariantsCone F).π.app (shapePoint G) =
        invariantsLift F c ≫ (invariantsCone F).π.app (shapePoint G) := by
      rw [hm (shapePoint G), invariantsLift_fac F c (shapePoint G)]
    have h4 := congrArg (fun (g : c.pt ⟶ F.obj (shapePoint G)) => (g.hom.hom) x) h3
    exact Subtype.ext h4

instance hasLimitInvariants (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} K) :
    HasLimit F :=
  HasLimit.mk ⟨invariantsCone F, invariantsIsLimit F⟩

/-- CommAlgCat.FiniteEtale K has all limits of shape (SingleObj G)^op: the limit of a
G-action is its invariant subalgebra. -/
instance hasLimitsOfShapeOpSingleObj :
    HasLimitsOfShape (SingleObj G)ᵒᵖ (CommAlgCat.FiniteEtale.{u} K) :=
  ⟨fun F => hasLimitInvariants F⟩

end Limit