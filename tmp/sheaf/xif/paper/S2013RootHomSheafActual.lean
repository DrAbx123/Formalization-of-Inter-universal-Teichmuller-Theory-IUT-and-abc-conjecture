import tmp.sheaf.xif.paper.S2008RootPrestackActual
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.Algebra.Group.Units.Hom

/-!
# S2013: the root hom presheaf of the l-tors root prestack is a sheaf

This file proves `S2008RootHomSheaf`, the single missing statement of S2008,
hence `(S1997RootPrestack K l).IsPrestack (etaleTopology K)`, and combines it
with `S2008isStack_iff`.

## Route

* (M1) `T |-> Gamma(T.left.left, O)` is a sheaf for the etale topology.  The
  global sections functor is representable by the affine line
  `A1 = Spec Z[t]` (`S2013sectionsIso`, via
  `AlgebraicGeometry.AffineSpace.toSpecMvPolyIntEquiv`), and the etale topology
  is subcanonical, so its yoneda image is a sheaf.
* (M2) the units presheaf is local (a section which is locally a unit is a unit).
* (M3) root morphisms are determined by their unit component
  (`S1997RootHom.ext`), and the unit component of the restriction map is
  `Units.map (appTop ...)` (`S2008pullHom_zeta`), so the sheaf condition for
  the root hom presheaf is reduced to (M1) and (M2).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2013RootHomSheafActual

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped SpecOfNotation
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S2008RootPrestackActual

variable {K : Type u} [Field K] {l : Nat}

/-! ## 1. Global sections are representable by the affine line -/

/-- The free commutative ring on one generator, at universe `u`. -/
noncomputable abbrev S2013A1Ring : CommRingCat.{u} :=
  CommRingCat.of (MvPolynomial (PUnit.{u + 1}) (ULift.{u} ℤ))

/-- The affine line `A1 = Spec Z[t]` over `Spec Z`. -/
noncomputable abbrev S2013A1 : Scheme.{u} :=
  Scheme.Spec.obj (op S2013A1Ring)

/-- The (type valued) presheaf of global sections of the structure sheaf. -/
noncomputable def S2013sections : Scheme.{u}ᵒᵖ ⥤ Type u :=
  Scheme.Γ ⋙ forget CommRingCat

/-- `(PUnit -> a) ≃ a`, with definitional computation rules. -/
def S2013unitFunEquiv (a : Type u) : (PUnit.{u + 1} → a) ≃ a where
  toFun f := f PUnit.unit
  invFun x := fun _ => x
  left_inv f := by funext i; cases i; rfl
  right_inv x := rfl

@[simp]
lemma S2013unitFunEquiv_apply (a : Type u) (f : PUnit.{u + 1} → a) :
    S2013unitFunEquiv a f = f PUnit.unit := rfl

@[simp]
lemma S2013unitFunEquiv_symm_apply (a : Type u) (x : a) (i : PUnit.{u + 1}) :
    (S2013unitFunEquiv a).symm x i = x := rfl

/-- Global sections of a scheme are morphisms into the affine line. -/
noncomputable def S2013sectionsEquiv {X : Scheme.{u}} : Γ(X, ⊤) ≃ (X ⟶ S2013A1) :=
  (S2013unitFunEquiv Γ(X, ⊤)).symm.trans
    (AffineSpace.toSpecMvPolyIntEquiv (PUnit.{u + 1}) (X := X)).symm

lemma S2013sectionsEquiv_apply_eq {X : Scheme.{u}} (s : Γ(X, ⊤)) :
    S2013sectionsEquiv s =
      (AffineSpace.toSpecMvPolyIntEquiv (PUnit.{u + 1}) (X := X)).symm (fun _ => s) := rfl

theorem S2013sectionsEquiv_natural {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤)) :
    S2013sectionsEquiv (f.appTop s) = f ≫ S2013sectionsEquiv s := by
  rw [S2013sectionsEquiv_apply_eq, S2013sectionsEquiv_apply_eq]
  apply (AffineSpace.toSpecMvPolyIntEquiv (PUnit.{u + 1}) (X := X)).injective
  rw [Equiv.apply_symm_apply]
  funext i
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp, Equiv.apply_symm_apply]

/-- The sections presheaf is represented by the affine line. -/
noncomputable def S2013sectionsIso : S2013sections ≅ yoneda.obj S2013A1 :=
  NatIso.ofComponents (fun X => (S2013sectionsEquiv (X := X.unop)).toIso) (fun {X Y} f => by
    ext s
    exact S2013sectionsEquiv_natural f.unop s)

instance : AlgebraicGeometry.Scheme.etaleTopology.Subcanonical :=
  GrothendieckTopology.Subcanonical.of_le
    AlgebraicGeometry.Scheme.etaleTopology_le_proetaleTopology

/-- (M1) The sections presheaf is an etale sheaf on schemes. -/
theorem S2013sections_isSheaf :
    Presheaf.IsSheaf AlgebraicGeometry.Scheme.etaleTopology S2013sections := by
  rw [Presheaf.isSheaf_of_iso_iff S2013sectionsIso]
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-! ## 2. The sections sheaf on the over-site -/

section OverSite

variable (S : Iut.SchemeOverField K)

/-- The type of sections of the structure sheaf over a test object. -/
noncomputable abbrev S2013Sec (T : (Over S)ᵒᵖ) : Type u :=
  ↥(Scheme.Γ.obj (op T.unop.left.left))

/-- The presheaf of sections of the structure sheaf on `(Over S)ᵒᵖ`. -/
@[reducible] noncomputable def S2013Γ : (Over S)ᵒᵖ ⥤ Type u where
  obj T := S2013Sec S T
  map {T T'} f := ↾fun a => Scheme.Hom.appTop f.unop.left.left a
  map_id T := by ext a; simp
  map_comp {T T' T''} f g := by ext a; simp [Scheme.Hom.comp_appTop]

/-- The same presheaf as a composite of forgetful functors, used to transport
sheafness from the etale site of schemes. -/
noncomputable def S2013Γcomp : (Over S)ᵒᵖ ⥤ Type u :=
  ((Over.forget S).op ⋙ (Over.forget (Spec(K))).op ⋙ Scheme.Γ) ⋙ forget CommRingCat

lemma S2013Γ_eq_comp : S2013Γ S = S2013Γcomp S := rfl

lemma S2013Γ_map_apply {X Y : (Over S)ᵒᵖ} (f : X ⟶ Y) (a : S2013Sec S X) :
    (S2013Γ S).map f a = Scheme.Hom.appTop f.unop.left.left a := rfl

theorem S2013Γcomp_isSheaf :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology K).over S) (S2013Γcomp S) := by
  have h2 : Presheaf.IsSheaf (Iut.SchemeOverField.etaleTopology K)
      ((Over.forget (Spec(K))).op ⋙ S2013sections) :=
    Functor.op_comp_isSheaf_of_isSheaf (Over.forget (Spec(K)))
      (Iut.SchemeOverField.etaleTopology K) AlgebraicGeometry.Scheme.etaleTopology
      S2013sections S2013sections_isSheaf
  exact Functor.op_comp_isSheaf_of_isSheaf (Over.forget S)
    ((Iut.SchemeOverField.etaleTopology K).over S) (Iut.SchemeOverField.etaleTopology K)
    ((Over.forget (Spec(K))).op ⋙ S2013sections) h2

/-- (M1) The sections of the structure sheaf form a sheaf on the etale over-site. -/
theorem S2013Γ_isSheaf :
    Presieve.IsSheaf ((Iut.SchemeOverField.etaleTopology K).over S) (S2013Γ S) := by
  rw [S2013Γ_eq_comp]
  exact (isSheaf_iff_isSheaf_of_type ((Iut.SchemeOverField.etaleTopology K).over S)
    (S2013Γcomp S)).mp (S2013Γcomp_isSheaf S)

/-- Local characterisation of equality of sections. -/
theorem S2013Γ_ext {X : (Over S)ᵒᵖ} {R : Sieve X.unop}
    (hR : R ∈ (Iut.SchemeOverField.etaleTopology K).over S X.unop)
    {a b : S2013Sec S X}
    (h : ∀ ⦃Y : Over S⦄ (f : Y ⟶ X.unop) (hf : R f),
      Scheme.Hom.appTop f.left.left a = Scheme.Hom.appTop f.left.left b) : a = b := by
  have hsep := Presieve.IsSheaf.isSeparated
    (J := (Iut.SchemeOverField.etaleTopology K).over S) (S2013Γ_isSheaf S) R hR
  refine Presieve.IsSeparatedFor.ext hsep ?_
  intro Y f hf
  exact h f hf

/-! ## 3. The units presheaf -/

/-- The presheaf of units of the structure sheaf on the over-site. -/
@[reducible] noncomputable def S2013units : (Over S)ᵒᵖ ⥤ Type u where
  obj T := (S2013Sec S T)ˣ
  map {T T'} f := ↾fun u => Units.map (Scheme.Hom.appTop f.unop.left.left).hom.toMonoidHom u
  map_id T := by ext u; simp
  map_comp {T T' T''} f g := by ext u; simp [Scheme.Hom.comp_appTop]

lemma S2013units_map_apply {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (u : (S2013units S).obj T) :
    (S2013units S).map f u =
      Units.map (Scheme.Hom.appTop f.unop.left.left).hom.toMonoidHom u := rfl

lemma S2013Γ_map_one {X Y : (Over S)ᵒᵖ} (f : X ⟶ Y) :
    (S2013Γ S).map f (1 : S2013Sec S X) = 1 := by
  rw [S2013Γ_map_apply]
  exact map_one _

lemma S2013Γ_map_mul {X Y : (Over S)ᵒᵖ} (f : X ⟶ Y) (a b : S2013Sec S X) :
    (S2013Γ S).map f (a * b) = (S2013Γ S).map f a * (S2013Γ S).map f b := by
  rw [S2013Γ_map_apply, S2013Γ_map_apply, S2013Γ_map_apply]
  exact map_mul _ a b

/-- A ring homomorphism sends the inverse of a unit to the inverse of its image. -/
lemma S2013_appTop_units_inv {A B : Type u} [CommRing A] [CommRing B] (phi : A →+* B)
    (u : Aˣ) : phi (↑u⁻¹) = ↑((Units.map phi.toMonoidHom u)⁻¹) :=
  (Units.coe_map_inv phi.toMonoidHom u).symm

lemma S2013Γ_map_units_inv {X Y : (Over S)ᵒᵖ} (f : X ⟶ Y) (u : (S2013units S).obj X) :
    (S2013Γ S).map f (↑(u⁻¹)) = ↑(((S2013units S).map f u)⁻¹) := by
  rw [S2013Γ_map_apply, S2013units_map_apply, S2013_appTop_units_inv]

/-- (M2) The presheaf of units of the structure sheaf is a sheaf. -/
theorem S2013units_isSheaf :
    Presieve.IsSheaf ((Iut.SchemeOverField.etaleTopology K).over S) (S2013units S) := by
  have hΓ := S2013Γ_isSheaf S
  refine Presieve.IsSeparated.isSheaf ?_ ?_
  · intro X R hR x u₁ u₂ h₁ h₂
    apply Units.ext
    refine S2013Γ_ext (S := S) (R := R) hR ?_
    intro Y f hf
    have k₁ := congrArg Units.val (h₁ f hf)
    have k₂ := congrArg Units.val (h₂ f hf)
    rw [S2013units_map_apply] at k₁
    rw [S2013units_map_apply] at k₂
    simpa using k₁.trans k₂.symm
  · intro X R hR x hx
    let a : Presieve.FamilyOfElements (S2013Γ S) (R : Presieve X) := fun Y f hf => ↑(x f hf)
    have ha : a.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
      have hu := hx g₁ g₂ h₁ h₂ comm
      rw [S2013units_map_apply, S2013units_map_apply] at hu
      simpa [a] using congrArg Units.val hu
    obtain ⟨t, ht, -⟩ := hΓ R hR a ha
    let b : Presieve.FamilyOfElements (S2013Γ S) (R : Presieve X) :=
      fun Y f hf => ↑((x f hf)⁻¹)
    have hb : b.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
      have hu := hx g₁ g₂ h₁ h₂ comm
      rw [S2013Γ_map_units_inv, S2013Γ_map_units_inv, hu]
    obtain ⟨t', ht', -⟩ := hΓ R hR b hb
    have hmul : t * t' = (1 : S2013Sec S (op X)) := by
      refine S2013Γ_ext (S := S) (R := R) hR ?_
      intro Y f hf
      have h₁ : Scheme.Hom.appTop f.left.left t = (↑(x f hf) : S2013Sec S (op Y)) := ht f hf
      have h₂ : Scheme.Hom.appTop f.left.left t' = b f hf := ht' f hf
      rw [map_mul, map_one, h₁, h₂]
      exact Units.mul_inv _
    refine ⟨Units.mk t t' hmul (by rw [mul_comm]; exact hmul), ?_⟩
    intro Y f hf
    apply Units.ext
    rw [S2013units_map_apply]
    exact ht f hf

end OverSite

/-! ## 4. The `b`-components and the root hom sheaf -/

section RootHom

variable (S : Iut.SchemeOverField K)

/-- The `b`-component of the object `M` pulled back to a test object. -/
noncomputable def S2013x (M : (S2008PF K l).obj (LocallyDiscrete.mk (op S))) (T : Over S) :
    S2013Sec S (op T) :=
  (Scheme.Hom.appTop T.hom.left).hom M.b

/-- The `b`-component of the object `N` pulled back to a test object. -/
noncomputable def S2013y (N : (S2008PF K l).obj (LocallyDiscrete.mk (op S))) (T : Over S) :
    S2013Sec S (op T) :=
  (Scheme.Hom.appTop T.hom.left).hom N.b

lemma S2013x_natural {Y X : Over S} (f : Y ⟶ X)
    (M : (S2008PF K l).obj (LocallyDiscrete.mk (op S))) :
    S2013x S M Y = Scheme.Hom.appTop f.left.left (S2013x S M X) := by
  rw [S2013x, S2013x, ← Over.w f, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

lemma S2013y_natural {Y X : Over S} (f : Y ⟶ X)
    (N : (S2008PF K l).obj (LocallyDiscrete.mk (op S))) :
    S2013y S N Y = Scheme.Hom.appTop f.left.left (S2013y S N X) := by
  rw [S2013y, S2013y, ← Over.w f, Over.comp_left, Scheme.Hom.comp_appTop]
  rfl

/-- The value of the units presheaf on a morphism. -/
lemma S2013units_map_val {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') (u : (S2013units S).obj T) :
    Units.val ((S2013units S).map f u) =
      Scheme.Hom.appTop f.unop.left.left (Units.val u) := rfl

/-- The unit component of the restriction of a root morphism (`S2008pullHom_zeta`,
in the form needed below). -/
lemma S2013_zeta_restrict {M N : (S2008PF K l).obj (LocallyDiscrete.mk (op S))}
    {X : Over S} {R : Sieve X}
    {x : Presieve.FamilyOfElements ((S2008PF K l).presheafHom M N) (R : Presieve X)}
    {t : ((S2008PF K l).presheafHom M N).obj (op X)} (ht : x.IsAmalgamation t)
    {Y : Over S} (f : Y ⟶ X) (hf : R f) :
    Scheme.Hom.appTop f.left.left (Units.val t.zeta) = Units.val (x f hf).zeta := by
  have h := congrArg (fun r => r.zeta) (ht f hf)
  rw [S2008pullHom_zeta S M N f t] at h
  exact congrArg Units.val h

/-- The unit component of a glued family of root morphisms. -/
lemma S2013_zeta_glue {M N : (S2008PF K l).obj (LocallyDiscrete.mk (op S))}
    {X : Over S} {R : Sieve X}
    {x : Presieve.FamilyOfElements ((S2008PF K l).presheafHom M N) (R : Presieve X)}
    {zeta : (S2013Sec S (op X))ˣ}
    (hzeta : ∀ ⦃Y : Over S⦄ (f : Y ⟶ X) (hf : R f),
      (S2013units S).map f.op zeta = (x f hf).zeta)
    {Y : Over S} (f : Y ⟶ X) (hf : R f) :
    Scheme.Hom.appTop f.left.left (Units.val zeta) = Units.val (x f hf).zeta := by
  have h := congrArg Units.val (hzeta f hf)
  rw [S2013units_map_val] at h
  exact h

/-- (M3) The root hom presheaf is a sheaf for the etale topology. -/
theorem S2013presheafHom_isSheaf (M N : (S2008PF K l).obj (LocallyDiscrete.mk (op S))) :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology K).over S)
      ((S2008PF K l).presheafHom M N) := by
  have hΓ := S2013Γ_isSheaf S
  have hU := S2013units_isSheaf S
  rw [isSheaf_iff_isSheaf_of_type]
  refine Presieve.IsSeparated.isSheaf ?_ ?_
  · intro X R hR x t₁ t₂ h₁ h₂
    apply S1997RootHom.ext
    apply Units.ext
    refine S2013Γ_ext (S := S) (R := R) hR ?_
    intro Y f hf
    exact (S2013_zeta_restrict (S := S) h₁ f hf).trans
      (S2013_zeta_restrict (S := S) h₂ f hf).symm
  · intro X R hR x hx
    let u : Presieve.FamilyOfElements (S2013units S) (R : Presieve X) := fun Y f hf => (x f hf).zeta
    have hu : u.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
      have h := congrArg (fun r => r.zeta) (hx g₁ g₂ h₁ h₂ comm)
      rw [S2008pullHom_zeta S M N g₁, S2008pullHom_zeta S M N g₂] at h
      exact h
    obtain ⟨zeta, hzeta, -⟩ := hU R hR u hu
    have hpow : ((↑zeta : S2013Sec S (op X)) ^ l) = 1 := by
      refine S2013Γ_ext (S := S) (R := R) hR ?_
      intro Y f hf
      have h := S2013_zeta_glue (S := S) hzeta f hf
      rw [map_pow, map_one, h]
      exact (x f hf).zeta_pow
    have heq : S2013y S N X = (↑zeta : S2013Sec S (op X)) * S2013x S M X := by
      refine S2013Γ_ext (S := S) (R := R) hR ?_
      intro Y f hf
      have h := S2013_zeta_glue (S := S) hzeta f hf
      rw [← S2013y_natural (S := S) f N, map_mul, ← S2013x_natural (S := S) f M, h]
      exact (x f hf).eq
    refine ⟨⟨zeta, hpow, heq⟩, ?_⟩
    intro Y f hf
    apply S1997RootHom.ext
    apply Units.ext
    rw [S2008pullHom_zeta S M N f]
    exact congrArg Units.val (hzeta f hf)

end RootHom

/-! ## 5. The target statements -/

/-- The missing statement of S2008 is proved. -/
theorem S2013RootHomSheaf_holds {l : PrimeGeFive} :
    S2008RootHomSheaf (K := K) (l := l) := by
  intro S M N
  exact S2013presheafHom_isSheaf (K := K) (l := l.value) S M N

/-- Descent of morphisms for the l-tors root prestack. -/
theorem S2013RootPrestackIsPrestack {l : PrimeGeFive} :
    S2008RootPrestackIsPrestack (K := K) (l := l) :=
  (S2008isPrestack_iff (K := K) (l := l)).mpr S2013RootHomSheaf_holds

/-- The root prestack is a prestack for the etale topology. -/
theorem S2013RootPrestack_isPrestack {l : PrimeGeFive} :
    (S1997RootPrestack K l.value).IsPrestack (Iut.SchemeOverField.etaleTopology K) :=
  S2013RootPrestackIsPrestack

/-- Consequently `IsStack` for the root prestack is *equivalent* to effective
descent: the descent-of-morphisms half is now unconditional. -/
theorem S2013isStack_iff {l : PrimeGeFive} :
    (S1997RootPrestack K l.value).IsStack (Iut.SchemeOverField.etaleTopology K) ↔
      S1997RootEffectiveDescent K l.value :=
  S2008isStack_iff_effDescent (K := K) (l := l) S2013RootPrestackIsPrestack

/-! ## 6. Axiom footprint -/

#print axioms S2013sections_isSheaf
#print axioms S2013Γ_isSheaf
#print axioms S2013units_isSheaf
#print axioms S2013presheafHom_isSheaf
#print axioms S2013RootHomSheaf_holds
#print axioms S2013RootPrestack_isPrestack
#print axioms S2013isStack_iff

end LeanFormal.IUT.XiFPaper.S2013RootHomSheafActual
