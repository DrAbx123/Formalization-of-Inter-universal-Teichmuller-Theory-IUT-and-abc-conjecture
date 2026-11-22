import tmp.sheaf.xif.paper.S2903A6QEffectiveDescentActual
import tmp.sheaf.xif.paper.S2812IsStackActual
noncomputable section
open CategoryTheory Opposite
open CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2812IsStackActual
open LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual
open LeanFormal.IUT.XiFPaper.S2903A6QEffectiveDescentActual
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S2976bA6QDescentGluing
abbrev K : Type := S2844D6F6BaseChangeActual.K
local instance : Field K := S2847A6.fieldF
local instance : NumberField K := S2847A6.numberFieldF
local instance : DecidableEq K := Classical.decEq _
abbrev X : Iut.SchemeOverField K := S2844D6F6BaseChangeActual.S2844X
abbrev Q : Iut.EtaleStackPseudofunctor K := S2882A6Q
abbrev P : Iut.EtaleStackPseudofunctor K := Iut.schemeRepresentableEtalePseudofunctor K X
local instance smulPoint (Y : Iut.SchemeOverField K) :
    SMul SignGroup (Y ⟶ X) :=
  S2882A6PointSMul (LocallyDiscrete.mk (op Y))
local instance mulActionPoint (Y : Iut.SchemeOverField K) :
    MulAction SignGroup (Y ⟶ X) :=
  S2882A6PointMulAction (LocallyDiscrete.mk (op Y))

lemma map_obj_back {Y Z : Iut.SchemeOverField K} (f : Y ⟶ Z)
    (p : Q.obj (LocallyDiscrete.mk (op Z))) :
    ((Q.map f.op.toLoc).toFunctor.obj p).back = f ≫ p.back := by
  rfl

lemma map_obj_snd {Y Z : Iut.SchemeOverField K} (f : Y ⟶ Z)
    (p : Q.obj (LocallyDiscrete.mk (op Z))) :
    ((Q.map f.op.toLoc).toFunctor.obj p).snd = f ≫ p.snd := by
  rfl

lemma map_map_val {Y Z : Iut.SchemeOverField K} (f : Y ⟶ Z)
    {p q : Q.obj (LocallyDiscrete.mk (op Z))} (φ : p ⟶ q) :
    ((Q.map f.op.toLoc).toFunctor.map φ).val = φ.val := by
  rfl

lemma map₂_val {a b : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    {f g : a ⟶ b} (ψ : f ⟶ g) (M : Q.obj a) :
    ((Q.map₂ ψ).toNatTrans.app M).val = (1 : SignGroup) := by
  have h : f = g := LocallyDiscrete.eq_of_hom ψ
  subst h
  have hψ : ψ = 𝟙 f := Subsingleton.elim _ _
  subst hψ
  rw [PrelaxFunctor.map₂_id]
  exact ActionCategory.id_val _

lemma map₂Iso_hom_val {a b : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    {f g : a ⟶ b} (e : f ≅ g) (M : Q.obj a) :
    ((Q.map₂Iso e).hom.toNatTrans.app M).val = (1 : SignGroup) := by
  change ((Q.map₂ e.hom).toNatTrans.app M).val = (1 : SignGroup)
  exact map₂_val e.hom M

lemma map₂Iso_inv_val {a b : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ}
    {f g : a ⟶ b} (e : f ≅ g) (M : Q.obj a) :
    ((Q.map₂Iso e).inv.toNatTrans.app M).val = (1 : SignGroup) := by
  change ((Q.map₂ e.inv).toNatTrans.app M).val = (1 : SignGroup)
  exact map₂_val e.inv M

lemma mapComp_hom_val {a b c : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (M : Q.obj a) :
    ((Q.mapComp f g).hom.toNatTrans.app M).val = (1 : SignGroup) := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  rw [show Q.mapComp _ _ = (S2882A6PFunctor.toPseudofunctor').mapComp _ _ from rfl]
  rw [Functor.toPseudofunctor'_mapComp]
  rw [show (eqToIso _).hom = eqToHom _ from rfl]
  rw [CategoryTheory.Cat.eqToHom_app]
  · exact S1971ActionCategory_eqToHom_val _
  · rfl

lemma mapComp_inv_val {a b c : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (M : Q.obj a) :
    ((Q.mapComp f g).inv.toNatTrans.app M).val = (1 : SignGroup) := by
  obtain ⟨f⟩ := f
  obtain ⟨g⟩ := g
  rw [show Q.mapComp _ _ = (S2882A6PFunctor.toPseudofunctor').mapComp _ _ from rfl]
  rw [Functor.toPseudofunctor'_mapComp]
  rw [show (eqToIso _).inv = eqToHom _ from rfl]
  rw [CategoryTheory.Cat.eqToHom_app]
  · exact S1971ActionCategory_eqToHom_val _
  · rfl

lemma mapComp'_hom_val {a b c : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (fg : a ⟶ c) (h : f ≫ g = fg) (M : Q.obj a) :
    ((Q.mapComp' f g fg h).hom.toNatTrans.app M).val = (1 : SignGroup) := by
  have h1 : ((Q.mapComp f g).hom.toNatTrans.app M).val = (1 : SignGroup) :=
    mapComp_hom_val f g M
  rw [Pseudofunctor.mapComp']
  rw [Iso.trans_hom]
  rw [CategoryTheory.Cat.Hom₂.comp_app]
  rw [ActionCategory.comp_val]
  rw [h1]
  simp [map₂_val]
  exact one_mul (1 : SignGroup)

lemma mapComp'_inv_val {a b c : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
    (fg : a ⟶ c) (h : f ≫ g = fg) (M : Q.obj a) :
    ((Q.mapComp' f g fg h).inv.toNatTrans.app M).val = (1 : SignGroup) := by
  have h1 : ((Q.mapComp f g).inv.toNatTrans.app M).val = (1 : SignGroup) :=
    mapComp_inv_val f g M
  rw [Pseudofunctor.mapComp']
  rw [Iso.trans_inv]
  rw [CategoryTheory.Cat.Hom₂.comp_app]
  rw [ActionCategory.comp_val]
  rw [h1]
  simp [map₂_val]
  exact one_mul (1 : SignGroup)

lemma pullHom_val {Y Y' X1 X2 : Iut.SchemeOverField K}
    {f1 : Y ⟶ X1} {f2 : Y ⟶ X2}
    {M1 : Q.obj (LocallyDiscrete.mk (op X1))}
    {M2 : Q.obj (LocallyDiscrete.mk (op X2))}
    (φ : (Q.map f1.op.toLoc).toFunctor.obj M1 ⟶ (Q.map f2.op.toLoc).toFunctor.obj M2)
    (g : Y' ⟶ Y) (gf1 : Y' ⟶ X1) (gf2 : Y' ⟶ X2)
    (hgf1 : g ≫ f1 = gf1) (hgf2 : g ≫ f2 = gf2) :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf1 gf2 hgf1 hgf2).val = φ.val := by
  rw [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  rw [ActionCategory.comp_val]
  rw [ActionCategory.comp_val]
  rw [mapComp'_inv_val]
  rw [map_map_val]
  rw [mapComp'_hom_val]
  change (1 : SignGroup) * φ.val * 1 = φ.val
  rw [one_mul, mul_one]

section Descent
variable {U : Iut.SchemeOverField K} {R : Sieve U}
variable (D : Q.DescentData (fun f : R.arrows.category => f.obj.hom))
variable (hR : R ∈ Iut.SchemeOverField.etaleTopology K U)

/-- The underlying point of the action-groupoid object over the index i. -/
noncomputable def pt (i : R.arrows.category) : i.obj.left ⟶ X :=
  (D.obj i).snd

/-- The common refinement of two indices: the fibre product of their maps to U. -/
noncomputable abbrev W (i1 i2 : R.arrows.category) : Iut.SchemeOverField K :=
  pullback i1.obj.hom i2.obj.hom

/-- The index object carried by the common refinement of two indices. -/
noncomputable def Wcat (i1 i2 : R.arrows.category) : R.arrows.category :=
  ⟨Over.mk (pullback.fst i1.obj.hom i2.obj.hom ≫ i1.obj.hom),
    R.downward_closed i1.property (pullback.fst i1.obj.hom i2.obj.hom)⟩

@[simp] lemma Wcat_obj_left (i1 i2 : R.arrows.category) :
    (Wcat i1 i2).obj.left = W i1 i2 := rfl

@[simp] lemma Wcat_obj_hom (i1 i2 : R.arrows.category) :
    (Wcat i1 i2).obj.hom = pullback.fst i1.obj.hom i2.obj.hom ≫ i1.obj.hom := rfl

/-- The sign attached to an ordered pair of indices, computed at the canonical pair
of projections from the fibre product. -/
noncomputable def sig (i1 i2 : R.arrows.category) : SignGroup :=
  (D.hom (Y := W i1 i2) (q := pullback.fst i1.obj.hom i2.obj.hom ≫ i1.obj.hom)
    (i₁ := i1) (i₂ := i2) (pullback.fst i1.obj.hom i2.obj.hom)
    (pullback.snd i1.obj.hom i2.obj.hom)
    rfl (pullback.condition (f := i1.obj.hom) (g := i2.obj.hom)).symm).val

/-- The sign attached to a pair is independent of the chosen pair of maps. -/
lemma hom_val_eq_sig {Y : Iut.SchemeOverField K} {q : Y ⟶ U}
    {i1 i2 : R.arrows.category} (f1 : Y ⟶ i1.obj.left) (f2 : Y ⟶ i2.obj.left)
    (hf1 : f1 ≫ i1.obj.hom = q) (hf2 : f2 ≫ i2.obj.hom = q) :
    (D.hom q f1 f2 hf1 hf2).val = sig D i1 i2 := by
  let c : Y ⟶ W i1 i2 := pullback.lift f1 f2 (by rw [hf1, hf2])
  have h1 : c ≫ pullback.fst i1.obj.hom i2.obj.hom = f1 := pullback.lift_fst _ _ _
  have h2 : c ≫ pullback.snd i1.obj.hom i2.obj.hom = f2 := pullback.lift_snd _ _ _
  have hq : c ≫ (pullback.fst i1.obj.hom i2.obj.hom ≫ i1.obj.hom) = q := by
    rw [← Category.assoc, h1, hf1]
  have hph := D.pullHom_hom (Y' := Y) (g := c)
    (q := pullback.fst i1.obj.hom i2.obj.hom ≫ i1.obj.hom) (q' := q) hq
    (i₁ := i1) (i₂ := i2)
    (f₁ := pullback.fst i1.obj.hom i2.obj.hom)
    (f₂ := pullback.snd i1.obj.hom i2.obj.hom)
    (hf₁ := rfl) (hf₂ := (pullback.condition (f := i1.obj.hom) (g := i2.obj.hom)).symm)
    (gf₁ := f1) (gf₂ := f2) (hgf₁ := h1) (hgf₂ := h2)
  have hv := pullHom_val (Y := W i1 i2) (Y' := Y) (X1 := i1.obj.left) (X2 := i2.obj.left)
    (f1 := pullback.fst i1.obj.hom i2.obj.hom)
    (f2 := pullback.snd i1.obj.hom i2.obj.hom)
    (M1 := D.obj i1) (M2 := D.obj i2)
    (φ := D.hom (Y := W i1 i2) (q := pullback.fst i1.obj.hom i2.obj.hom ≫ i1.obj.hom)
      (i₁ := i1) (i₂ := i2) (pullback.fst i1.obj.hom i2.obj.hom)
      (pullback.snd i1.obj.hom i2.obj.hom)
      rfl (pullback.condition (f := i1.obj.hom) (g := i2.obj.hom)).symm)
    c f1 f2 h1 h2
  rw [← hph]
  rw [hv]
  rfl

/-- The sign of the diagonal pair is trivial. -/
lemma sig_self (i : R.arrows.category) : sig D i i = (1 : SignGroup) := by
  have h := hom_val_eq_sig D (Y := i.obj.left) (q := i.obj.hom) (i1 := i) (i2 := i)
    (𝟙 i.obj.left) (𝟙 i.obj.left) (by simp) (by simp)
  rw [← h]
  rw [D.hom_self]
  · exact ActionCategory.id_val _
  · simp

/-- The signs attached to index pairs form a (multiplicative) cocycle. -/
lemma sig_cocycle (i1 i2 i3 : R.arrows.category) :
    sig D i1 i3 = sig D i2 i3 * sig D i1 i2 := by
  let i12 : R.arrows.category := Wcat i1 i2
  let π12 : W i12 i3 ⟶ W i1 i2 := pullback.fst i12.obj.hom i3.obj.hom
  let π3 : W i12 i3 ⟶ i3.obj.left := pullback.snd i12.obj.hom i3.obj.hom
  let g1 : W i12 i3 ⟶ i1.obj.left := π12 ≫ pullback.fst i1.obj.hom i2.obj.hom
  let g2 : W i12 i3 ⟶ i2.obj.left := π12 ≫ pullback.snd i1.obj.hom i2.obj.hom
  let g3 : W i12 i3 ⟶ i3.obj.left := π3
  let q : W i12 i3 ⟶ U := pullback.fst i12.obj.hom i3.obj.hom ≫ i12.obj.hom
  have hg1 : g1 ≫ i1.obj.hom = q := by
    simp only [g1, q, π12, i12, Wcat_obj_hom, Category.assoc]
  have hg2 : g2 ≫ i2.obj.hom = q := by
    simp only [g2, q, π12, i12, Wcat_obj_hom, Category.assoc,
      pullback.condition (f := i1.obj.hom) (g := i2.obj.hom)]
  have hg3 : g3 ≫ i3.obj.hom = q := by
    simp only [g3, q, π3]
    exact (pullback.condition (f := i12.obj.hom) (g := i3.obj.hom)).symm
  have hcomp := D.hom_comp (Y := W i12 i3) (q := q) (i₁ := i1) (i₂ := i2) (i₃ := i3)
    g1 g2 g3 hg1 hg2 hg3
  have hv := congrArg Subtype.val hcomp
  rw [ActionCategory.comp_val] at hv
  rw [hom_val_eq_sig D g1 g2 hg1 hg2,
    hom_val_eq_sig D g2 g3 hg2 hg3,
    hom_val_eq_sig D g1 g3 hg1 hg3] at hv
  exact hv.symm

/-- Every element of the sign group is an involution. -/
lemma sign_sq (g : SignGroup) : g * g = (1 : SignGroup) := by
  rcases signGroup_cases g with h | h <;> subst h <;> decide

/-- The sign action is postcomposition with the automorphism. -/
lemma smul_eq_comp {Y : Iut.SchemeOverField K} (g : SignGroup) (p : Y ⟶ X) :
    g • p = p ≫ S2882A6Aut g := rfl

/-- The sign action commutes with precomposition. -/
lemma smul_comp {Y Z : Iut.SchemeOverField K} (g : SignGroup) (f : Y ⟶ Z) (p : Z ⟶ X) :
    g • (f ≫ p) = f ≫ (g • p) := by
  rw [smul_eq_comp, smul_eq_comp, Category.assoc]

/-- The twisted point at an index, relative to a chosen base index. -/
noncomputable def spoint (i0 i : R.arrows.category) : i.obj.left ⟶ X :=
  sig D i i0 • pt D i

/-- The twisted points of a descent datum are compatible on overlaps. -/
lemma spoint_compat (i0 : R.arrows.category) {Y : Iut.SchemeOverField K} {q : Y ⟶ U}
    {i1 i2 : R.arrows.category} (f1 : Y ⟶ i1.obj.left) (f2 : Y ⟶ i2.obj.left)
    (hf1 : f1 ≫ i1.obj.hom = q) (hf2 : f2 ≫ i2.obj.hom = q) :
    f1 ≫ spoint D i0 i1 = f2 ≫ spoint D i0 i2 := by
  have hD := (D.hom q f1 f2 hf1 hf2).property
  have hv : (D.hom q f1 f2 hf1 hf2).val = sig D i1 i2 :=
    hom_val_eq_sig D f1 f2 hf1 hf2
  have hD' : sig D i1 i2 • (f1 ≫ pt D i1) = f2 ≫ pt D i2 := by
    have h := hD
    simp only [map_obj_snd, hv] at h
    exact h
  have hc := sig_cocycle D i1 i2 i0
  have hstep : sig D i1 i0 • (f1 ≫ pt D i1) = sig D i2 i0 • (f2 ≫ pt D i2) := by
    rw [hc]
    rw [mul_smul, hD']
  simp only [spoint]
  rw [← smul_comp, ← smul_comp]
  exact hstep

/-! ## Gluing the twisted family via the representable stack -/

/-- The compatible family of twisted points on the sieve. -/
noncomputable def famTwist (i0 : R.arrows.category) :
    Presieve.FamilyOfElements (yoneda.obj X) R.arrows :=
  fun {Y} f hf => spoint D i0 ⟨Over.mk f, hf⟩

/-- The twisted family is compatible. -/
lemma famTwist_compatible (i0 : R.arrows.category) :
    (famTwist D i0).Compatible := by
  intro Y1 Y2 Z g1 g2 f1 f2 h1 h2 comm
  change g1 ≫ spoint D i0 ⟨Over.mk f1, h1⟩ = g2 ≫ spoint D i0 ⟨Over.mk f2, h2⟩
  exact spoint_compat D i0 (q := g1 ≫ f1) (i1 := ⟨Over.mk f1, h1⟩) (i2 := ⟨Over.mk f2, h2⟩) g1 g2 rfl comm.symm

/-- The global point obtained by gluing the twisted family. -/
noncomputable def gluedM (i0 : R.arrows.category) : U ⟶ X :=
  (yoneda_isSheafFor K X U R hR (famTwist D i0) (famTwist_compatible D i0)).choose

/-- The face condition of the glued point. -/
lemma gluedM_fac (i0 : R.arrows.category) {Y : Iut.SchemeOverField K} (f : Y ⟶ U)
    (hf : R.arrows f) :
    f ≫ gluedM D hR i0 = spoint D i0 ⟨Over.mk f, hf⟩ :=
  (yoneda_isSheafFor K X U R hR (famTwist D i0) (famTwist_compatible D i0)).choose_spec.1 f hf

/-- The action-groupoid object attached to the glued point. -/
noncomputable def M (i0 : R.arrows.category) : Q.obj (LocallyDiscrete.mk (op U)) :=
  (gluedM D hR i0 : ActionCategory SignGroup (Opposite.unop (LocallyDiscrete.mk (op U)).as ⟶ X))

/-- The underlying point of the glued action-groupoid object. -/
lemma M_back (i0 : R.arrows.category) : (M D hR i0).back = gluedM D hR i0 := rfl

/-- The underlying point of the descent data of the glued object at an index. -/
lemma toDescentData_obj_back (i0 : R.arrows.category) (i : R.arrows.category) :
    (((Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).obj (M D hR i0)).obj i).back =
      i.obj.hom ≫ gluedM D hR i0 := by
  change ((Q.map (i.obj.hom).op.toLoc).toFunctor.obj (M D hR i0)).back = _
  rw [map_obj_back]
  rfl

/-- The value of the structural morphism of a toDescentData object is trivial. -/
lemma toDescentData_hom_val (i0 : R.arrows.category) {Y : Iut.SchemeOverField K} {q : Y ⟶ U}
    {i1 i2 : R.arrows.category} (f1 : Y ⟶ i1.obj.left) (f2 : Y ⟶ i2.obj.left)
    (hf1 : f1 ≫ i1.obj.hom = q) (hf2 : f2 ≫ i2.obj.hom = q) :
    (((Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).obj (M D hR i0)).hom
      q f1 f2 hf1 hf2).val = (1 : SignGroup) := by
  change ((Pseudofunctor.DescentData.ofObj (M D hR i0)).hom q f1 f2 hf1 hf2).val = (1 : SignGroup)
  rw [Pseudofunctor.DescentData.ofObj_hom]
  rw [ActionCategory.comp_val]
  rw [mapComp'_hom_val, mapComp'_inv_val]
  exact one_mul (1 : SignGroup)

/-- Twisting the twisted point returns the original point. -/
lemma twist_spoint (i0 i : R.arrows.category) :
    sig D i i0 • spoint D i0 i = pt D i := by
  simp only [spoint]
  rw [← mul_smul, sign_sq, one_smul]

lemma index_mk_self (i : R.arrows.category) :
    (⟨Over.mk i.obj.hom, i.property⟩ : R.arrows.category) = i := by
  cases i
  rfl

/-- **Gluing of the twisted underlying family.**

For a descent datum D of the action groupoid Q and a chosen base index i0, the
underlying points, twisted by the coboundary signs sig i i0, glue to a global
point m : U ⟶ X. -/
theorem S2976b_descent_gluing (i0 : R.arrows.category)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology K U) :
    ∃ m : U ⟶ X, ∀ {Y : Iut.SchemeOverField K} (f : Y ⟶ U) (hf : R.arrows f),
      f ≫ m = sig D ⟨Over.mk f, hf⟩ i0 • pt D ⟨Over.mk f, hf⟩ := by
  refine ⟨gluedM D hR i0, fun f hf => ?_⟩
  simpa only [spoint] using gluedM_fac D hR i0 f hf

/-- **The signs are a coboundary**: the pair signs are the quotients of the
base-index signs. -/
theorem S2976b_sign_coboundary (i0 i1 i2 : R.arrows.category) :
    sig D i1 i2 = sig D i1 i0 * sig D i2 i0 := by
  have hc := sig_cocycle D i1 i2 i0
  have h2 : sig D i2 i0 * sig D i1 i0 = sig D i1 i2 := by
    rw [hc, ← mul_assoc, sign_sq, one_mul]
  rw [← h2, mul_comm]

noncomputable def compIso (i0 i : R.arrows.category) :
    ((Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).obj (M D hR i0)).obj i ≅ D.obj i := by
  have hsp : (((Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).obj (M D hR i0)).obj i).back =
      spoint D i0 i := by
    rw [toDescentData_obj_back D hR i0 i]
    exact gluedM_fac D hR i0 i.obj.hom i.property
  have hsp' : (((Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).obj (M D hR i0)).obj i).snd =
      spoint D i0 i := hsp
  have hinv : sig D i i0 • pt D i = spoint D i0 i := by
    have h := congrArg (fun p => sig D i i0 • p) (twist_spoint D i0 i)
    rw [← mul_smul, sign_sq, one_smul] at h
    exact h.symm
  refine
    { hom := ⟨sig D i i0, ?_⟩
      inv := ⟨sig D i i0, ?_⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · change (fun x : i.obj.left ⟶ X => sig D i i0 • x)
        (((Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).obj (M D hR i0)).obj i).snd =
      (D.obj i).snd
    rw [hsp']
    exact twist_spoint D i0 i
  · change (fun x : i.obj.left ⟶ X => sig D i i0 • x) (D.obj i).snd =
        (((Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).obj (M D hR i0)).obj i).snd
    rw [hsp']
    exact hinv
  · apply Subtype.ext
    rw [ActionCategory.comp_val, ActionCategory.id_val]
    exact sign_sq _
  · apply Subtype.ext
    rw [ActionCategory.comp_val, ActionCategory.id_val]
    exact sign_sq _

/-- The comparison isomorphism between the descent data of the glued object and D. -/
noncomputable def descentIso (i0 : R.arrows.category) :
    (Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).obj (M D hR i0) ≅ D :=
  Pseudofunctor.DescentData.isoMk (fun i => compIso D hR i0 i) (by
    intro Y q i1 i2 f1 f2 hf1 hf2
    apply Subtype.ext
    rw [ActionCategory.comp_val, ActionCategory.comp_val]
    rw [hom_val_eq_sig D f1 f2 hf1 hf2,
      toDescentData_hom_val D hR i0 f1 f2 hf1 hf2]
    change sig D i1 i2 * sig D i1 i0 = sig D i2 i0 * 1
    rw [mul_one]
    have hc := sig_cocycle D i1 i2 i0
    rw [hc]
    calc sig D i1 i2 * (sig D i2 i0 * sig D i1 i2)
        = (sig D i1 i2 * sig D i1 i2) * sig D i2 i0 := by
          rw [mul_comm (sig D i2 i0) (sig D i1 i2), mul_assoc]
      _ = 1 * sig D i2 i0 := by rw [sign_sq]
      _ = sig D i2 i0 := by rw [one_mul])

#print axioms S2976b_descent_gluing
#print axioms descentIso
#print axioms S2976b_sign_coboundary
#print axioms sig_cocycle
#print axioms spoint_compat

end Descent

/-- Effective descent for the action groupoid Q along a covering sieve with a chosen index. -/
theorem S2976b_essSurj_nonempty {U : Iut.SchemeOverField K} {R : Sieve U}
    (i0 : R.arrows.category) (hR : R ∈ Iut.SchemeOverField.etaleTopology K U) :
    (Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj :=
  ⟨fun D => ⟨M D hR i0, ⟨descentIso D hR i0⟩⟩⟩

/-- Reduction of the effective-descent target: it suffices that every covering sieve
of the etale topology has a nonempty index category. -/
theorem S2976b_QEffectiveDescent_of_nonempty
    (hne : ∀ {U : Iut.SchemeOverField K} (R : Sieve U),
      R ∈ Iut.SchemeOverField.etaleTopology K U → Nonempty R.arrows.category) :
    S2893A6QEffectiveDescent := by
  change ∀ (U : Iut.SchemeOverField K) (R : Sieve U),
    R ∈ Iut.SchemeOverField.etaleTopology K U →
      (Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj
  intro U R hR
  obtain ⟨i0⟩ := hne R hR
  exact S2976b_essSurj_nonempty i0 hR

#check S2976b_essSurj_nonempty
#check S2976b_QEffectiveDescent_of_nonempty
#print axioms S2976b_essSurj_nonempty
#print axioms S2976b_QEffectiveDescent_of_nonempty
#print axioms S2976b_essSurj_nonempty
#print axioms S2976b_QEffectiveDescent_of_nonempty

end LeanFormal.IUT.XiFPaper.S2976bA6QDescentGluing
end