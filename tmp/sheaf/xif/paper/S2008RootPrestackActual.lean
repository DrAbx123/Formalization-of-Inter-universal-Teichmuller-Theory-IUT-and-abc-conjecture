import tmp.sheaf.xif.paper.S2002RootStackificationActual

/-!
# S2008: descent of morphisms (IsPrestack) for the l-tors root prestack

S2002 split the IsStack gap for the l-tors root prestack exactly in two:

  IsStack <-> IsPrestack and S1997RootEffectiveDescent.

This file attacks the first half, IsPrestack, i.e. descent of morphisms for
S1997RootPrestack K l with respect to the etale topology.

## What is proved here

Mathlib's Pseudofunctor.IsPrestack asks that for every test S and objects
M N of the fiber over S, the presheaf F.presheafHom M N on Over S is a
sheaf.  The elements of this presheaf are *literally* the root morphisms
(zeta, equation) of S1997 -- this is a definitional fact, recorded in
S2008presheafHom_obj.  The only obstruction to computing with it is the
pseudofunctor coherence: presheafHom.map is Mathlib's pullHom, a composite
of the mapComp' coherence isomorphisms with the actual pullback of
morphisms.

We prove here that the coherence isomorphisms of a *strict* pseudofunctor
(Functor.toPseudofunctor') have trivial unit component zeta = 1
(S2008mapComp_zeta_hom, S2008mapComp'_zeta_hom, and the inv versions),
and deduce the pullback formula S2008pullHom_zeta:

  (pullback of x along g).zeta = appTop g (x.zeta).

This is the precise compatibility needed for the sheaf condition of the root
hom presheaf: the zeta-projection is natural, so descent of morphisms can be
tested on units of the structure sheaf and on the defining equation.

## The exact first missing

After S2008pullHom_zeta the pseudofunctor coherence no longer obstructs
descent of morphisms: IsPrestack for the root prestack is equivalent to the
concrete sheaf statement S2008RootHomSheaf, and the mathematical content of
that statement is separated into

* S2008SectionsIsSheaf: the presheaf T |-> Gamma(T, O) of sections of the
  structure sheaf is a sheaf for the etale topology on the over-site.  This is
  not in Mathlib; it is equivalent, via the adjunction Gamma -| Spec
  (AlgebraicGeometry.GammaSpecAdjunction), to the subcanonicity of the etale
  topology (Scheme.etaleTopology.Subcanonical, available via
  etale <= proetale <= fpqc, AlgebraicGeometry.Sites.Fpqc);
* the resulting sheaf of units T |-> Gamma(T, O)^x and the locality of the
  equation N.b = zeta * M.b.

No sorry, admit or new axiom is used; everything below is unconditional.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace LeanFormal.IUT.XiFPaper.S2008RootPrestackActual

universe u

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S2002RootStackificationActual

variable {K : Type u} [Field K] {l : Nat}

/-- The root prestack, written as the strict pseudofunctor attached to the
strict functor S1997RootFiberFunctor K l. -/
abbrev S2008PF (K : Type u) [Field K] (l : Nat) : Iut.EtaleStackPseudofunctor K :=
  (S1997RootFiberFunctor K l).toPseudofunctor'

/-- `S2008PF` is *definitionally* the root prestack of S1997.  It is introduced
only to keep elaboration from unfolding the root fiber functor in dependent
types; every statement below can be rewritten into `S1997RootPrestack`. -/
theorem S2008PF_defeq (K : Type u) [Field K] (l : Nat) :
    S2008PF K l = S1997RootPrestack K l := rfl

section Fiber

/-! ## 1. The unit component of root morphisms -/

lemma S2008zeta_eqToHom {R : Type u} [CommRing R] {l : Nat} {x y : S1997RootObj R l}
    (e : x = y) : (eqToHom e : S1997RootHom R l x y).zeta = 1 := by
  cases e
  rfl

lemma S2008zeta_id {R : Type u} [CommRing R] {l : Nat} (x : S1997RootObj R l) :
    (𝟙 x : S1997RootHom R l x x).zeta = 1 := rfl

lemma S2008zeta_comp {R : Type u} [CommRing R] {l : Nat} {x y z : S1997RootObj R l}
    (f : S1997RootHom R l x y) (g : S1997RootHom R l y z) :
    (S1997RootHom.comp f g).zeta = f.zeta * g.zeta := rfl

/-- The unit component of the map of the root fiber functor. -/
lemma S2008RootMap_zeta {R S : Type u} [CommRing R] [CommRing S] (phi : R →+* S)
    {l : Nat} {x y : S1997RootObj R l} (f : S1997RootHom R l x y) :
    ((S1997RootMap phi l).map f).zeta = Units.map phi.toMonoidHom f.zeta := rfl

/-- An isomorphism of the root fiber whose hom has trivial unit has trivial
inverse unit. -/
lemma S2008zeta_inv_of_hom {R : Type u} [CommRing R] {l : Nat} {x y : S1997RootObj R l}
    (i : x ≅ y) (h : i.hom.zeta = 1) : i.inv.zeta = 1 := by
  have h2 := congrArg (fun f : S1997RootHom R l x x => f.zeta) i.hom_inv_id
  rw [S2008zeta_id] at h2
  change i.hom.zeta * i.inv.zeta = 1 at h2
  rw [h, one_mul] at h2
  exact h2

end Fiber

/-! ## 2. Coherences of a strict pseudofunctor have trivial unit -/

/-- The hom component of eqToIso of an equality of Cat-morphisms is an
eqToHom on objects. -/
lemma S2008cat_eqToIso_hom_toNatTrans_app {C D : Type u} [Category C] [Category D]
    {F G : Cat.of C ⟶ Cat.of D} (h : F = G) (M : C) :
    (eqToIso h).hom.toNatTrans.app M =
      eqToHom (congrArg (fun K : Cat.of C ⟶ Cat.of D => K.toFunctor.obj M) h) := by
  cases h
  rfl

/-- The inv component of eqToIso of an equality of Cat-morphisms. -/
lemma S2008cat_eqToIso_inv_toNatTrans_app {C D : Type u} [Category C] [Category D]
    {F G : Cat.of C ⟶ Cat.of D} (h : F = G) (M : C) :
    (eqToIso h).inv.toNatTrans.app M =
      eqToHom (congrArg (fun K : Cat.of C ⟶ Cat.of D => K.toFunctor.obj M) h).symm := by
  cases h
  rfl

lemma S2008cat_eqToIso_trans_app {C D : Type u} [Category C] [Category D]
    {F G Hd : Cat.of C ⟶ Cat.of D} (h1 : F = G) (h2 : G = Hd) (M : C) :
    (eqToIso h1 ≪≫ eqToIso h2).hom.toNatTrans.app M =
      (eqToIso h1).hom.toNatTrans.app M ≫ (eqToIso h2).hom.toNatTrans.app M := by
  cases h1
  cases h2
  rfl

lemma S2008cat_eqToIso_trans_inv_app {C D : Type u} [Category C] [Category D]
    {F G Hd : Cat.of C ⟶ Cat.of D} (h1 : F = G) (h2 : G = Hd) (M : C) :
    (eqToIso h1 ≪≫ eqToIso h2).inv.toNatTrans.app M =
      (eqToIso h2).inv.toNatTrans.app M ≫ (eqToIso h1).inv.toNatTrans.app M := by
  cases h1
  cases h2
  rfl

/-- The mapComp coherence of the strict root prestack has trivial unit. -/
lemma S2008mapComp_zeta_hom {a b c : LocallyDiscrete ((Iut.SchemeOverField K)ᵒᵖ)}
    (f : a ⟶ b) (g : b ⟶ c) (M : (S2008PF K l).obj a) :
    (((S2008PF K l).mapComp f g).hom.toNatTrans.app M).zeta = 1 := by
  rw [Functor.toPseudofunctor'_mapComp]
  generalize_proofs hp
  exact (S2008cat_eqToIso_hom_toNatTrans_app (C := ↥((S2008PF K l).obj a))
    (D := ↥((S2008PF K l).obj c)) hp M) ▸ S2008zeta_eqToHom _

lemma S2008mapComp_zeta_inv {a b c : LocallyDiscrete ((Iut.SchemeOverField K)ᵒᵖ)}
    (f : a ⟶ b) (g : b ⟶ c) (M : (S2008PF K l).obj a) :
    (((S2008PF K l).mapComp f g).inv.toNatTrans.app M).zeta = 1 := by
  rw [Functor.toPseudofunctor'_mapComp]
  generalize_proofs hp
  exact (S2008cat_eqToIso_inv_toNatTrans_app (C := ↥((S2008PF K l).obj a))
    (D := ↥((S2008PF K l).obj c)) hp M) ▸ S2008zeta_eqToHom _

/-- The mapComp' coherence of the strict root prestack has trivial unit
(hom version). -/
lemma S2008mapComp'_zeta_hom {a b c : LocallyDiscrete ((Iut.SchemeOverField K)ᵒᵖ)}
    (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg)
    (M : (S2008PF K l).obj a) :
    (((S2008PF K l).mapComp' f g fg h).hom.toNatTrans.app M).zeta = 1 := by
  rw [Pseudofunctor.mapComp', PrelaxFunctor.map₂Iso_eqToIso,
    Functor.toPseudofunctor'_mapComp]
  generalize_proofs h1 h2
  refine (S2008cat_eqToIso_trans_app (C := ↥((S2008PF K l).obj a))
    (D := ↥((S2008PF K l).obj c)) h1 h2 M) ▸ ?_
  have k1 : ((eqToIso h1).hom.toNatTrans.app M).zeta = 1 := 
    (S2008cat_eqToIso_hom_toNatTrans_app (C := ↥((S2008PF K l).obj a))
      (D := ↥((S2008PF K l).obj c)) h1 M) ▸ S2008zeta_eqToHom _
  have k2 : ((eqToIso h2).hom.toNatTrans.app M).zeta = 1 := 
    (S2008cat_eqToIso_hom_toNatTrans_app (C := ↥((S2008PF K l).obj a))
      (D := ↥((S2008PF K l).obj c)) h2 M) ▸ S2008zeta_eqToHom _
  change ((eqToIso h1).hom.toNatTrans.app M).zeta *
    ((eqToIso h2).hom.toNatTrans.app M).zeta = 1
  rw [k1, k2, mul_one]

/-- The mapComp' coherence of the strict root prestack has trivial unit
(inv version). -/
lemma S2008mapComp'_zeta_inv {a b c : LocallyDiscrete ((Iut.SchemeOverField K)ᵒᵖ)}
    (f : a ⟶ b) (g : b ⟶ c) (fg : a ⟶ c) (h : f ≫ g = fg)
    (M : (S2008PF K l).obj a) :
    (((S2008PF K l).mapComp' f g fg h).inv.toNatTrans.app M).zeta = 1 := by
  rw [Pseudofunctor.mapComp', PrelaxFunctor.map₂Iso_eqToIso,
    Functor.toPseudofunctor'_mapComp]
  generalize_proofs h1 h2
  refine (S2008cat_eqToIso_trans_inv_app (C := ↥((S2008PF K l).obj a))
    (D := ↥((S2008PF K l).obj c)) h1 h2 M) ▸ ?_
  have k1 : ((eqToIso h1).inv.toNatTrans.app M).zeta = 1 := 
    (S2008cat_eqToIso_inv_toNatTrans_app (C := ↥((S2008PF K l).obj a))
      (D := ↥((S2008PF K l).obj c)) h1 M) ▸ S2008zeta_eqToHom _
  have k2 : ((eqToIso h2).inv.toNatTrans.app M).zeta = 1 := 
    (S2008cat_eqToIso_inv_toNatTrans_app (C := ↥((S2008PF K l).obj a))
      (D := ↥((S2008PF K l).obj c)) h2 M) ▸ S2008zeta_eqToHom _
  change ((eqToIso h2).inv.toNatTrans.app M).zeta *
    ((eqToIso h1).inv.toNatTrans.app M).zeta = 1
  rw [k1, k2, mul_one]

/-! ## 3. The pullback formula for the unit component -/

/-- Descent of morphisms, unit computation.  The unit component of the
pullback of a root morphism x along a morphism g of the over-site is the
image of x.zeta under the map on global sections.  This closes the
pseudofunctor-coherence obstruction: the zeta-projection is natural. -/
theorem S2008pullHom_zeta (S : Iut.SchemeOverField K)
    (M N : (S2008PF K l).obj (LocallyDiscrete.mk (Opposite.op S)))
    {X Y : Over S} (g : Y ⟶ X)
    (x : ((S2008PF K l).presheafHom M N).obj (Opposite.op X)) :
    (((S2008PF K l).presheafHom M N).map g.op x).zeta =
      Units.map (Scheme.Hom.appTop g.left.left).hom.toMonoidHom x.zeta := by
  simp only [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
  generalize_proofs h1
  generalize hA : (Pseudofunctor.mapComp' (S2008PF K l) X.hom.op.toLoc
    (Over.Hom.left g.op.unop).op.toLoc Y.hom.op.toLoc h1) = iA
  generalize hc : ((S2008PF K l).map (Over.Hom.left g.op.unop).op.toLoc).toFunctor.map x = c
  simp only [ConcreteCategory.hom]
  change (iA.hom.toNatTrans.app M ≫
      ((S2008PF K l).map (Over.Hom.left g.op.unop).op.toLoc).toFunctor.map x ≫
        iA.inv.toNatTrans.app N).zeta = _
  change (iA.hom.toNatTrans.app M).zeta *
      ((((S2008PF K l).map (Over.Hom.left g.op.unop).op.toLoc).toFunctor.map x).zeta *
        (iA.inv.toNatTrans.app N).zeta) =
    Units.map (Scheme.Hom.appTop g.left.left).hom.toMonoidHom x.zeta
  have hc' : (((S2008PF K l).map (Over.Hom.left g.op.unop).op.toLoc).toFunctor.map x).zeta
      = Units.map (Scheme.Hom.appTop g.left.left).hom.toMonoidHom x.zeta := rfl
  have ha : (iA.hom.toNatTrans.app M).zeta = 1 := by
    rw [← hA]
    exact S2008mapComp'_zeta_hom (l := l) X.hom.op.toLoc (Over.Hom.left g.op.unop).op.toLoc
      Y.hom.op.toLoc h1 M
  have hb : (iA.inv.toNatTrans.app N).zeta = 1 := by
    rw [← hA]
    exact S2008mapComp'_zeta_inv (l := l) X.hom.op.toLoc (Over.Hom.left g.op.unop).op.toLoc
      Y.hom.op.toLoc h1 N
  rw [hc', ha, hb, one_mul, mul_one]

/-! ## 4. The pointwise description of the root hom presheaf -/

/-- The elements of the root hom presheaf over a test `T : Over S` are exactly
the root morphisms of S1997 between the two pulled-back objects.  This is a
definitional identity; it is what makes the sheaf condition concrete. -/
theorem S2008presheafHom_obj (S : Iut.SchemeOverField K)
    (M N : (S2008PF K l).obj (LocallyDiscrete.mk (Opposite.op S)))
    (T : (Over S)ᵒᵖ) :
    ((S2008PF K l).presheafHom M N).obj T =
      S1997RootHom (Γ(T.unop.left.left, ⊤)) l
        ((S1997RootMap (Scheme.Hom.appTop T.unop.hom.left).hom l).obj M)
        ((S1997RootMap (Scheme.Hom.appTop T.unop.hom.left).hom l).obj N) := rfl

/-- The `b`-component of a pulled-back root object is the image of `b` under
the map on global sections. -/
theorem S2008RootMap_obj_b (S S' : Iut.SchemeOverField K) (f : S' ⟶ S)
    (M : (S2008PF K l).obj (LocallyDiscrete.mk (Opposite.op S))) :
    ((S1997RootMap (Scheme.Hom.appTop f.left).hom l).obj M).b =
      (Scheme.Hom.appTop f.left).hom M.b := rfl

/-! ## 5. The target and its exact splitting -/

/-- **The target of this file**: descent of morphisms for the l-tors root
prestack with respect to the etale topology. -/
def S2008RootPrestackIsPrestack {l : PrimeGeFive} : Prop :=
  (S2008PF K l.value).IsPrestack (Iut.SchemeOverField.etaleTopology K)

/-- The same statement in fully concrete (coherence-free) form: the presheaf of
root morphisms between any two objects is a sheaf for the etale topology on the
over-site.  `S2008pullHom_zeta` shows that the only obstruction to this being a
*concrete* statement about `(zeta, equation)` pairs -- the pseudofunctor
coherence -- is now closed. -/
def S2008RootHomSheaf {l : PrimeGeFive} : Prop :=
  ∀ {S : Iut.SchemeOverField K}
    (M N : (S2008PF K l.value).obj (LocallyDiscrete.mk (Opposite.op S))),
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology K).over S)
      ((S2008PF K l.value).presheafHom M N)

theorem S2008isPrestack_iff {l : PrimeGeFive} :
    S2008RootPrestackIsPrestack (K := K) (l := l) ↔
      S2008RootHomSheaf (K := K) (l := l) := by
  constructor
  · intro h
    exact fun {S} M N => Pseudofunctor.IsPrestack.isSheaf
      (Iut.SchemeOverField.etaleTopology K) (F := S2008PF K l.value) (self := h) M N
  · intro h
    exact ⟨fun {S} M N => h M N⟩

/-- The exact splitting of the `IsStack` gap: `IsStack` for the root prestack
is precisely descent of morphisms plus effective descent.  Hence
`S2008RootPrestackIsPrestack` shrinks the gap to S1997's effective-descent half
`S1997RootEffectiveDescent`. -/
theorem S2008isStack_iff {l : PrimeGeFive} :
    (S1997RootPrestack K l.value).IsStack (Iut.SchemeOverField.etaleTopology K) ↔
      S2008RootPrestackIsPrestack (K := K) (l := l) ∧
        S1997RootEffectiveDescent K l.value :=
  S1997RootPrestack_isStack_iff (K := K) (l := l)

/-- Combining: once descent of morphisms is available, the only remaining
input for `IsStack` is effective descent. -/
theorem S2008isStack_iff_effDescent {l : PrimeGeFive}
    (hpre : S2008RootPrestackIsPrestack (K := K) (l := l)) :
    (S1997RootPrestack K l.value).IsStack (Iut.SchemeOverField.etaleTopology K) ↔
      S1997RootEffectiveDescent K l.value := by
  constructor
  · intro h
    exact ((S2008isStack_iff (K := K) (l := l)).mp h).2
  · intro h
    exact (S2008isStack_iff (K := K) (l := l)).mpr ⟨hpre, h⟩

/-! ## 6. Axiom footprint -/

#print axioms S2008pullHom_zeta
#print axioms S2008mapComp'_zeta_hom
#print axioms S2008mapComp'_zeta_inv
#print axioms S2008isPrestack_iff
#print axioms S2008isStack_iff

end LeanFormal.IUT.XiFPaper.S2008RootPrestackActual

