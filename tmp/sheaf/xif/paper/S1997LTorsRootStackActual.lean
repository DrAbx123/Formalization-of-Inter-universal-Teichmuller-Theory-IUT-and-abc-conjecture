import tmp.sheaf.xif.paper.S1994KSideCoversActual
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# S1997: the l-tors root stack at the origin -- prestack, stacky point, and exact missing

S1994 isolated the first missing K-side object as an actual non-representable
etale stack over A.K with a certified order-l stacky point at the origin
(the l-tors root stack at the puncture).  This file constructs the honest
pointwise root fibre and its restriction functors, proves that the resulting
category-valued pseudofunctor has a genuine order-l automorphism at the
origin, and isolates the stackification/effective-descent datum which is
exactly the remaining input.

## What is constructed

* S1997RootObj R l: the objects of the pointwise l-tors root fibre at the
  origin over a test ring R: nilpotent sections b with b ^ l = 0.
* S1997RootHom R l x y: the morphisms, units zeta with zeta ^ l = 1 acting by
  multiplication.  This is the honest stabilizer mu_l at the origin, not an
  orbit set.
* S1997RootFiberFunctor K l : (SchemeOverField K)^op to Cat: the strict
  functor sending a test scheme U to the root groupoid of Gamma(U, top), with
  restriction functors along scheme morphisms.  S1997RootPrestack K l is the
  associated category-valued pseudofunctor.
* The cyclic test ring K[Z/l] supplies a genuine order-l unit.  Over
  Spec K[Z/l] the origin 0 has an automorphism S1997CyclicOriginAut of
  order l: S1997CyclicOriginAut_pow and S1997CyclicOriginAut_ne_one.

## Exact first missing

The pointwise root fibre has the required order-l stacky point, but the
global pseudofunctor is not yet an etale stack.  The exact missing datum is a
stack presentation

  S1997RootStackification K l

(section 5): an etale stack Q together with a comparison pseudonatural
transformation from the concrete root prestack, faithful at the origin.  Its
consequence for S1994 is proved conditionally in section 6:
S1997RootStackification A.K l implies S1994StackyOrbicurveMissing l A.

No IsStack instance, sorry, admit, new axiom, PUnit or terminal-stack
substitution is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1200000

namespace LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual

universe u

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1989KSideCover
open LeanFormal.IUT.XiFPaper.S1994KSideCovers

/-! ## 1. The pointwise l-tors root category at the origin -/

structure S1997RootObj (R : Type u) [CommRing R] (l : Nat) where
  b : R
  pow_eq_zero : b ^ l = 0

namespace S1997RootObj

variable {R : Type u} [CommRing R] {l : Nat}

@[ext]
theorem ext {x y : S1997RootObj R l} (h : x.b = y.b) : x = y := by
  cases x
  cases y
  simp_all

end S1997RootObj

structure S1997RootHom (R : Type u) [CommRing R] (l : Nat)
    (x y : S1997RootObj R l) where
  zeta : Rˣ
  zeta_pow : ((zeta : R) ^ l = 1)
  eq : y.b = (zeta : R) * x.b

namespace S1997RootHom

variable {R : Type u} [CommRing R] {l : Nat}
variable {x y z : S1997RootObj R l}

@[ext]
theorem ext {f g : S1997RootHom R l x y} (h : f.zeta = g.zeta) : f = g := by
  cases f
  cases g
  simp_all

def id (x : S1997RootObj R l) : S1997RootHom R l x x where
  zeta := 1
  zeta_pow := by simp
  eq := by simp

def comp (f : S1997RootHom R l x y) (g : S1997RootHom R l y z) :
    S1997RootHom R l x z where
  zeta := f.zeta * g.zeta
  zeta_pow := by
    rw [Units.val_mul, mul_pow, f.zeta_pow, g.zeta_pow, one_mul]
  eq := by
    rw [g.eq, f.eq, Units.val_mul]
    ring

end S1997RootHom

instance S1997RootCategory (R : Type u) [CommRing R] (l : Nat) :
    Category (S1997RootObj R l) where
  Hom x y := S1997RootHom R l x y
  id := S1997RootHom.id
  comp := S1997RootHom.comp
  id_comp f := by
    apply S1997RootHom.ext
    ext
    simp [S1997RootHom.id, S1997RootHom.comp]
  comp_id f := by
    apply S1997RootHom.ext
    ext
    simp [S1997RootHom.id, S1997RootHom.comp]
  assoc f g h := by
    apply S1997RootHom.ext
    ext
    simp [S1997RootHom.comp, mul_assoc]

noncomputable def S1997RootZetaHom {R : Type u} [CommRing R] {l : Nat}
    (x : S1997RootObj R l) : End x →* Rˣ where
  toFun f := f.zeta
  map_one' := by
    change (S1997RootHom.id x).zeta = 1
    rfl
  map_mul' f g := by
    change (S1997RootHom.comp g f).zeta = f.zeta * g.zeta
    change g.zeta * f.zeta = f.zeta * g.zeta
    exact mul_comm g.zeta f.zeta

lemma S1997RootHom_pow_zeta {R : Type u} [CommRing R] {l : Nat}
    {x : S1997RootObj R l} (f : End x) (n : Nat) :
    (f ^ n).zeta = f.zeta ^ n :=
  map_pow (S1997RootZetaHom x) f n

noncomputable def S1997RootMap {R S : Type u} [CommRing R] [CommRing S]
    (phi : R →+* S) (l : Nat) :
    S1997RootObj R l ⥤ S1997RootObj S l where
  obj x := ⟨phi x.b, by rw [← map_pow, x.pow_eq_zero, map_zero]⟩
  map {x y} f :=
    { zeta := Units.map phi.toMonoidHom f.zeta
      zeta_pow := by
        change (phi (f.zeta : R)) ^ l = 1
        rw [← map_pow, f.zeta_pow, map_one]
      eq := by
        change phi y.b = phi (f.zeta : R) * phi x.b
        rw [f.eq, map_mul] }
  map_id x := by
    apply S1997RootHom.ext
    ext
    change phi (1 : R) = (1 : S)
    simp
  map_comp f g := by
    apply S1997RootHom.ext
    ext
    change phi ((f.zeta * g.zeta : Rˣ) : R) =
      ((Units.map phi.toMonoidHom f.zeta * Units.map phi.toMonoidHom g.zeta : Sˣ) : S)
    simp [Units.val_mul, map_mul]

@[simp]
theorem S1997RootMap_id (R : Type u) [CommRing R] (l : Nat) :
    S1997RootMap (RingHom.id R) l = CategoryTheory.Functor.id (S1997RootObj R l) := by
  refine CategoryTheory.Functor.hext (fun x => S1997RootObj.ext rfl) ?_
  intro x y f
  have hx : (S1997RootMap (RingHom.id R) l).obj x =
      (CategoryTheory.Functor.id (S1997RootObj R l)).obj x := S1997RootObj.ext rfl
  have hy : (S1997RootMap (RingHom.id R) l).obj y =
      (CategoryTheory.Functor.id (S1997RootObj R l)).obj y := S1997RootObj.ext rfl
  cases hx
  cases hy
  rfl

theorem S1997RootMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (phi : R →+* S) (psi : S →+* T) (l : Nat) :
    S1997RootMap (psi.comp phi) l = S1997RootMap phi l ⋙ S1997RootMap psi l := by
  refine CategoryTheory.Functor.hext (fun x => S1997RootObj.ext rfl) ?_
  intro x y f
  have hx : (S1997RootMap (psi.comp phi) l).obj x =
      (S1997RootMap phi l ⋙ S1997RootMap psi l).obj x := S1997RootObj.ext rfl
  have hy : (S1997RootMap (psi.comp phi) l).obj y =
      (S1997RootMap phi l ⋙ S1997RootMap psi l).obj y := S1997RootObj.ext rfl
  cases hx
  cases hy
  rfl

/-! ## 2. The category-valued pseudofunctor over the etale site -/

noncomputable def S1997RootFiberFunctor (K : Type u) [Field K] (l : Nat) :
    (Iut.SchemeOverField K)ᵒᵖ ⥤ Cat.{u, u} where
  obj U := Cat.of (S1997RootObj (Γ(U.unop.left, ⊤)) l)
  map {U V} f := (S1997RootMap (Scheme.Hom.appTop f.unop.left).hom l).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    change S1997RootMap (Scheme.Hom.appTop (𝟙 (Opposite.unop U).left)).hom l = _
    rw [Scheme.Hom.id_appTop]
    change S1997RootMap (RingHom.id (Γ((Opposite.unop U).left, ⊤))) l =
      CategoryTheory.Functor.id _
    rw [S1997RootMap_id]
  map_comp {U V W} f g := by
    apply Cat.Hom.ext
    change S1997RootMap (Scheme.Hom.appTop ((f ≫ g).unop.left)).hom l =
      S1997RootMap (Scheme.Hom.appTop f.unop.left).hom l ⋙
        S1997RootMap (Scheme.Hom.appTop g.unop.left).hom l
    rw [show (f ≫ g).unop.left = g.unop.left ≫ f.unop.left by rfl]
    rw [Scheme.Hom.comp_appTop]
    change S1997RootMap
      ((Scheme.Hom.appTop f.unop.left ≫ Scheme.Hom.appTop g.unop.left).hom) l = _
    rw [CommRingCat.hom_comp]
    rw [S1997RootMap_comp]

noncomputable def S1997RootPrestack (K : Type u) [Field K] (l : Nat) :
    Iut.EtaleStackPseudofunctor K :=
  (S1997RootFiberFunctor K l).toPseudofunctor'

@[simp]
theorem S1997RootPrestack_obj (K : Type u) [Field K] (l : Nat)
    (U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) :
    (S1997RootPrestack K l).obj U = Cat.of (S1997RootObj (Γ(U.as.unop.left, ⊤)) l) :=
  rfl

/-! ## 3. The cyclic test ring and the order-l origin automorphism -/

abbrev S1997CyclicRing (K : Type u) [Field K] (l : PrimeGeFive) : Type u :=
  MonoidAlgebra K (Multiplicative (ZMod l.value))

noncomputable def S1997CyclicGen (K : Type u) [Field K] (l : PrimeGeFive) :
    S1997CyclicRing K l :=
  MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod l.value)) (1 : K)

lemma S1997CyclicGen_pow (K : Type u) [Field K] (l : PrimeGeFive) :
    S1997CyclicGen K l ^ l.value = 1 := by
  rw [S1997CyclicGen, MonoidAlgebra.single_pow]
  have hindex : (Multiplicative.ofAdd (1 : ZMod l.value)) ^ l.value = 1 := by
    rw [← ofAdd_nsmul]
    rw [show (l.value • (1 : ZMod l.value)) = 0 by simp]
    exact ofAdd_zero
  have hcoef : (1 : K) ^ l.value = 1 := one_pow _
  rw [hindex, hcoef, MonoidAlgebra.one_def]

lemma S1997CyclicGen_ne_one (K : Type u) [Field K] (l : PrimeGeFive) :
    S1997CyclicGen K l ≠ 1 := by
  intro h
  have hc := congrArg (fun x : S1997CyclicRing K l =>
    x.coeff (Multiplicative.ofAdd (1 : ZMod l.value))) h
  rw [S1997CyclicGen] at hc
  rw [MonoidAlgebra.coeff_single_apply] at hc
  simp only [if_pos rfl] at hc
  have hm : (Multiplicative.ofAdd (1 : ZMod l.value)) ≠ 1 := by
    intro hm
    rw [ofAdd_eq_one] at hm
    have hne : (1 : ZMod l.value) ≠ 0 := by
      intro hzero
      have hn : l.value = 1 := (ZMod.one_eq_zero_iff).mp hzero
      have h5 := l.ge_five
      omega
    exact hne hm
  rw [MonoidAlgebra.one_def] at hc
  rw [MonoidAlgebra.coeff_single_apply] at hc
  have h1m : (1 : Multiplicative (ZMod l.value)) ≠
      Multiplicative.ofAdd (1 : ZMod l.value) := fun h => hm h.symm
  rw [if_neg h1m] at hc
  exact one_ne_zero hc

lemma S1997CyclicGen_unit (K : Type u) [Field K] (l : PrimeGeFive) :
    IsUnit (S1997CyclicGen K l) := by
  apply IsUnit.of_pow_eq_one (S1997CyclicGen_pow K l)
  have h5 := l.ge_five
  omega

noncomputable def S1997CyclicGenUnit (K : Type u) [Field K] (l : PrimeGeFive) :
    (S1997CyclicRing K l)ˣ :=
  (S1997CyclicGen_unit K l).unit

lemma S1997CyclicGenUnit_val (K : Type u) [Field K] (l : PrimeGeFive) :
    ((S1997CyclicGenUnit K l : (S1997CyclicRing K l)ˣ) : S1997CyclicRing K l) =
      S1997CyclicGen K l :=
  IsUnit.unit_spec _

lemma S1997CyclicGenUnit_pow (K : Type u) [Field K] (l : PrimeGeFive) :
    S1997CyclicGenUnit K l ^ l.value = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, S1997CyclicGenUnit_val, S1997CyclicGen_pow, Units.val_one]

lemma S1997CyclicGenUnit_val_pow (K : Type u) [Field K] (l : PrimeGeFive) :
    ((S1997CyclicGenUnit K l : S1997CyclicRing K l) ^ l.value = 1) := by
  rw [← Units.val_pow_eq_pow_val, S1997CyclicGenUnit_pow, Units.val_one]

noncomputable def S1997CyclicScheme (K : Type u) [Field K] (l : PrimeGeFive) :
    Iut.SchemeOverField K :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (S1997CyclicRing K l))))

noncomputable def S1997CyclicSectionsEquiv (K : Type u) [Field K] (l : PrimeGeFive) :
    Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤) ≃+* S1997CyclicRing K l :=
  (Scheme.ΓSpecIso (CommRingCat.of (S1997CyclicRing K l))).commRingCatIsoToRingEquiv

noncomputable def S1997CyclicOrigin (K : Type u) [Field K] (l : PrimeGeFive) :
    S1997RootObj (Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤)) l.value where
  b := (S1997CyclicSectionsEquiv K l).symm 0
  pow_eq_zero := by
    change ((S1997CyclicSectionsEquiv K l).symm 0) ^ l.value = 0
    rw [← map_pow, zero_pow (by have h5 := l.ge_five; omega), map_zero]

@[simp]
lemma S1997CyclicOrigin_b (K : Type u) [Field K] (l : PrimeGeFive) :
    (S1997CyclicOrigin K l).b = 0 := by
  simp [S1997CyclicOrigin]

noncomputable def S1997CyclicOriginAut (K : Type u) [Field K] (l : PrimeGeFive) :
    S1997RootHom (Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤)) l.value
      (S1997CyclicOrigin K l) (S1997CyclicOrigin K l) where
  zeta := Units.map (S1997CyclicSectionsEquiv K l).symm.toMonoidHom
    (S1997CyclicGenUnit K l)
  zeta_pow := by
    change ((S1997CyclicSectionsEquiv K l).symm
      (S1997CyclicGenUnit K l : S1997CyclicRing K l)) ^ l.value = 1
    rw [← map_pow]
    have h : (S1997CyclicGenUnit K l : S1997CyclicRing K l) ^ l.value = 1 :=
      S1997CyclicGenUnit_val_pow K l
    rw [h, map_one]
  eq := by
    change (S1997CyclicOrigin K l).b =
      ((S1997CyclicSectionsEquiv K l).symm
        (S1997CyclicGenUnit K l : S1997CyclicRing K l)) *
        (S1997CyclicOrigin K l).b
    rw [S1997CyclicOrigin]
    simp

noncomputable def S1997CyclicOriginAutEnd (K : Type u) [Field K] (l : PrimeGeFive) :
    End (S1997CyclicOrigin K l) :=
  S1997CyclicOriginAut K l

lemma S1997CyclicOriginAut_pow (K : Type u) [Field K] (l : PrimeGeFive) :
    S1997CyclicOriginAutEnd K l ^ l.value = 1 := by
  apply S1997RootHom.ext
  rw [S1997RootHom_pow_zeta]
  change (S1997CyclicOriginAut K l).zeta ^ l.value = 1
  change (Units.map (S1997CyclicSectionsEquiv K l).symm.toMonoidHom
    (S1997CyclicGenUnit K l)) ^ l.value = 1
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  apply (S1997CyclicSectionsEquiv K l).injective
  rw [map_pow, Units.val_one, map_one]
  change (S1997CyclicSectionsEquiv K l)
    ((S1997CyclicSectionsEquiv K l).symm (S1997CyclicGenUnit K l : S1997CyclicRing K l)) ^
      l.value = 1
  rw [RingEquiv.apply_symm_apply]
  exact S1997CyclicGenUnit_val_pow K l

lemma S1997CyclicOriginAut_ne_one (K : Type u) [Field K] (l : PrimeGeFive) :
    S1997CyclicOriginAutEnd K l ≠ 1 := by
  intro h
  have hzeta : (S1997CyclicOriginAutEnd K l).zeta = 1 := by
    have h' := congrArg S1997RootHom.zeta h
    change (S1997CyclicOriginAutEnd K l).zeta =
      (S1997RootHom.id (S1997CyclicOrigin K l)).zeta at h'
    simpa [S1997RootHom.id] using h'
  have hval : (S1997CyclicSectionsEquiv K l)
      ((Units.map (S1997CyclicSectionsEquiv K l).symm.toMonoidHom
        (S1997CyclicGenUnit K l) :
        (Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤))ˣ) :
        Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤)) = 1 := by
    simpa [S1997CyclicOriginAutEnd, S1997CyclicOriginAut] using
      congrArg (fun u : (Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤))ˣ =>
        (S1997CyclicSectionsEquiv K l)
          (u : Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤))) hzeta
  have hg : S1997CyclicGenUnit K l = 1 := by
    simpa using hval
  have hgval := congrArg (fun u : (S1997CyclicRing K l)ˣ =>
    (u : S1997CyclicRing K l)) hg
  rw [S1997CyclicGenUnit_val] at hgval
  exact S1997CyclicGen_ne_one K l hgval

/-! ## 4. The pointwise stacky-point statement for the prestack -/

def S1997HasPointAutOfOrder (K : Type u) [Field K]
    (P : Iut.EtaleStackPseudofunctor K) (n : Nat) : Prop :=
  ∃ (U : Iut.SchemeOverField K)
    (X : (P.obj (LocallyDiscrete.mk (Opposite.op U))))
    (f : End X), f ≠ 1 ∧ f ^ n = 1

theorem S1997RootPrestack_hasPointAutOfOrder (K : Type u) [Field K]
    (l : PrimeGeFive) :
    S1997HasPointAutOfOrder K (S1997RootPrestack K l.value) l.value := by
  refine ⟨S1997CyclicScheme K l, S1997CyclicOrigin K l,
    S1997CyclicOriginAutEnd K l, S1997CyclicOriginAut_ne_one K l,
    S1997CyclicOriginAut_pow K l⟩

/-! ## 5. The stackification datum and the exact first missing -/

structure S1997RootStackification (K : Type u) [Field K] (l : PrimeGeFive) where
  stack : Iut.EtaleStackPseudofunctor K
  isStack : stack.IsStack (Iut.SchemeOverField.etaleTopology K)
  comparison : Pseudofunctor.StrongTrans (S1997RootPrestack K l.value) stack
  origin_faithful :
    ∀ f : End (S1997CyclicOrigin K l),
      (comparison.app (LocallyDiscrete.mk
        (Opposite.op (S1997CyclicScheme K l)))).toFunctor.map f =
          𝟙 ((comparison.app (LocallyDiscrete.mk
            (Opposite.op (S1997CyclicScheme K l)))).toFunctor.obj
              (S1997CyclicOrigin K l)) →
        f = 𝟙 (S1997CyclicOrigin K l)

def S1997RootStackificationMissing (K : Type u) [Field K] (l : PrimeGeFive) :
    Prop :=
  Nonempty (S1997RootStackification K l)

def S1997RootEffectiveDescent (K : Type u) [Field K] (l : Nat) : Prop :=
  ∀ (U : Iut.SchemeOverField K) (R : Sieve U), R ∈ Iut.SchemeOverField.etaleTopology K U →
    ((S1997RootPrestack K l).toDescentData
      (fun i : R.arrows.category => i.obj.hom)).EssSurj

/-! ## 6. Conditional consequence: a stack presentation gives S1994's missing object -/

noncomputable def S1997EndMap {C D : Type u} [Category C] [Category D]
    (F : C ⥤ D) (X : C) : End X →* End (F.obj X) where
  toFun f := F.map f
  map_one' := F.map_id X
  map_mul' f g := by
    change F.map (g ≫ f) = F.map g ≫ F.map f
    rw [F.map_comp]

theorem S1997RootStackification_stackyOrbicurve (K : Type u) [Field K]
    (l : PrimeGeFive) (P : S1997RootStackification K l) :
    ∃ X : Iut.HyperbolicOrbicurve K,
      S1994HasAutOfOrder (F := K) X l.value := by
  let U : Iut.SchemeOverField K := S1997CyclicScheme K l
  let u : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ :=
    LocallyDiscrete.mk (Opposite.op U)
  let P0 : (S1997RootPrestack K l.value).obj u := S1997CyclicOrigin K l
  let f0 : End P0 := S1997CyclicOriginAutEnd K l
  let e := (P.comparison.app u).toFunctor
  let P1 : P.stack.obj u := e.obj P0
  let f1 : End P1 := e.map f0
  have hf1_ne : f1 ≠ 𝟙 P1 := by
    intro h
    have h' : e.map f0 = 𝟙 (e.obj P0) := h
    exact S1997CyclicOriginAut_ne_one K l (P.origin_faithful f0 h')
  have hf1_pow : f1 ^ l.value = 1 := by
    have h := map_pow (S1997EndMap e P0) f0 l.value
    change e.map (f0 ^ l.value) = f1 ^ l.value at h
    have h0 : f0 ^ l.value = 1 := S1997CyclicOriginAut_pow K l
    rw [h0] at h
    change e.map (𝟙 P0) = f1 ^ l.value at h
    rw [e.map_id] at h
    exact h.symm
  let X : Iut.HyperbolicOrbicurve K :=
    realizedHyperbolicOrbicurve K P.stack P.isStack
      (sourceTypeOneLTorsion l) (sourceTypeOneLTorsion_hyperbolic l)
  refine ⟨X, ?_⟩
  exact ⟨U, P1, f1, hf1_ne, hf1_pow⟩

theorem S1997RootStackification_stackyOrbicurve_not_representable
    (K : Type u) [Field K] (l : PrimeGeFive) (P : S1997RootStackification K l) :
    ∃ X : Iut.HyperbolicOrbicurve K,
      S1994HasAutOfOrder (F := K) X l.value ∧
        ∀ (Y : Iut.SchemeOverField K) (σ : Iut.OrbicurveSignature)
          (hσ : σ.IsHyperbolic),
          X ≠ S1994RepresentableOrbicurve (F := K) Y σ hσ := by
  obtain ⟨X, hX⟩ := S1997RootStackification_stackyOrbicurve K l P
  refine ⟨X, hX, ?_⟩
  intro Y σ hσ hEq
  exact S1994RepresentableOrbicurve_noAutOfOrder (F := K) Y σ hσ l.value
    (hEq ▸ hX)

theorem S1994StackyOrbicurveMissing_of_rootStackification
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (P : S1997RootStackification A.K l) :
    S1994StackyOrbicurveMissing l A :=
  S1997RootStackification_stackyOrbicurve A.K l P

def S1997FirstMissing (l : PrimeGeFive) (A : InitialThetaArithmeticData l) :
    Prop :=
  S1997RootStackificationMissing A.K l

theorem S1997FirstMissing_implies_S1994Stacky
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (h : S1997FirstMissing l A) :
    S1994StackyOrbicurveMissing l A := by
  obtain ⟨P⟩ := h
  exact S1994StackyOrbicurveMissing_of_rootStackification P

end LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual

/-! ## 7. Axiom footprint -/

#print axioms LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual.S1997RootPrestack_hasPointAutOfOrder
#print axioms LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual.S1997CyclicOriginAut_pow
#print axioms LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual.S1997CyclicOriginAut_ne_one
#print axioms LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual.S1997RootStackification_stackyOrbicurve
#print axioms LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual.S1997RootStackification_stackyOrbicurve_not_representable
#print axioms LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual.S1994StackyOrbicurveMissing_of_rootStackification
#print axioms LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual.S1997FirstMissing_implies_S1994Stacky
