import tmp.sheaf.xif.paper.S2019RebasedRootStackActual

/-!
# S2022: the quotient stack [Z / mu_l] -- torsor-stack package and exact first missing

S2002 §5 isolated the *mathematical* content of the root-stack missing: the direct
construction of the quotient stack

  [Z / mu_l],  Z = Spec K[t]/t^l,  mu_l = Spec K[t,t^{-1}]/(t^l - 1),
  zeta . b = zeta * b,

whose U-points are mu_l-torsors P on the etale site of U together with a
mu_l-equivariant map P -> Z.  S2019 then proved that rebasing the *prestack*
route on S2015's corrected full descent is conservative:
S2019FirstMissing <-> S1997RootEffectiveDescent <-> IsStack for the root prestack.
So the prestack route cannot be repaired by strengthening its stack condition.

This file builds the quotient-stack / torsor-stack package and pins down what is
missing, without fabricating an IsStack instance.

## What is constructed (unconditionally, at the pointwise level)

1. S2022Mu R l: the group of l-th roots of unity in a commutative ring R,
   as the subgroup of R^x cut out by zeta^l = 1, i.e. the functor of points of
   mu_l = Spec K[t,t^{-1}]/(t^l-1) on affines.  Functoriality in R is
   S2022Mu.map.

2. S2022Zc R l: the thickened origin {b : R // b^l = 0} (the functor of points
   of Z = Spec K[t]/t^l), with the action zeta . b = zeta * b
   (S2022Zc.smul), its action laws, and the action groupoid
   S2022Zhom (zeta with y = zeta * x), which is a groupoid
   (S2022ZhomGroupoid).

3. The comparison at the pointwise level: the action groupoid of mu_l on the
   thickened origin *is* the S1997 root fibre (S2022toRoot, S2022zhEquiv,
   S2022ofRoot), i.e. the action-groupoid presentation of [Z / mu_l].

4. (ii) the associated twist: for a principal homogeneous space P of mu_l,
   the twist (P x Z)/mu_l (S2022PHS.twist), and the torsor/twist dictionary

     { mu_l-equivariant maps P -> Z }  =  points of the twist
     (S2022PHS.twistEquivariantEquiv),

   proved by the graph of the equivariant map; every PHS is trivial
   (S2022PHS.trivialize), which is why the pointwise twist is *isomorphic* to Z.

5. (iv) the comparison, fully: for every commutative ring R,

   * objects: Z(R) is equivalent to the equivariant maps from the trivial torsor
     to Z (S2022PhiEquiv);
   * morphisms: the twisted hom set {c : mu_l // c * y = x} is equivalent to
     S1997RootHom x y (S2022PhiTwistHomEquiv), with the comparison sending a
     root morphism zeta to the right translation by zeta^{-1}.

   Consequently the comparison is fully faithful on the trivial-torsor locus, and in
   particular faithful at the origin: at b = 0 the automorphism group is all of
   mu_l (S2022PhiTwistHomZero, S2022RootHomZeroEquiv), matching S1997CyclicOriginAut.

## The package and the exact first missing

6. S2022QuotientStackPackage K l is the quotient-stack package: a
   category-valued etale stack Q, its stack condition Q.IsStack, the comparison
   S1997RootPrestack K l -> Q, and *full faithfulness* of that comparison at every
   test object.  Item (iv) is **not** an extra assumption for the actual [Z/mu_l]:
   §4 proves it pointwise (objects and homs), so the package is exactly S2002's
   items (i)+(iii) together with the already constructed comparison data.

7. Reductions:
   * S2022QuotientStackPackage.toRootStackification: the package gives S1997's
     root stackification, with origin_faithful *derived* from full faithfulness
     (S2022QuotientStackPackage.faithfulAtOrigin), not postulated;
   * the consumer chain to S1994's stacky orbicurve, and to S2019's corrected datum;
   * S2022QuotientStackPackage.prestack_iff_S2019FirstMissing: the package is
     realised by the root prestack itself **iff** the root prestack is a stack, i.e.
     exactly S2019FirstMissing.  Hence the quotient-stack route is a genuine
     relaxation of the prestack route, and the Kummer effective-descent failure which
     S2002/S2019 record does not block it.

8. S2022FirstMissing K l := Nonempty (S2022QuotientStackPackage K l) is the exact
   first missing: the existence of the etale-local quotient stack as a *stack*, i.e.
   the Giraud/stackification input (the stack of etale-locally trivial mu_l-torsors)
   for this particular action.  It is not proved here, no IsStack instance is
   asserted, and the package is not satisfiable by any representable or discrete
   stack (S2002's no-go).  The pointwise model does *not* satisfy it: pointwise every
   torsor is trivial, so pointwise the comparison is an equivalence, while etale
   local triviality is exactly what fails to be global.

## Honest boundary

No sorry, no new axiom, no Shrink/ULift/PUnit, no fabricated stack, equivalence,
2-cell or IsStack instance.  S2022FirstMissing is a named proposition with no
inhabitant asserted.  The only axioms used are propext, Classical.choice and
Quot.sound.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2022QuotientStackActual

open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1994KSideCovers
open LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
open LeanFormal.IUT.XiFPaper.S2002RootStackificationActual
open LeanFormal.IUT.XiFPaper.S2019RebasedRootStackActual

universe u

variable {K : Type u} [Field K] {l : PrimeGeFive}

/-! ## 1. The group mu_l and the thickened origin Z -/

/-- The group mu_l of l-th roots of unity in a commutative ring R: the functor of
points of mu_l = Spec K[t,t^{-1}]/(t^l - 1) on affines. -/
def S2022Mu (R : Type u) [CommRing R] (l : Nat) : Subgroup Rˣ where
  carrier := {ζ | ((ζ : R) ^ l = 1)}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [Units.val_mul, mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    have hua : a ^ l = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ha, Units.val_one]
    show ((a⁻¹ : Rˣ) : R) ^ l = 1
    rw [← Units.val_pow_eq_pow_val, inv_pow, hua, inv_one, Units.val_one]

/-- The value of an l-torsion unit. -/
lemma S2022Mu.pow_eq_one {R : Type u} [CommRing R] {l : Nat} (ζ : ↥(S2022Mu R l)) :
    ((ζ.1 : R) ^ l = 1) := ζ.2

/-- Functoriality of mu_l in the ring. -/
def S2022Mu.map {R S : Type u} [CommRing R] [CommRing S] (phi : R →+* S) (l : Nat) :
    ↥(S2022Mu R l) →* ↥(S2022Mu S l) where
  toFun ζ :=
    ⟨Units.map phi.toMonoidHom ζ.1, by
      change (phi (ζ.1 : R)) ^ l = 1
      rw [← map_pow, ζ.2, map_one]⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    simp [Units.val_mul]

@[simp]
lemma S2022Mu.map_val {R S : Type u} [CommRing R] [CommRing S] (phi : R →+* S) (l : Nat)
    (ζ : ↥(S2022Mu R l)) :
    (((S2022Mu.map phi l ζ).1 : Sˣ) : S) = phi (ζ.1 : R) := rfl

/-- The thickened origin Z = Spec K[t]/t^l over a commutative ring: nilpotent
sections of order l. -/
abbrev S2022Zc (R : Type u) [CommRing R] (l : Nat) := {b : R // b ^ l = 0}

/-- The origin b = 0 (only for positive l). -/
def S2022Zc.zero (R : Type u) [CommRing R] (l : Nat) (h : 0 < l) : S2022Zc R l :=
  ⟨0, by rw [zero_pow h.ne']⟩

/-- Restriction of the thickened origin along a ring homomorphism. -/
def S2022Zc.map {R S : Type u} [CommRing R] [CommRing S] (phi : R →+* S) {l : Nat}
    (b : S2022Zc R l) : S2022Zc S l :=
  ⟨phi b.1, by rw [← map_pow, b.2, map_zero]⟩

/-- The action zeta . b = zeta * b of mu_l on the thickened origin. -/
def S2022Zc.smul {R : Type u} [CommRing R] {l : Nat} (ζ : ↥(S2022Mu R l))
    (b : S2022Zc R l) : S2022Zc R l :=
  ⟨(ζ.1 : R) * b.1, by rw [mul_pow, b.2, mul_zero]⟩

@[simp]
lemma S2022Zc.smul_val {R : Type u} [CommRing R] {l : Nat} (ζ : ↥(S2022Mu R l))
    (b : S2022Zc R l) : (S2022Zc.smul ζ b).1 = (ζ.1 : R) * b.1 := rfl

lemma S2022Zc.smul_one {R : Type u} [CommRing R] {l : Nat} (b : S2022Zc R l) :
    S2022Zc.smul (1 : ↥(S2022Mu R l)) b = b := by
  apply Subtype.ext
  simp [S2022Zc.smul]

lemma S2022Zc.smul_mul {R : Type u} [CommRing R] {l : Nat} (ζ η : ↥(S2022Mu R l))
    (b : S2022Zc R l) :
    S2022Zc.smul ζ (S2022Zc.smul η b) = S2022Zc.smul (ζ * η) b := by
  apply Subtype.ext
  simp [S2022Zc.smul, mul_assoc]

/-- The hom set of the action groupoid of mu_l on the thickened origin: a unit zeta
with y = zeta * x.  This is exactly the S1997 root hom. -/
abbrev S2022Zhom {R : Type u} [CommRing R] (l : Nat) (x y : S2022Zc R l) : Type u :=
  {ζ : ↥(S2022Mu R l) // y.1 = (ζ.1 : R) * x.1}

lemma S2022Zhom.ext {R : Type u} [CommRing R] {l : Nat} {x y : S2022Zc R l}
    {f g : S2022Zhom l x y} (h : f.1 = g.1) : f = g := by
  cases f; cases g; simp_all

def S2022Zhom.id {R : Type u} [CommRing R] {l : Nat} (x : S2022Zc R l) :
    S2022Zhom l x x := ⟨1, by simp⟩

def S2022Zhom.comp {R : Type u} [CommRing R] {l : Nat} {x y z : S2022Zc R l}
    (f : S2022Zhom l x y) (g : S2022Zhom l y z) : S2022Zhom l x z :=
  ⟨f.1 * g.1, by
    have hg : z.1 = (g.1.1 : R) * y.1 := g.2
    have hf : y.1 = (f.1.1 : R) * x.1 := f.2
    calc z.1 = (g.1.1 : R) * y.1 := hg
      _ = (g.1.1 : R) * ((f.1.1 : R) * x.1) :=
            congrArg (fun t : R => (g.1.1 : R) * t) hf
      _ = ((f.1 * g.1).1 : R) * x.1 := by
            rw [Subgroup.coe_mul, Units.val_mul]
            ring⟩

instance S2022Zcat {R : Type u} [CommRing R] (l : Nat) : Category (S2022Zc R l) where
  Hom x y := S2022Zhom l x y
  id x := S2022Zhom.id x
  comp f g := S2022Zhom.comp f g
  id_comp f := by apply S2022Zhom.ext; simp [S2022Zhom.id, S2022Zhom.comp]
  comp_id f := by apply S2022Zhom.ext; simp [S2022Zhom.id, S2022Zhom.comp]
  assoc f g h := by apply S2022Zhom.ext; simp [S2022Zhom.comp, mul_assoc]

/-- The inverse hom of the action groupoid (the action is by units). -/
def S2022Zhom.inv {R : Type u} [CommRing R] {l : Nat} {x y : S2022Zc R l}
    (f : S2022Zhom l x y) : S2022Zhom l y x :=
  ⟨f.1⁻¹, by
    have hf : y.1 = (f.1.1 : R) * x.1 := f.2
    calc x.1 = ((f.1⁻¹ * f.1 : ↥(S2022Mu R l)).1 : R) * x.1 := by
          rw [inv_mul_cancel, Subgroup.coe_one, Units.val_one, one_mul]
      _ = (f.1⁻¹.1 : R) * ((f.1.1 : R) * x.1) := by
          rw [Subgroup.coe_mul, Units.val_mul]
          ring
      _ = (f.1⁻¹.1 : R) * y.1 :=
            (congrArg (fun t : R => (f.1⁻¹.1 : R) * t) hf).symm⟩

lemma S2022Zhom.inv_comp {R : Type u} [CommRing R] {l : Nat} {x y : S2022Zc R l}
    (f : S2022Zhom l x y) :
    S2022Zhom.comp (S2022Zhom.inv f) f = S2022Zhom.id y := by
  apply S2022Zhom.ext
  simp [S2022Zhom.inv, S2022Zhom.comp, S2022Zhom.id]

lemma S2022Zhom.comp_inv {R : Type u} [CommRing R] {l : Nat} {x y : S2022Zc R l}
    (f : S2022Zhom l x y) :
    S2022Zhom.comp f (S2022Zhom.inv f) = S2022Zhom.id x := by
  apply S2022Zhom.ext
  simp [S2022Zhom.inv, S2022Zhom.comp, S2022Zhom.id]

instance S2022ZhomGroupoid {R : Type u} [CommRing R] (l : Nat) : Groupoid (S2022Zc R l) where
  inv f := S2022Zhom.inv f
  inv_comp f := S2022Zhom.inv_comp f
  comp_inv f := S2022Zhom.comp_inv f

/-! ## 2. The action groupoid is the S1997 root fibre -/

/-- The action-groupoid hom is the S1997 root hom: same unit, same equation. -/
def S2022zhEquiv {R : Type u} [CommRing R] {l : Nat} (x y : S2022Zc R l) :
    S2022Zhom l x y ≃ S1997RootHom R l ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ where
  toFun f := ⟨f.1.1, f.1.2, f.2⟩
  invFun f := ⟨⟨f.zeta, f.zeta_pow⟩, f.eq⟩
  left_inv f := by cases f; rfl
  right_inv f := by cases f; rfl

/-- The action groupoid maps to the S1997 root fibre. -/
def S2022toRoot {R : Type u} [CommRing R] (l : Nat) :
    S2022Zc R l ⥤ S1997RootObj R l where
  obj x := ⟨x.1, x.2⟩
  map f := ⟨f.1.1, f.1.2, f.2⟩
  map_id x := by apply S1997RootHom.ext; rfl
  map_comp f g := by apply S1997RootHom.ext; rfl

/-- The S1997 root fibre maps back to the action groupoid. -/
def S2022ofRoot {R : Type u} [CommRing R] (l : Nat) :
    S1997RootObj R l ⥤ S2022Zc R l where
  obj x := ⟨x.b, x.pow_eq_zero⟩
  map f := ⟨⟨f.zeta, f.zeta_pow⟩, f.eq⟩
  map_id x := by apply S2022Zhom.ext; rfl
  map_comp f g := by apply S2022Zhom.ext; rfl

lemma S2022toRoot_obj {R : Type u} [CommRing R] {l : Nat} (x : S2022Zc R l) :
    (S2022toRoot l).obj x = ⟨x.1, x.2⟩ := rfl

lemma S2022ofRoot_obj {R : Type u} [CommRing R] {l : Nat} (x : S1997RootObj R l) :
    (S2022ofRoot l).obj x = ⟨x.b, x.pow_eq_zero⟩ := rfl

theorem S2022toRoot_comp_ofRoot {R : Type u} [CommRing R] (l : Nat) :
    S2022toRoot l ⋙ S2022ofRoot l = 𝟭 (S2022Zc R l) := by
  refine CategoryTheory.Functor.hext (fun x => Subtype.ext rfl) ?_
  intro x y f
  have hx : (S2022toRoot l ⋙ S2022ofRoot l).obj x = (𝟭 (S2022Zc R l)).obj x :=
    Subtype.ext rfl
  have hy : (S2022toRoot l ⋙ S2022ofRoot l).obj y = (𝟭 (S2022Zc R l)).obj y :=
    Subtype.ext rfl
  cases hx
  cases hy
  rfl

theorem S2022ofRoot_comp_toRoot {R : Type u} [CommRing R] (l : Nat) :
    S2022ofRoot l ⋙ S2022toRoot l = 𝟭 (S1997RootObj R l) := by
  refine CategoryTheory.Functor.hext (fun x => S1997RootObj.ext rfl) ?_
  intro x y f
  have hx : (S2022ofRoot l ⋙ S2022toRoot l).obj x = (𝟭 (S1997RootObj R l)).obj x :=
    S1997RootObj.ext rfl
  have hy : (S2022ofRoot l ⋙ S2022toRoot l).obj y = (𝟭 (S1997RootObj R l)).obj y :=
    S1997RootObj.ext rfl
  cases hx
  cases hy
  rfl

/-- The action groupoid of mu_l on the thickened origin is the S1997 root fibre:
the pointwise presentation of [Z / mu_l] is the root prestack. -/
def S2022ZEquivRoot {R : Type u} [CommRing R] (l : Nat) :
    CategoryTheory.Equivalence (S2022Zc R l) (S1997RootObj R l) :=
  CategoryTheory.Equivalence.mk (S2022toRoot l) (S2022ofRoot l)
    (eqToIso (S2022toRoot_comp_ofRoot l).symm) (eqToIso (S2022ofRoot_comp_toRoot l))

/-! ## 3. Principal homogeneous spaces, triviality, and the associated twist -/

/-- A principal homogeneous space for mu_l over a commutative ring: a nonempty set with
a free and transitive action of the l-torsion units.  This is the pointwise (Zariski,
not yet etale-local) notion of a torsor; the etale-local version is what the quotient
stack construction needs and is the content of the first missing. -/
structure S2022PHS (R : Type u) [CommRing R] (l : Nat) where
  /-- The underlying type. -/
  P : Type u
  /-- The action of the l-torsion units. -/
  smul : ↥(S2022Mu R l) → P → P
  one_smul : ∀ p : P, smul 1 p = p
  mul_smul : ∀ (ζ η : ↥(S2022Mu R l)) (p : P), smul ζ (smul η p) = smul (ζ * η) p
  free : ∀ (ζ : ↥(S2022Mu R l)) (p : P), smul ζ p = p → ζ = 1
  transitive : ∀ p q : P, ∃ ζ : ↥(S2022Mu R l), smul ζ p = q
  nonempty : Nonempty P

/-- A mu_l-equivariant map from a PHS to the thickened origin. -/
def S2022IsEquivariant {R : Type u} [CommRing R] {l : Nat} (P : S2022PHS R l)
    (φ : P.P → S2022Zc R l) : Prop :=
  ∀ (ζ : ↥(S2022Mu R l)) (p : P.P), φ (P.smul ζ p) = S2022Zc.smul ζ (φ p)

namespace S2022PHS

variable {R : Type u} [CommRing R] {l : Nat}

/-- The action at a fixed point is injective: freeness in the form used below. -/
lemma smul_inj (P : S2022PHS R l) (p : P.P) :
    Function.Injective (fun ζ : ↥(S2022Mu R l) => P.smul ζ p) := by
  intro ζ η h
  have h1 : P.smul (ζ * η⁻¹) (P.smul η p) = P.smul η p := by
    rw [P.mul_smul]
    have hc : ζ * η⁻¹ * η = ζ := by rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [hc]
    exact h
  have h2 : ζ * η⁻¹ = 1 := P.free (ζ * η⁻¹) (P.smul η p) h1
  calc ζ = ζ * η⁻¹ * η := by rw [mul_assoc, inv_mul_cancel, mul_one]
    _ = 1 * η := by rw [h2]
    _ = η := one_mul η

/-- Every principal homogeneous space is trivial: choosing a point identifies it with
mu_l.  This is why the pointwise quotient model coincides with the action groupoid and
why the missing input is exactly *etale local* triviality. -/
def trivialize (P : S2022PHS R l) (p₀ : P.P) : P.P ≃ ↥(S2022Mu R l) where
  toFun q := Classical.choose (P.transitive p₀ q)
  invFun ζ := P.smul ζ p₀
  left_inv q := Classical.choose_spec (P.transitive p₀ q)
  right_inv ζ := P.smul_inj p₀ (Classical.choose_spec (P.transitive p₀ (P.smul ζ p₀)))

lemma smul_trivialize (P : S2022PHS R l) (p₀ : P.P) (p : P.P) :
    P.smul (P.trivialize p₀ p) p₀ = p :=
  Classical.choose_spec (P.transitive p₀ p)

lemma trivialize_self (P : S2022PHS R l) (p₀ : P.P) : P.trivialize p₀ p₀ = 1 := by
  apply P.smul_inj p₀
  show P.smul (P.trivialize p₀ p₀) p₀ = P.smul 1 p₀
  rw [P.smul_trivialize, P.one_smul]

lemma smul_inv_trivialize (P : S2022PHS R l) (p₀ : P.P) (p : P.P) :
    P.smul (P.trivialize p₀ p)⁻¹ p = p₀ := by
  calc P.smul (P.trivialize p₀ p)⁻¹ p
      = P.smul (P.trivialize p₀ p)⁻¹ (P.smul (P.trivialize p₀ p) p₀) :=
          congrArg (P.smul (P.trivialize p₀ p)⁻¹) (P.smul_trivialize p₀ p).symm
    _ = P.smul ((P.trivialize p₀ p)⁻¹ * P.trivialize p₀ p) p₀ := P.mul_smul _ _ _
    _ = P.smul 1 p₀ := by rw [inv_mul_cancel]
    _ = p₀ := P.one_smul p₀

lemma trivialize_smul (P : S2022PHS R l) (p₀ : P.P) (ζ : ↥(S2022Mu R l)) (p : P.P) :
    P.trivialize p₀ (P.smul ζ p) = ζ * P.trivialize p₀ p := by
  apply P.smul_inj p₀
  show P.smul (P.trivialize p₀ (P.smul ζ p)) p₀ = P.smul (ζ * P.trivialize p₀ p) p₀
  rw [P.smul_trivialize, ← P.mul_smul, P.smul_trivialize]

/-- The trivial torsor: mu_l acting on itself by left translations. -/
@[reducible] def trivial (R : Type u) [CommRing R] (l : Nat) : S2022PHS R l where
  P := ↥(S2022Mu R l)
  smul ζ p := ζ * p
  one_smul p := one_mul p
  mul_smul ζ η p := (mul_assoc ζ η p).symm
  free ζ p h := by
    have h2 : ζ * p * p⁻¹ = p * p⁻¹ := by rw [h]
    rw [mul_assoc, mul_inv_cancel, mul_one] at h2
    exact h2
  transitive p q := ⟨q * p⁻¹, by rw [mul_assoc, inv_mul_cancel, mul_one]⟩
  nonempty := ⟨1⟩

/-! ### The twist (P x Z)/mu_l -/

/-- The diagonal action of mu_l on P x Z. -/
def twistSmul (P : S2022PHS R l) (ζ : ↥(S2022Mu R l))
    (x : P.P × S2022Zc R l) : P.P × S2022Zc R l :=
  (P.smul ζ x.1, S2022Zc.smul ζ x.2)

lemma twistSmul_one (P : S2022PHS R l) (x : P.P × S2022Zc R l) :
    P.twistSmul 1 x = x := by
  apply Prod.ext
  · exact P.one_smul x.1
  · exact S2022Zc.smul_one x.2

lemma twistSmul_mul (P : S2022PHS R l) (ζ η : ↥(S2022Mu R l))
    (x : P.P × S2022Zc R l) :
    P.twistSmul ζ (P.twistSmul η x) = P.twistSmul (ζ * η) x := by
  apply Prod.ext
  · exact P.mul_smul ζ η x.1
  · exact S2022Zc.smul_mul ζ η x.2

/-- The relation 'a is in the mu_l-orbit of b' on P x Z. -/
def twistRel (P : S2022PHS R l) (a b : P.P × S2022Zc R l) : Prop :=
  ∃ ζ : ↥(S2022Mu R l), a = P.twistSmul ζ b

/-- The twist of the thickened origin by a principal homogeneous space: the orbit
space (P x Z)/mu_l. -/
def twistSetoid (P : S2022PHS R l) : Setoid (P.P × S2022Zc R l) where
  r := P.twistRel
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro a
      exact ⟨1, by rw [P.twistSmul_one]⟩
    · intro a b h
      obtain ⟨ζ, rfl⟩ := h
      exact ⟨ζ⁻¹, by rw [P.twistSmul_mul, inv_mul_cancel, P.twistSmul_one]⟩
    · intro a b c hab hbc
      obtain ⟨ζ, rfl⟩ := hab
      obtain ⟨η, rfl⟩ := hbc
      exact ⟨ζ * η, by rw [P.twistSmul_mul]⟩

/-- The twist (P x Z)/mu_l as a type. -/
def twist (P : S2022PHS R l) : Type u := Quot P.twistSetoid

/-- The class of a point of P x Z in the twist. -/
def twistMk (P : S2022PHS R l) (x : P.P × S2022Zc R l) : P.twist := Quot.mk _ x

/-- The section of the twist attached to a point: [p, b] is transported to Z by
dividing by the trivialization of p. -/
def twistToZ (P : S2022PHS R l) (p₀ : P.P) : P.twist → S2022Zc R l :=
  Quot.lift
    (fun x : P.P × S2022Zc R l => S2022Zc.smul (P.trivialize p₀ x.1)⁻¹ x.2)
    (by
      intro a b hab
      obtain ⟨ζ, rfl⟩ := hab
      show S2022Zc.smul (P.trivialize p₀ (P.smul ζ b.1))⁻¹ (S2022Zc.smul ζ b.2) =
        S2022Zc.smul (P.trivialize p₀ b.1)⁻¹ b.2
      rw [P.trivialize_smul, S2022Zc.smul_mul]
      have h : (ζ * P.trivialize p₀ b.1)⁻¹ * ζ = (P.trivialize p₀ b.1)⁻¹ := by group
      rw [h])

lemma twistToZ_mk (P : S2022PHS R l) (p₀ : P.P) (x : P.P × S2022Zc R l) :
    P.twistToZ p₀ (P.twistMk x) = S2022Zc.smul (P.trivialize p₀ x.1)⁻¹ x.2 := rfl

/-- The zero section: the class of (p₀, b). -/
def twistOfZ (P : S2022PHS R l) (p₀ : P.P) (b : S2022Zc R l) : P.twist :=
  P.twistMk (p₀, b)

/-- **The twist of Z by a torsor is Z**, canonically once a point p₀ of the torsor is
chosen: points of the twist are points of the thickened origin. -/
def twistEquiv (P : S2022PHS R l) (p₀ : P.P) : P.twist ≃ S2022Zc R l where
  toFun := P.twistToZ p₀
  invFun := P.twistOfZ p₀
  left_inv := by
    intro t
    induction t using Quot.ind with
    | mk a =>
      apply Quot.sound
      refine ⟨(P.trivialize p₀ a.1)⁻¹, ?_⟩
      apply Prod.ext
      · exact (P.smul_inv_trivialize p₀ a.1).symm
      · rfl
  right_inv := by
    intro b
    show S2022Zc.smul (P.trivialize p₀ p₀)⁻¹ b = b
    rw [P.trivialize_self, inv_one]
    exact S2022Zc.smul_one b

/-! ### Equivariant maps and the torsor/twist dictionary -/

/-- The graph of an equivariant map, evaluated at p₀, is a point of the twist. -/
def twistGraph (P : S2022PHS R l) (p₀ : P.P) (φ : P.P → S2022Zc R l) : P.twist :=
  P.twistMk (p₀, φ p₀)

/-- The equivariant map attached to a point of the twist. -/
def twistEquivariantMap (P : S2022PHS R l) (p₀ : P.P) (t : P.twist) :
    P.P → S2022Zc R l :=
  fun q => S2022Zc.smul (P.trivialize p₀ q) (P.twistToZ p₀ t)

lemma twistEquivariantMap_equivariant (P : S2022PHS R l) (p₀ : P.P) (t : P.twist) :
    S2022IsEquivariant P (P.twistEquivariantMap p₀ t) := by
  intro ζ q
  show S2022Zc.smul (P.trivialize p₀ (P.smul ζ q)) (P.twistToZ p₀ t) =
    S2022Zc.smul ζ (S2022Zc.smul (P.trivialize p₀ q) (P.twistToZ p₀ t))
  rw [P.trivialize_smul, S2022Zc.smul_mul]

/-- **The torsor/twist dictionary**: equivariant maps P -> Z are the same thing as
points of the twist (P x Z)/mu_l.  This is (ii) of S2002 §5 at the pointwise level. -/
def twistEquivariantEquiv (P : S2022PHS R l) (p₀ : P.P) :
    {φ : P.P → S2022Zc R l // S2022IsEquivariant P φ} ≃ P.twist where
  toFun φ := P.twistGraph p₀ φ.1
  invFun t := ⟨P.twistEquivariantMap p₀ t, P.twistEquivariantMap_equivariant p₀ t⟩
  left_inv := by
    intro φ
    apply Subtype.ext
    funext q
    show S2022Zc.smul (P.trivialize p₀ q)
        (S2022Zc.smul (P.trivialize p₀ p₀)⁻¹ (φ.1 p₀)) = φ.1 q
    rw [P.trivialize_self, inv_one, S2022Zc.smul_one]
    have hq : q = P.smul (P.trivialize p₀ q) p₀ := (P.smul_trivialize p₀ q).symm
    calc S2022Zc.smul (P.trivialize p₀ q) (φ.1 p₀)
        = φ.1 (P.smul (P.trivialize p₀ q) p₀) := (φ.2 (P.trivialize p₀ q) p₀).symm
      _ = φ.1 q := (congrArg φ.1 hq).symm
  right_inv := by
    intro t
    induction t using Quot.ind with
    | mk a =>
      have h1 : P.twistEquivariantMap p₀ (P.twistMk a) p₀ =
          S2022Zc.smul (P.trivialize p₀ a.1)⁻¹ a.2 := by
        show S2022Zc.smul (P.trivialize p₀ p₀) (P.twistToZ p₀ (P.twistMk a)) = _
        simp only [P.trivialize_self, inv_one, S2022Zc.smul_one, P.twistToZ_mk]
      show P.twistMk (p₀, P.twistEquivariantMap p₀ (P.twistMk a) p₀) = P.twistMk a
      rw [h1]
      apply Quot.sound
      refine ⟨(P.trivialize p₀ a.1)⁻¹, ?_⟩
      apply Prod.ext
      · exact (P.smul_inv_trivialize p₀ a.1).symm
      · rfl

end S2022PHS

/-! ## 4. The comparison is fully faithful on the trivial-torsor locus -/

/-- The comparison's object-level map: a point b of Z gives the equivariant map
zeta |-> zeta . b from the trivial torsor. -/
def S2022Phi {R : Type u} [CommRing R] {l : Nat} (b : S2022Zc R l) :
    ↥(S2022Mu R l) → S2022Zc R l :=
  fun ζ => S2022Zc.smul ζ b

lemma S2022Phi_equivariant {R : Type u} [CommRing R] {l : Nat} (b : S2022Zc R l) :
    S2022IsEquivariant (S2022PHS.trivial R l) (S2022Phi b) := by
  intro ζ η
  show S2022Zc.smul (ζ * η) b = S2022Zc.smul ζ (S2022Zc.smul η b)
  rw [S2022Zc.smul_mul]

/-- **The object part of the comparison is a bijection**: the trivial-torsor objects of
[Z / mu_l] are exactly the points of Z, i.e. the objects of the root prestack. -/
def S2022PhiEquiv (R : Type u) [CommRing R] (l : Nat) :
    S2022Zc R l ≃
      {φ : ↥(S2022Mu R l) → S2022Zc R l //
        S2022IsEquivariant (S2022PHS.trivial R l) φ} where
  toFun b := ⟨S2022Phi b, S2022Phi_equivariant b⟩
  invFun φ := φ.1 1
  left_inv b := by
    show S2022Zc.smul 1 b = b
    exact S2022Zc.smul_one b
  right_inv φ := by
    apply Subtype.ext
    funext ζ
    show S2022Zc.smul ζ (φ.1 1) = φ.1 ζ
    simpa using (φ.2 ζ 1).symm

/-- The hom set of the trivial-torsor locus: right translations eta |-> eta * c of the
trivial torsor compatible with the two equivariant maps.  The compatibility is
c . y = x. -/
abbrev S2022PhiTwistHom {R : Type u} [CommRing R] {l : Nat}
    (x y : S2022Zc R l) : Type u :=
  {c : ↥(S2022Mu R l) // (c.1 : R) * y.1 = x.1}

/-- **The morphism part of the comparison is a bijection**: the twisted hom set is the
S1997 root hom, via c |-> c^{-1} (the comparison sends a root morphism zeta to the
right translation by zeta^{-1}). -/
def S2022PhiTwistHomEquiv {R : Type u} [CommRing R] {l : Nat}
    (x y : S2022Zc R l) :
    S2022PhiTwistHom x y ≃ S1997RootHom R l ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ where
  toFun c :=
    { zeta := c.1.1⁻¹
      zeta_pow := (c.1⁻¹).2
      eq := by
        have hc : (c.1.1 : R) * y.1 = x.1 := c.2
        calc y.1 = ((c.1.1⁻¹ * c.1.1 : Rˣ) : R) * y.1 := by
              rw [inv_mul_cancel, Units.val_one, one_mul]
          _ = ((c.1.1⁻¹ : Rˣ) : R) * ((c.1.1 : R) * y.1) := by
              rw [Units.val_mul]
              ring
          _ = ((c.1.1⁻¹ : Rˣ) : R) * x.1 :=
              congrArg (fun t : R => ((c.1.1⁻¹ : Rˣ) : R) * t) hc }
  invFun f :=
    ⟨⟨f.zeta, f.zeta_pow⟩⁻¹, by
      have hf : y.1 = (f.zeta : R) * x.1 := f.eq
      calc ((⟨f.zeta, f.zeta_pow⟩⁻¹ : ↥(S2022Mu R l)).1 : R) * y.1
          = ((f.zeta⁻¹ : Rˣ) : R) * y.1 := rfl
        _ = ((f.zeta⁻¹ : Rˣ) : R) * ((f.zeta : R) * x.1) :=
              congrArg (fun t : R => ((f.zeta⁻¹ : Rˣ) : R) * t) hf
        _ = ((f.zeta⁻¹ * f.zeta : Rˣ) : R) * x.1 := by
              rw [Units.val_mul]
              ring
        _ = x.1 := by
              rw [inv_mul_cancel, Units.val_one, one_mul]⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact inv_inv c.1.1
  right_inv f := by
    apply S1997RootHom.ext
    exact inv_inv f.zeta

/-- **At the origin the stabilizer is the whole group**: the twisted hom set at b = 0 is
all of mu_l.  This is the pointwise content of faithfulness at the origin (S1997's
origin_faithful) and matches the order-l automorphism S1997CyclicOriginAut. -/
def S2022PhiTwistHomZero (R : Type u) [CommRing R] {l : Nat} (h : 0 < l) :
    S2022PhiTwistHom (S2022Zc.zero R l h) (S2022Zc.zero R l h) ≃ ↥(S2022Mu R l) where
  toFun c := c.1
  invFun ζ := ⟨ζ, by rw [S2022Zc.zero]; simp⟩
  left_inv c := by apply Subtype.ext; rfl
  right_inv ζ := rfl

/-- The origin of the thickened origin, as an object of the S1997 root fibre. -/
def S2022RootObjZero (R : Type u) [CommRing R] {l : Nat} (h : 0 < l) : S1997RootObj R l :=
  ⟨0, by rw [zero_pow h.ne']⟩

/-- The endomorphisms of the origin in the S1997 root fibre are exactly the l-torsion
units: the comparison is faithful (indeed bijective on endomorphisms) at the origin. -/
def S2022RootHomZeroEquiv (R : Type u) [CommRing R] {l : Nat} (h : 0 < l) :
    ↥(S2022Mu R l) ≃ S1997RootHom R l (S2022RootObjZero R h) (S2022RootObjZero R h) :=
  (S2022PhiTwistHomZero R h).symm.trans
    (S2022PhiTwistHomEquiv (S2022Zc.zero R l h) (S2022Zc.zero R l h))

/-! ## 5. The quotient-stack package and its reductions -/

/-- **The quotient-stack package** for the l-tors root stack.

It consists of

* (i)+(iii) 'quotient': the category-valued etale stack [Z / mu_l], with its stack
  condition 'isStack';
* (iv) 'comparison': the comparison S1997RootPrestack K l -> quotient,
  b |-> (trivial torsor, zeta |-> zeta . b);
* 'fullyFaithful': the comparison is fully faithful at every test object.  For the
  actual [Z / mu_l] this is the pointwise computation of §4: on objects it is
  S2022PhiEquiv, on morphisms S2022PhiTwistHomEquiv.  It is therefore recorded here as
  the identifying property of the quotient stack, not as an extra hypothesis.

The genuinely missing input is 'quotient' together with 'isStack': the etale-local
torsor stack and its effectivity of descent (Giraud/stackification). -/
structure S2022QuotientStackPackage (K : Type u) [Field K] (l : PrimeGeFive) where
  /-- (i)+(iii): the quotient stack [Z / mu_l] as a category-valued pseudofunctor. -/
  quotient : Iut.EtaleStackPseudofunctor K
  /-- (iii): the quotient stack is a stack. -/
  isStack : quotient.IsStack (Iut.SchemeOverField.etaleTopology K)
  /-- (iv): the comparison from the root prestack (the trivial-torsor locus). -/
  comparison : Pseudofunctor.StrongTrans (S1997RootPrestack K l.value) quotient
  /-- The comparison is fully faithful at every test object. -/
  fullyFaithful : ∀ U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ,
    (comparison.app U).toFunctor.FullyFaithful

namespace S2022QuotientStackPackage

variable {K : Type u} [Field K] {l : PrimeGeFive}

/-- Faithfulness of the comparison at the origin, *derived* from full faithfulness.
This is the direction that S1997 postulated in its origin_faithful field. -/
theorem faithfulAtOrigin (D : S2022QuotientStackPackage K l) :
    S2002FaithfulAtOrigin D.quotient D.comparison := by
  intro f hf
  have hff := D.fullyFaithful (S2002CyclicPoint (K := K) (l := l))
  have hid : (D.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map
      (𝟙 (S1997CyclicOrigin K l)) =
      𝟙 ((D.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.obj
        (S1997CyclicOrigin K l)) :=
    (D.comparison.app (S2002CyclicPoint (K := K) (l := l))).toFunctor.map_id _
  exact hff.map_injective (hf.trans hid.symm)

/-- The package gives S1997's root stackification. -/
noncomputable def toRootStackification (D : S2022QuotientStackPackage K l) :
    S1997RootStackification K l where
  stack := D.quotient
  isStack := D.isStack
  comparison := D.comparison
  origin_faithful := fun f hf => D.faithfulAtOrigin f hf

/-- The package supplies S1997's missing datum. -/
theorem toRootStackificationMissing (D : S2022QuotientStackPackage K l) :
    S1997RootStackificationMissing K l :=
  ⟨D.toRootStackification⟩

/-- The package supplies S2002's existential datum. -/
theorem toS2002Datum (D : S2022QuotientStackPackage K l) :
    S2002RootStackificationDatum (K := K) (l := l) :=
  (S2002RootStackificationDatum_iff (K := K) (l := l)).mpr D.toRootStackificationMissing

/-- The package supplies S2019's corrected root stack datum. -/
noncomputable def toCorrectedDatum (D : S2022QuotientStackPackage K l) :
    S2019CorrectedRootStackDatum K l :=
  S2019CorrectedRootStackDatum.ofRecorded D.toRootStackification

/-- The quotient stack of any package carries a nontrivial order-l automorphism: its
fibres are genuinely stacky. -/
theorem stacky_point (D : S2022QuotientStackPackage K l) :
    ∃ (U : LocallyDiscrete (Iut.SchemeOverField K)ᵒᵖ) (X : D.quotient.obj U)
      (f : End X), f ≠ 1 ∧ f ^ l.value = 1 := by
  refine ⟨S2002CyclicPoint (K := K) (l := l),
    S2002WitnessImage D.toRootStackification,
    S2002WitnessAut D.toRootStackification, ?_, ?_⟩
  · exact (S2002_witness_aut D.toRootStackification).2
  · exact (S2002_witness_aut D.toRootStackification).1

/-- No package is realised by a stack with discrete fibres: the origin faithfulness is
impossible for representable/discrete stacks (S2002's no-go).  This shows that the
package is not satisfiable by the trivial or terminal stack. -/
theorem not_discreteFiber (D : S2022QuotientStackPackage K l) :
    ¬ S2002DiscreteFiber D.quotient :=
  S2002_witness_not_discreteFiber D.toRootStackification

/-- Consumer: a package over A.K yields S1994's stacky orbicurve. -/
theorem toS1994 {lg : PrimeGeFive} {A : InitialThetaArithmeticData lg}
    (D : S2022QuotientStackPackage A.K lg) :
    S1994StackyOrbicurveMissing lg A :=
  S1997FirstMissing_implies_S1994Stacky ⟨D.toRootStackification⟩

/-! ### The package against the prestack route -/

/-- If the root prestack is already a stack, it realises the package: S2019's route is
the quotient = root prestack case. -/
theorem prestack_realization (h : S2019FirstMissing (K := K) (l := l)) :
    ∃ D : S2022QuotientStackPackage K l, D.quotient = S1997RootPrestack K l.value := by
  have hst : (S1997RootPrestack K l.value).IsStack
      (Iut.SchemeOverField.etaleTopology K) :=
    (S2019FirstMissing_iff_IsStack (K := K) (l := l)).mp h
  exact ⟨
    { quotient := S1997RootPrestack K l.value
      isStack := hst
      comparison := Pseudofunctor.StrongTrans.id _
      fullyFaithful := fun U =>
        Functor.FullyFaithful.id ((S1997RootPrestack K l.value).obj U) }, rfl⟩

/-- Conversely, a package realised by the root prestack itself forces the prestack to be
a stack, i.e. exactly S2019FirstMissing. -/
theorem of_prestack (D : S2022QuotientStackPackage K l)
    (h : D.quotient = S1997RootPrestack K l.value) :
    S2019FirstMissing (K := K) (l := l) := by
  have hst : D.quotient.IsStack (Iut.SchemeOverField.etaleTopology K) := D.isStack
  rw [h] at hst
  exact (S2019FirstMissing_iff_IsStack (K := K) (l := l)).mpr hst

/-- **The package is realised by the root prestack iff the root prestack is a stack.**
Hence the quotient-stack route is exactly the prestack route plus the possibility of a
genuinely larger quotient stack; it does not require the Kummer effective-descent
statement, whose failure S2002/S2019 record. -/
theorem prestack_iff_S2019FirstMissing :
    (∃ D : S2022QuotientStackPackage K l, D.quotient = S1997RootPrestack K l.value) ↔
      S2019FirstMissing (K := K) (l := l) :=
  ⟨fun ⟨D, h⟩ => D.of_prestack h, prestack_realization⟩

end S2022QuotientStackPackage

/-! ## 6. The exact first missing -/

/-- **The exact first missing of the root-stack route**: the existence of the etale-local
quotient stack [Z / mu_l] as a genuine stack, with the comparison from the root prestack
(whose full faithfulness is proved pointwise in §4).  It is exactly S2002 §5's items
(i)+(iii); items (ii) (the twist, S2022PHS.twistEquivariantEquiv) and (iv)
(S2022PhiEquiv, S2022PhiTwistHomEquiv) are constructed in this file.

This is the Giraud/stackification input: the stack of etale-locally trivial
mu_l-torsors, and the effectivity of descent for it.  It is not the effectivity of
descent for the root prestack (prestack_iff_S2019FirstMissing), which is expected to
fail for Kummer covers.  No inhabitant is asserted here. -/
def S2022FirstMissing (K : Type u) [Field K] (l : PrimeGeFive) : Prop :=
  Nonempty (S2022QuotientStackPackage K l)

/-- The named first missing supplies S1997's root stackification. -/
theorem S2022FirstMissing_implies_S1997 (h : S2022FirstMissing K l) :
    S1997RootStackificationMissing K l := by
  obtain ⟨D⟩ := h
  exact D.toRootStackificationMissing

/-- The named first missing supplies S2002's existential form. -/
theorem S2022FirstMissing_implies_S2002 (h : S2022FirstMissing K l) :
    S2002RootStackificationDatum (K := K) (l := l) := by
  obtain ⟨D⟩ := h
  exact D.toS2002Datum

/-- The named first missing supplies S2019's corrected datum. -/
theorem S2022FirstMissing_implies_S2019Corrected (h : S2022FirstMissing K l) :
    Nonempty (S2019CorrectedRootStackDatum K l) := by
  obtain ⟨D⟩ := h
  exact ⟨D.toCorrectedDatum⟩

/-- The named first missing supplies S1994's stacky orbicurve. -/
theorem S2022FirstMissing_implies_S1994 {lg : PrimeGeFive}
    {A : InitialThetaArithmeticData lg} (h : S2022FirstMissing A.K lg) :
    S1994StackyOrbicurveMissing lg A := by
  obtain ⟨D⟩ := h
  exact D.toS1994

/-- S2019's route is the prestack case of the quotient-stack route. -/
theorem S2019FirstMissing_implies_S2022FirstMissing
    (h : S2019FirstMissing (K := K) (l := l)) : S2022FirstMissing K l := by
  obtain ⟨D, -⟩ := S2022QuotientStackPackage.prestack_realization h
  exact ⟨D⟩

/-! ## 7. Checks and axiom footprint -/

#check S2022Mu
#check S2022Mu.map
#check S2022Zc
#check S2022Zc.smul
#check S2022Zc.smul_mul
#check S2022Zhom
#check S2022ZhomGroupoid
#check S2022zhEquiv
#check S2022toRoot
#check S2022ofRoot
#check S2022ZEquivRoot
#check S2022PHS
#check S2022PHS.smul_inj
#check S2022PHS.trivialize
#check S2022PHS.trivial
#check S2022PHS.twist
#check S2022PHS.twistEquiv
#check S2022IsEquivariant
#check S2022PHS.twistEquivariantEquiv
#check S2022Phi
#check S2022PhiEquiv
#check S2022PhiTwistHom
#check S2022PhiTwistHomEquiv
#check S2022PhiTwistHomZero
#check S2022RootObjZero
#check S2022RootHomZeroEquiv
#check S2022QuotientStackPackage
#check S2022QuotientStackPackage.faithfulAtOrigin
#check S2022QuotientStackPackage.toRootStackification
#check S2022QuotientStackPackage.toRootStackificationMissing
#check S2022QuotientStackPackage.toS2002Datum
#check S2022QuotientStackPackage.toCorrectedDatum
#check S2022QuotientStackPackage.stacky_point
#check S2022QuotientStackPackage.not_discreteFiber
#check S2022QuotientStackPackage.toS1994
#check S2022QuotientStackPackage.prestack_realization
#check S2022QuotientStackPackage.of_prestack
#check S2022QuotientStackPackage.prestack_iff_S2019FirstMissing
#check S2022FirstMissing
#check S2022FirstMissing_implies_S1997
#check S2022FirstMissing_implies_S2002
#check S2022FirstMissing_implies_S2019Corrected
#check S2022FirstMissing_implies_S1994
#check S2019FirstMissing_implies_S2022FirstMissing

#print axioms S2022zhEquiv
#print axioms S2022toRoot
#print axioms S2022ZEquivRoot
#print axioms S2022PHS.smul_inj
#print axioms S2022PHS.trivialize
#print axioms S2022PHS.trivialize_smul
#print axioms S2022PHS.smul_inv_trivialize
#print axioms S2022PHS.twistToZ
#print axioms S2022PHS.twistEquiv
#print axioms S2022PHS.twistEquivariantEquiv
#print axioms S2022PhiEquiv
#print axioms S2022PhiTwistHomEquiv
#print axioms S2022PhiTwistHomZero
#print axioms S2022RootHomZeroEquiv
#print axioms S2022QuotientStackPackage.faithfulAtOrigin
#print axioms S2022QuotientStackPackage.toRootStackification
#print axioms S2022QuotientStackPackage.toRootStackificationMissing
#print axioms S2022QuotientStackPackage.toS2002Datum
#print axioms S2022QuotientStackPackage.toCorrectedDatum
#print axioms S2022QuotientStackPackage.stacky_point
#print axioms S2022QuotientStackPackage.not_discreteFiber
#print axioms S2022QuotientStackPackage.toS1994
#print axioms S2022QuotientStackPackage.prestack_realization
#print axioms S2022QuotientStackPackage.of_prestack
#print axioms S2022QuotientStackPackage.prestack_iff_S2019FirstMissing
#print axioms S2022FirstMissing_implies_S1997
#print axioms S2022FirstMissing_implies_S2002
#print axioms S2022FirstMissing_implies_S2019Corrected
#print axioms S2022FirstMissing_implies_S1994
#print axioms S2019FirstMissing_implies_S2022FirstMissing


end LeanFormal.IUT.XiFPaper.S2022QuotientStackActual
