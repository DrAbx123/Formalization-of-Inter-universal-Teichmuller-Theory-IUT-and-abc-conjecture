import tmp.sheaf.xif.paper.S1994KSideCoversActual
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Group.TypeTags.Basic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
universe u
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
structure S1997RootObj (R : Type u) [CommRing R] (l : Nat) where
  b : R
  pow_eq_zero : b ^ l = 0
namespace S1997RootObj
variable {R : Type u} [CommRing R] {l : Nat}
@[ext] theorem ext {x y : S1997RootObj R l} (h : x.b = y.b) : x = y := by cases x; cases y; simp_all
end S1997RootObj
structure S1997RootHom (R : Type u) [CommRing R] (l : Nat) (x y : S1997RootObj R l) where
  zeta : Rˣ
  zeta_pow : ((zeta : R) ^ l = 1)
  eq : y.b = (zeta : R) * x.b
namespace S1997RootHom
variable {R : Type u} [CommRing R] {l : Nat} {x y z : S1997RootObj R l}
@[ext] theorem ext {f g : S1997RootHom R l x y} (h : f.zeta = g.zeta) : f = g := by cases f; cases g; simp_all
def id (x : S1997RootObj R l) : S1997RootHom R l x x where
  zeta := 1
  zeta_pow := by simp
  eq := by simp
def comp (f : S1997RootHom R l x y) (g : S1997RootHom R l y z) : S1997RootHom R l x z where
  zeta := f.zeta * g.zeta
  zeta_pow := by rw [Units.val_mul, mul_pow, f.zeta_pow, g.zeta_pow, one_mul]
  eq := by rw [g.eq, f.eq, Units.val_mul]; ring
end S1997RootHom
instance S1997RootCategory (R : Type u) [CommRing R] (l : Nat) : Category (S1997RootObj R l) where
  Hom x y := S1997RootHom R l x y
  id := S1997RootHom.id
  comp := S1997RootHom.comp
  id_comp f := by apply S1997RootHom.ext; ext; simp [S1997RootHom.id, S1997RootHom.comp]
  comp_id f := by apply S1997RootHom.ext; ext; simp [S1997RootHom.id, S1997RootHom.comp]
  assoc f g h := by apply S1997RootHom.ext; ext; simp [S1997RootHom.comp, mul_assoc]
noncomputable def S1997RootZetaHom {R : Type u} [CommRing R] {l : Nat} (x : S1997RootObj R l) : End x →* Rˣ where
  toFun f := f.zeta
  map_one' := by change (S1997RootHom.id x).zeta = 1; rfl
  map_mul' f g := by change (S1997RootHom.comp g f).zeta = f.zeta * g.zeta; change g.zeta * f.zeta = f.zeta * g.zeta; exact mul_comm g.zeta f.zeta
lemma S1997RootHom_pow_zeta {R : Type u} [CommRing R] {l : Nat} {x : S1997RootObj R l} (f : End x) (n : Nat) : (f ^ n).zeta = f.zeta ^ n := map_pow (S1997RootZetaHom x) f n
abbrev S1997CyclicRing (K : Type u) [Field K] (l : PrimeGeFive) : Type u := MonoidAlgebra K (Multiplicative (ZMod l.value))
noncomputable def S1997CyclicGen (K : Type u) [Field K] (l : PrimeGeFive) : S1997CyclicRing K l := MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod l.value)) (1 : K)
lemma S1997CyclicGen_pow (K : Type u) [Field K] (l : PrimeGeFive) : S1997CyclicGen K l ^ l.value = 1 := by
  rw [S1997CyclicGen, MonoidAlgebra.single_pow]
  have hindex : (Multiplicative.ofAdd (1 : ZMod l.value)) ^ l.value = 1 := by
    rw [← ofAdd_nsmul]
    rw [show (l.value • (1 : ZMod l.value)) = 0 by simp]
    exact ofAdd_zero
  have hcoef : (1 : K) ^ l.value = 1 := one_pow _
  rw [hindex, hcoef, MonoidAlgebra.one_def]
lemma S1997CyclicGen_ne_one (K : Type u) [Field K] (l : PrimeGeFive) : S1997CyclicGen K l ≠ 1 := by
  intro h
  have hc := congrArg (fun x : S1997CyclicRing K l => x.coeff (Multiplicative.ofAdd (1 : ZMod l.value))) h
  rw [S1997CyclicGen] at hc
  rw [MonoidAlgebra.coeff_single_apply] at hc
  simp only [if_pos rfl] at hc
  have hm : (Multiplicative.ofAdd (1 : ZMod l.value)) ≠ 1 := by
    intro hm
    rw [ofAdd_eq_one] at hm
    have hne : (1 : ZMod l.value) ≠ 0 := by
      intro hzero
      have hn : l.value = 1 := (ZMod.one_eq_zero_iff).mp hzero
      have h5 := l.ge_five; omega
    exact hne hm
  rw [MonoidAlgebra.one_def] at hc
  rw [MonoidAlgebra.coeff_single_apply] at hc
  have h1m : (1 : Multiplicative (ZMod l.value)) ≠ Multiplicative.ofAdd (1 : ZMod l.value) := fun h => hm h.symm
  rw [if_neg h1m] at hc
  exact one_ne_zero hc
lemma S1997CyclicGen_unit (K : Type u) [Field K] (l : PrimeGeFive) : IsUnit (S1997CyclicGen K l) := by
  apply IsUnit.of_pow_eq_one (S1997CyclicGen_pow K l)
  have h5 := l.ge_five; omega
noncomputable def S1997CyclicGenUnit (K : Type u) [Field K] (l : PrimeGeFive) : (S1997CyclicRing K l)ˣ := (S1997CyclicGen_unit K l).unit
lemma S1997CyclicGenUnit_val (K : Type u) [Field K] (l : PrimeGeFive) : ((S1997CyclicGenUnit K l : (S1997CyclicRing K l)ˣ) : S1997CyclicRing K l) = S1997CyclicGen K l := IsUnit.unit_spec _
lemma S1997CyclicGenUnit_pow (K : Type u) [Field K] (l : PrimeGeFive) : S1997CyclicGenUnit K l ^ l.value = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, S1997CyclicGenUnit_val, S1997CyclicGen_pow, Units.val_one]
noncomputable def S1997CyclicSectionsEquiv (K : Type u) [Field K] (l : PrimeGeFive) : Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤) ≃+* S1997CyclicRing K l := (Scheme.ΓSpecIso (CommRingCat.of (S1997CyclicRing K l))).commRingCatIsoToRingEquiv
noncomputable def S1997CyclicOrigin (K : Type u) [Field K] (l : PrimeGeFive) : S1997RootObj (Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤)) l.value where
  b := (S1997CyclicSectionsEquiv K l).symm 0
  pow_eq_zero := by
    change ((S1997CyclicSectionsEquiv K l).symm 0) ^ l.value = 0
    rw [← map_pow, zero_pow (by have h5 := l.ge_five; omega), map_zero]
noncomputable def S1997CyclicOriginAut (K : Type u) [Field K] (l : PrimeGeFive) : S1997RootHom (Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤)) l.value (S1997CyclicOrigin K l) (S1997CyclicOrigin K l) where
  zeta := Units.map (S1997CyclicSectionsEquiv K l).symm.toMonoidHom (S1997CyclicGenUnit K l)
  zeta_pow := by
    change ((S1997CyclicSectionsEquiv K l).symm (S1997CyclicGenUnit K l : S1997CyclicRing K l)) ^ l.value = 1
    rw [← map_pow]
    have h : (S1997CyclicGenUnit K l : S1997CyclicRing K l) ^ l.value = 1 := by
      rw [← Units.val_pow_eq_pow_val, S1997CyclicGenUnit_pow, Units.val_one]
    rw [h, map_one]
  eq := by
    change (S1997CyclicOrigin K l).b = ((S1997CyclicSectionsEquiv K l).symm (S1997CyclicGenUnit K l : S1997CyclicRing K l)) * (S1997CyclicOrigin K l).b
    rw [S1997CyclicOrigin]
    simp
noncomputable def S1997CyclicOriginAutEnd (K : Type u) [Field K] (l : PrimeGeFive) : End (S1997CyclicOrigin K l) := S1997CyclicOriginAut K l
lemma S1997CyclicOriginAut_ne_one (K : Type u) [Field K] (l : PrimeGeFive) : S1997CyclicOriginAutEnd K l ≠ 1 := by
  intro h
  have hzeta : (S1997CyclicOriginAutEnd K l).zeta = 1 := by
    have h' := congrArg S1997RootHom.zeta h
    change (S1997CyclicOriginAutEnd K l).zeta = (S1997RootHom.id (S1997CyclicOrigin K l)).zeta at h'
    simpa [S1997RootHom.id] using h'
  have hval : (S1997CyclicSectionsEquiv K l) ((Units.map (S1997CyclicSectionsEquiv K l).symm.toMonoidHom (S1997CyclicGenUnit K l) : (Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤))ˣ) : Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤)) = 1 := by
    simpa [S1997CyclicOriginAutEnd, S1997CyclicOriginAut] using congrArg (fun u : (Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤))ˣ => (S1997CyclicSectionsEquiv K l) (u : Γ(Spec (CommRingCat.of (S1997CyclicRing K l)), ⊤))) hzeta
  have hg : S1997CyclicGenUnit K l = 1 := by simpa using hval
  have hgval := congrArg (fun u : (S1997CyclicRing K l)ˣ => (u : S1997CyclicRing K l)) hg
  rw [S1997CyclicGenUnit_val] at hgval
  exact S1997CyclicGen_ne_one K l hgval
end LeanFormal.IUT.XiFPaper.S1997LTorsRootStackActual
