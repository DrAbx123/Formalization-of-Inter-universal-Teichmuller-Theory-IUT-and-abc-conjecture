import tmp.sheaf.xif.paper.S2801D6FaithfulActual
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveProjectiveClosureDirectGlue

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure

open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual

universe u

variable (K : Type u) [Field K]

/-- E37 homogeneous equation X^3 - X Z^2 - Y^2 Z - Y Z^2. -/
def E37Homogeneous : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 0 ^ 3 - MvPolynomial.X 0 * MvPolynomial.X 2 ^ 2 -
    MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 - MvPolynomial.X 1 * MvPolynomial.X 2 ^ 2

/-- Chart Z != 0 substitution X=x, Y=y, Z=1. -/
def E37ChartZSubstitution : Fin 3 → MvPolynomial (Fin 2) K
  | ⟨0, _⟩ => MvPolynomial.X 0
  | ⟨1, _⟩ => MvPolynomial.X 1
  | ⟨2, _⟩ => 1
  | ⟨n + 3, h⟩ => absurd h (by omega)

theorem E37_chartZ :
    MvPolynomial.aeval (E37ChartZSubstitution K) (E37Homogeneous K) =
      -(S2801E37Polynomial K) := by
  simp [E37Homogeneous, S2801E37Polynomial, weierstrassAffinePolynomial,
    S2801E37Curve, E37ChartZSubstitution]
  ring

/-- Chart Y != 0 substitution X=s, Y=1, Z=t. -/
def E37ChartYSubstitution : Fin 3 → MvPolynomial (Fin 2) K
  | ⟨0, _⟩ => MvPolynomial.X 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => MvPolynomial.X 1
  | ⟨n + 3, h⟩ => absurd h (by omega)

/-- Chart Y equation s^3 - s t^2 - t - t^2. -/
def E37ChartYPolynomial : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 3 - MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 -
    MvPolynomial.X 1 - MvPolynomial.X 1 ^ 2

theorem E37_chartY :
    MvPolynomial.aeval (E37ChartYSubstitution K) (E37Homogeneous K) =
      E37ChartYPolynomial K := by
  simp [E37Homogeneous, E37ChartYPolynomial, E37ChartYSubstitution]

def E37ChartYIdeal : Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span {E37ChartYPolynomial K}

abbrev E37ChartYRing : Type u :=
  MvPolynomial (Fin 2) K ⧸ E37ChartYIdeal K

abbrev E37ChartYScheme : Scheme :=
  Spec (CommRingCat.of (E37ChartYRing K))

def E37ChartYStructureMap :
    E37ChartYScheme K ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (E37ChartYRing K)))

abbrev E37ChartYAsOver : Over (Spec (CommRingCat.of K)) :=
  Over.mk (E37ChartYStructureMap K)

/-- Evaluation at (s,t) = (0,0) on the chart-Y polynomial ring. -/
abbrev E37InfinityPolynomialEval : MvPolynomial (Fin 2) K →+* K :=
  MvPolynomial.eval (fun _ : Fin 2 => (0 : K))

theorem E37InfinityPolynomialEval_vanishes :
    E37InfinityPolynomialEval K (E37ChartYPolynomial K) = 0 := by
  simp [E37InfinityPolynomialEval, E37ChartYPolynomial]

abbrev E37InfinityEval : E37ChartYRing K →+* K :=
  Ideal.Quotient.lift (E37ChartYIdeal K) (E37InfinityPolynomialEval K) (by
    intro a ha
    have hle : E37ChartYIdeal K ≤ RingHom.ker (E37InfinityPolynomialEval K) := by
      rw [E37ChartYIdeal, Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      change E37InfinityPolynomialEval K (E37ChartYPolynomial K) = 0
      exact E37InfinityPolynomialEval_vanishes K
    exact hle ha)

theorem E37InfinityEval_surjective : Function.Surjective (E37InfinityEval K) := by
  intro y
  refine ⟨Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.C y), ?_⟩
  rw [E37InfinityEval, Ideal.Quotient.lift_mk]
  simp [E37InfinityPolynomialEval]

abbrev E37InfinityIdeal : Ideal (E37ChartYRing K) :=
  RingHom.ker (E37InfinityEval K)

noncomputable instance E37InfinityIdeal_isMaximal :
    (E37InfinityIdeal K).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (E37InfinityEval K)
    (E37InfinityEval_surjective K)

abbrev E37InfinityPoint : E37ChartYScheme K :=
  ⟨E37InfinityIdeal K, (E37InfinityIdeal_isMaximal K).isPrime⟩

/-- Overlap Z != 0, Y != 0 on the affine chart: localization away from y. -/
abbrev E37ChartZOverlapRing : Type u :=
  Localization.Away (S2801E37Y K)

abbrev E37ChartZOverlap : Scheme :=
  Spec (CommRingCat.of (E37ChartZOverlapRing K))

def E37ChartZOverlapMap :
    E37ChartZOverlap K ⟶ S2801E37AffineScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (S2801E37CoordinateRing K)
    (E37ChartZOverlapRing K)))

/-- Overlap Z != 0, Y != 0 on the chart Y: localization away from t. -/
abbrev E37ChartYOverlapRing : Type u :=
  Localization.Away (Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.X 1))

abbrev E37ChartYOverlap : Scheme :=
  Spec (CommRingCat.of (E37ChartYOverlapRing K))

def E37ChartYOverlapMap : E37ChartYOverlap K ⟶ E37ChartYScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap (E37ChartYRing K)
    (E37ChartYOverlapRing K)))

local instance chartZOverlap_isOpenImmersion :
    IsOpenImmersion (E37ChartZOverlapMap K) :=
  AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway
    (R := CommRingCat.of (S2801E37CoordinateRing K)) (S2801E37Y K)

local instance chartYOverlap_isOpenImmersion :
    IsOpenImmersion (E37ChartYOverlapMap K) :=
  AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway
    (R := CommRingCat.of (E37ChartYRing K)) (Ideal.Quotient.mk (E37ChartYIdeal K) (MvPolynomial.X 1))

local instance chartZOverlap_mono : Mono (E37ChartZOverlapMap K) :=
  IsOpenImmersion.mono (E37ChartZOverlapMap K)

local instance chartYOverlap_mono : Mono (E37ChartYOverlapMap K) :=
  IsOpenImmersion.mono (E37ChartYOverlapMap K)

#check E37Homogeneous
#check E37_chartZ
#check E37_chartY
#check E37ChartYScheme
#check E37InfinityPoint
#check E37ChartZOverlapMap
#check E37ChartYOverlapMap
#print axioms E37_chartY


noncomputable abbrev E37ProjU (K : Type u) [Field K] : Bool → Scheme.{u}
  | false => S2801E37AffineScheme K
  | true => E37ChartYScheme K

noncomputable abbrev E37ProjV (K : Type u) [Field K] : Bool × Bool → Scheme.{u}
  | (false, false) => S2801E37AffineScheme K
  | (false, true) => E37ChartZOverlap K
  | (true, false) => E37ChartYOverlap K
  | (true, true) => E37ChartYScheme K

noncomputable abbrev E37ProjF (K : Type u) [Field K] :
    (i j : Bool) → E37ProjV K (i, j) ⟶ E37ProjU K i
  | false, false => 𝟙 (S2801E37AffineScheme K)
  | false, true => E37ChartZOverlapMap K
  | true, false => E37ChartYOverlapMap K
  | true, true => 𝟙 (E37ChartYScheme K)

noncomputable abbrev E37ProjT (K : Type u) [Field K]
    (e : E37ChartZOverlap K ≅ E37ChartYOverlap K) :
    (i j : Bool) → E37ProjV K (i, j) ⟶ E37ProjV K (j, i)
  | false, false => 𝟙 (S2801E37AffineScheme K)
  | false, true => e.hom
  | true, false => e.inv
  | true, true => 𝟙 (E37ChartYScheme K)

noncomputable abbrev E37ProjJ : Type u := ULift.{u} Bool

noncomputable def E37ProjTPrime (K : Type u) [Field K]
    (e : E37ChartZOverlap K ≅ E37ChartYOverlap K) (i j k : Bool) :
    pullback (E37ProjF K i j) (E37ProjF K i k) ⟶
      pullback (E37ProjF K j k) (E37ProjF K j i) := by
  haveI hft : Mono (E37ProjF K false true) := by
    dsimp [E37ProjF]
    exact IsOpenImmersion.mono (E37ProjF K false true)
  haveI htf : Mono (E37ProjF K true false) := by
    dsimp [E37ProjF]
    exact IsOpenImmersion.mono (E37ProjF K true false)
  cases i <;> cases j <;> cases k
  · exact 𝟙 _
  · exact (pullbackSymmetry _ _).hom
  · exact pullback.fst _ _ ≫ E37ProjT K e false true ≫ inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ E37ProjT K e false true ≫ inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ E37ProjT K e true false ≫ inv (pullback.snd _ _)
  · exact pullback.fst _ _ ≫ E37ProjT K e true false ≫ inv (pullback.snd _ _)
  · exact (pullbackSymmetry _ _).hom
  · exact 𝟙 _

noncomputable abbrev E37ProjGlueData (K : Type u) [Field K]
    (e : E37ChartZOverlap K ≅ E37ChartYOverlap K) : Scheme.GlueData.{u} where
  toGlueData :=
    { J := E37ProjJ
      U := fun i => E37ProjU K i.down
      V := fun p => E37ProjV K (p.1.down, p.2.down)
      f := fun i j => E37ProjF K i.down j.down
      f_mono i j := by
        dsimp only [E37ProjF]
        cases i.down <;> cases j.down <;> infer_instance
      f_hasPullback i j k := by
        dsimp only [E37ProjF]
        cases i.down <;> cases j.down <;> cases k.down <;> infer_instance
      f_id i := by
        dsimp only [E37ProjF]
        cases i.down <;> infer_instance
      t := fun i j => E37ProjT K e i.down j.down
      t_id i := by
        cases i with
        | up i => cases i <;> rfl
      t' i j k := E37ProjTPrime K e i.down j.down k.down
      t_fac i j k := by
        cases i with
        | up i => cases j with
          | up j => cases k with
            | up k =>
              cases i <;> cases j <;> cases k <;>
              simp [E37ProjTPrime, E37ProjT, E37ProjF, E37ProjU, E37ProjV,
                fst_eq_snd_of_mono_eq, pullback.condition,
                pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst,
                Category.comp_id, Category.id_comp, Category.assoc]
      cocycle i j k := by
        cases i with
        | up i => cases j with
          | up j => cases k with
            | up k =>
              cases i <;> cases j <;> cases k <;>
              (apply pullback.hom_ext <;>
                simp [E37ProjTPrime, E37ProjT, E37ProjF, E37ProjU, E37ProjV,
                  pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_snd,
                  pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd,
                  pullback.lift_fst, pullback.lift_snd,
                  fst_eq_snd_of_mono_eq, pullback.condition,
                  Category.comp_id, Category.id_comp, Category.assoc]) }
  f_open i j := by
    dsimp only [E37ProjF]
    cases i.down <;> cases j.down <;> infer_instance

noncomputable abbrev E37ProjGluedScheme (K : Type u) [Field K]
    (e : E37ChartZOverlap K ≅ E37ChartYOverlap K) : Scheme.{u} :=
  (E37ProjGlueData K e).glued

noncomputable abbrev E37ProjChartZMap (K : Type u) [Field K]
    (e : E37ChartZOverlap K ≅ E37ChartYOverlap K) :
    S2801E37AffineScheme K ⟶ E37ProjGluedScheme K e :=
  (E37ProjGlueData K e).ι (ULift.up false)

noncomputable abbrev E37ProjChartYMap (K : Type u) [Field K]
    (e : E37ChartZOverlap K ≅ E37ChartYOverlap K) :
    E37ChartYScheme K ⟶ E37ProjGluedScheme K e :=
  (E37ProjGlueData K e).ι (ULift.up true)

noncomputable abbrev E37ProjPointAtInfinity (K : Type u) [Field K]
    (e : E37ChartZOverlap K ≅ E37ChartYOverlap K) :
    E37ProjGluedScheme K e :=
  E37ProjChartYMap K e (E37InfinityPoint K)

#check E37ProjGlueData
#check E37ProjGluedScheme
#check E37ProjChartZMap
#check E37ProjChartYMap
#check E37ProjPointAtInfinity
#print axioms E37ProjGlueData

end LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
end
