import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Frobenius
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
open Polynomial NumberField
attribute [local instance] Ideal.Quotient.field
namespace LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
noncomputable def factorDegrees {K : Type*} [Field K] (f : K[X]) : Multiset Nat :=
  letI := Classical.decEq K
  (UniqueFactorizationMonoid.normalizedFactors f).map Polynomial.natDegree
/-- Localized reduction at an ideal. -/
def fbarAt {R : Type*} [CommRing R] (f : R[X]) (p : Ideal R) : (R ⧸ p)[X] :=
  f.map (Ideal.Quotient.mk p)
/-- The root permutation of a Galois automorphism acting on the roots of a
polynomial over a base ring R (through K). -/
noncomputable def rootPermR
    (R K L : Type*) [CommRing R] [Field K] [Field L]
    [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (f : R[X]) (hsplit : (f.map (algebraMap R L)).Splits) (sigma : Gal(L/K)) :
    Equiv.Perm ((f.map (algebraMap R K)).rootSet L) :=
  let p : K[X] := f.map (algebraMap R K)
  have hmap : p.map (algebraMap K L) = f.map (algebraMap R L) := by
    simp only [p, Polynomial.map_map]
    rw [IsScalarTower.algebraMap_eq R K L]
  have h : (p.map (algebraMap K L)).Splits := by
    rw [hmap]; exact hsplit
  letI : Fact ((p.map (algebraMap K L)).Splits) := ⟨h⟩
  MulAction.toPermHom (Gal(L/K)) (p.rootSet L) sigma
/-- The localized orbit-size Dedekind--Frobenius statement. -/
def LocalizedDedekindFrobeniusOrbitSizeStatement
    (R K L : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field K] [Field L] [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsFractionRing R K] [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L]
    [Algebra R (RingOfIntegers L)] [MulSemiringAction Gal(L/K) (RingOfIntegers L)] [SMulCommClass Gal(L/K) R (RingOfIntegers L)]
    (f : R[X]) (p : Ideal R) [p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [P.IsPrime] [P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbarAt f p).Separable)
    (hsplit : (f.map (algebraMap R L)).Splits) : Prop :=
  ∃ sigma : Gal(L/K), IsArithFrobAt R sigma P ∧
    orbitSizeMultiset (rootPermR R K L f hsplit sigma) = factorDegrees (fbarAt f p)
/-- The localized theorem, universally quantified. -/
def LocalizedDedekindFrobeniusOrbitSizeTheorem : Prop :=
  ∀ (R K L : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    [Field K] [Field L] [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsFractionRing R K] [NumberField K] [NumberField L]
    [FiniteDimensional K L] [IsGalois K L]
    [Algebra R (RingOfIntegers L)] [MulSemiringAction Gal(L/K) (RingOfIntegers L)] [SMulCommClass Gal(L/K) R (RingOfIntegers L)]
    (f : R[X]) (p : Ideal R) [p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [P.IsPrime] [P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbarAt f p).Separable)
    (hsplit : (f.map (algebraMap R L)).Splits),
    LocalizedDedekindFrobeniusOrbitSizeStatement R K L f p P hmonic hsep hsplit
#check LocalizedDedekindFrobeniusOrbitSizeTheorem
end LeanFormal.IUT.XiFPaper.S2532LocalizedDefinitionsActual
end
