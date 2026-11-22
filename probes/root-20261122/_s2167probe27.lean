import tmp.sheaf.xif.paper.S2132FrobCycleActual
import Mathlib.RingTheory.Frobenius
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open Polynomial
open NumberField
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual

attribute [local instance] Ideal.Quotient.field

namespace LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

noncomputable def factorDegrees {K : Type} [Field K] (f : K[X]) : Multiset Nat :=
  letI := Classical.decEq K
  (UniqueFactorizationMonoid.normalizedFactors f).map Polynomial.natDegree

def HasCycleType {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (sigma : Equiv.Perm alpha) (m : Multiset Nat) : Prop :=
  sigma.cycleType = m

noncomputable def rootPerm
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X])
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (sigma : Gal(L/K)) :
    Equiv.Perm ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L) :=
  let p : K[X] := f.map (algebraMap (RingOfIntegers K) K)
  have hmap : p.map (algebraMap K L) = f.map (algebraMap (RingOfIntegers K) L) := by
    simp only [p, Polynomial.map_map]
    rw [show (algebraMap K L).comp (algebraMap (RingOfIntegers K) K) =
        algebraMap (RingOfIntegers K) L from
      IsScalarTower.algebraMap_eq (RingOfIntegers K) K L]
  have h : (p.map (algebraMap K L)).Splits := by
    rw [hmap]
    exact hsplit
  letI : Fact ((p.map (algebraMap K L)).Splits) := ⟨h⟩
  MulAction.toPermHom (Gal(L/K)) (p.rootSet L) sigma

noncomputable def rootCycleType
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X])
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (sigma : Gal(L/K)) : Multiset Nat :=
  letI := Classical.decEq ((f.map (algebraMap (RingOfIntegers K) K)).rootSet L)
  (rootPerm K L f hsplit sigma).cycleType

def DedekindFrobeniusCycleTypeStatement
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [P.IsPrime] [P.LiesOver p]
    (hmonic : f.Monic)
    (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) : Prop :=
  let fbar : ((RingOfIntegers K) ⧸ p)[X] := f.map (Ideal.Quotient.mk p)
  ∃ sigma : Gal(L/K), IsArithFrobAt (RingOfIntegers K) sigma P ∧
    rootCycleType K L f hsplit sigma = factorDegrees fbar

def DedekindFrobeniusCycleTypeTheorem : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic)
    (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits),
    DedekindFrobeniusCycleTypeStatement K L f p P hmonic hsep hsplit

theorem S2167CorrectedProduct :
    S2132F2Z.map (Int.castRingHom (ZMod 29)) *
        S2132F10Z.map (Int.castRingHom (ZMod 29)) =
      LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z.map
        (Int.castRingHom (ZMod 29)) :=
  S2132CorrectedProduct

def S2167TenIrreducible : Prop :=
  Irreducible LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Factor10

theorem S2167TenIrreducible_proof : S2167TenIrreducible :=
  LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Factor10_irreducible

def S2167QuadraticIrreducible : Prop :=
  Irreducible (S2132F2Z.map (Int.castRingHom (ZMod 29)))

def S2167Mod29FactorizationRequired : Prop :=
  S2132F2Z.map (Int.castRingHom (ZMod 29)) *
      S2132F10Z.map (Int.castRingHom (ZMod 29)) =
    LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual.S2132Psi5Z.map
      (Int.castRingHom (ZMod 29)) ∧
  S2167QuadraticIrreducible ∧
  S2167TenIrreducible ∧
  (S2132F2Z.map (Int.castRingHom (ZMod 29))).natDegree = 2 ∧
  (S2132F10Z.map (Int.castRingHom (ZMod 29))).natDegree = 10

abbrev S2167ConcreteTarget : Prop := S2132FrobInducesPairCycleType

theorem S2167ConcreteTarget_iff :
    S2167ConcreteTarget ↔ S2132FrobInducesPairCycleType :=
  Iff.rfl

def S2167FirstMissing : Prop :=
  DedekindFrobeniusCycleTypeTheorem ∧ S2167QuadraticIrreducible

theorem S2167QuadraticIrreducible_of_firstMissing
    (h : S2167FirstMissing) : S2167QuadraticIrreducible :=
  h.2

theorem S2167DedekindFrobeniusCycleTypeTheorem_of_firstMissing
    (h : S2167FirstMissing) : DedekindFrobeniusCycleTypeTheorem :=
  h.1

#print axioms factorDegrees
#print axioms HasCycleType
#print axioms rootPerm
#print axioms rootCycleType
#print axioms DedekindFrobeniusCycleTypeStatement
#print axioms DedekindFrobeniusCycleTypeTheorem
#print axioms S2167CorrectedProduct
#print axioms S2167TenIrreducible_proof
#print axioms S2167ConcreteTarget_iff
#print axioms S2167FirstMissing

end LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

end
