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

namespace LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

/-- The multiset of degrees of the irreducible factors of a polynomial. -/
noncomputable def factorDegrees {K : Type} [Field K] (f : K[X]) : Multiset Nat :=
  letI := Classical.decEq K
  (UniqueFactorizationMonoid.normalizedFactors f).map Polynomial.natDegree

/-- A permutation has cycle type m. -/
def HasCycleType {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (sigma : Equiv.Perm alpha) (m : Multiset Nat) : Prop :=
  sigma.cycleType = m

/-- The action of an F'-automorphism on the roots of an integral polynomial
in a field extension. -/
noncomputable def rootPerm
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X]) (sigma : Gal(L/K)) :
    Equiv.Perm ((f.map (algebraMap (RingOfIntegers K) L)).rootSet L) where
  toFun x := ⟨sigma x.1, Polynomial.rootSet_mapsTo (p := f.map (algebraMap (RingOfIntegers K) L))
    sigma.toAlgHom x.2⟩
  invFun x := ⟨sigma.symm x.1, Polynomial.rootSet_mapsTo (p := f.map (algebraMap (RingOfIntegers K) L))
    (K := L) sigma.symm.toAlgHom x.2⟩
  left_inv x := by apply Subtype.ext; exact sigma.symm_apply_apply x.1
  right_inv x := by apply Subtype.ext; exact sigma.apply_symm_apply x.1

/-- The cycle type of a Galois automorphism on the roots of f. -/
noncomputable def rootCycleType
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X]) (sigma : Gal(L/K)) : Multiset Nat :=
  letI := Classical.decEq ((f.map (algebraMap (RingOfIntegers K) L)).rootSet L)
  (rootPerm K L f sigma).cycleType

/-- The Dedekind--Frobenius cycle-type statement for one prime ideal: the
arithmetic Frobenius at a prime P above p realises exactly the multiset of
degrees of the irreducible factors of f modulo p. -/
def DedekindFrobeniusCycleTypeStatement
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [P.IsPrime] [P.LiesOver p]
    (hmonic : f.Monic)
    (hsep : (f.map (algebraMap (RingOfIntegers K) ((RingOfIntegers K) ⧸ p))).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits) : Prop :=
  exists sigma : Gal(L/K), IsArithFrobAt (RingOfIntegers K) sigma P /    rootCycleType K L f sigma = factorDegrees (f.map (algebraMap (RingOfIntegers K) ((RingOfIntegers K) ⧸ p)))

/-- The general Dedekind--Frobenius cycle-type theorem, in the form that the
actual arithmetic input needs.  This is the exact missing theorem: Mathlib has
arithFrobAt but no result comparing its cycle type on roots with the
factorization modulo the prime. -/
def DedekindFrobeniusCycleTypeTheorem : Prop :=
  forall (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic)
    (hsep : (f.map (algebraMap (RingOfIntegers K) ((RingOfIntegers K) ⧸ p))).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits),
    DedekindFrobeniusCycleTypeStatement K L f p P hmonic hsep hsplit

/-- The concrete target of S2132, repeated here to make the consumer explicit. -/
abbrev S2167ConcreteTarget : Prop := S2132FrobInducesPairCycleType

/-- The concrete target is exactly the S2132 statement. -/
theorem S2167ConcreteTarget_iff : S2167ConcreteTarget ↔ S2132FrobInducesPairCycleType :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

end
