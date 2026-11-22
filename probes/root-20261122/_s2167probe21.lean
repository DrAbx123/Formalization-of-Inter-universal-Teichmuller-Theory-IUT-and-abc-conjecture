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
    (f : (RingOfIntegers K)[X]) (sigma : Gal(L/K)) :
    Equiv.Perm ((f.map (algebraMap (RingOfIntegers K) L)).rootSet L) where
  toFun x := ⟨sigma x.1, Polynomial.rootSet_mapsTo (p := f.map (algebraMap (RingOfIntegers K) L))
    (T := RingOfIntegers K) (S := L) (S' := L)
    (sigma.toAlgHom.restrictScalars (RingOfIntegers K)) x.2⟩
  invFun x := ⟨sigma.symm x.1, Polynomial.rootSet_mapsTo (p := f.map (algebraMap (RingOfIntegers K) L))
    (T := RingOfIntegers K) (S := L) (S' := L)
    (sigma.symm.toAlgHom.restrictScalars (RingOfIntegers K)) x.2⟩
  left_inv x := by apply Subtype.ext; exact sigma.symm_apply_apply x.1
  right_inv x := by apply Subtype.ext; exact sigma.apply_symm_apply x.1

noncomputable def rootCycleType
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X]) (sigma : Gal(L/K)) : Multiset Nat :=
  letI := Classical.decEq ((f.map (algebraMap (RingOfIntegers K) L)).rootSet L)
  (rootPerm K L f sigma).cycleType

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
    rootCycleType K L f sigma = factorDegrees fbar

def DedekindFrobeniusCycleTypeTheorem : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic)
    (hsep : (f.map (Ideal.Quotient.mk p)).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits),
    DedekindFrobeniusCycleTypeStatement K L f p P hmonic hsep hsplit

abbrev S2167ConcreteTarget : Prop := S2132FrobInducesPairCycleType

theorem S2167ConcreteTarget_iff : S2167ConcreteTarget ↔ S2132FrobInducesPairCycleType :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

end
