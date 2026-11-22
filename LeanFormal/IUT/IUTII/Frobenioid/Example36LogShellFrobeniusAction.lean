/-
  # The actual p-power Frobenius on principal units and its log-shell action

  Task task-84 (Foundation F6d).  At the actual finite place of the concrete
  Example 3.6 carrier (the concrete place of Q(i)), this module constructs:

  1. The actual p-power Frobenius candidate on the principal units H:
     x |-> x^p, where p is the actual rational prime below the concrete place.
     It is proved to be an endomorphism of the principal-unit group H.
  2. Its action on the actual p-adic logarithm: log(x^p) = p * log(x) for
     principal units x, using the tree's actual logarithm law.
  3. The induced action on the log-shell additive image: the p-fold scaling
     x |-> p * x, proved to be an additive endomorphism of the principal-unit
     log-shell, with membership closure.
  4. Compatibility with the tree's integral log-shell and its Z_p-lattice:
     the p-fold scaling preserves the actual integral log-shell and the
     integral log-shell lattice.
  5. Nontriviality and realification: the p-fold scaling is nontrivial on the
     actual integral log-shell (it moves the unit element), and the task-21
     finite-place unit value kernel realification of an n-th power is n times
     the realification; at n = p this is the p-fold realified Frobenius action.

  The exact missing source object is frozen as SourceFrobeniusLogKummerCard:
  the source Frobenius/log-Kummer carrier with its log-Kummer map and its
  commutation with the p-fold scaling is not constructed in the tree.  No fake
  Frobenius action is substituted.  No theta-pilot/q-pilot/Tate claim is made.

  Source correspondence: IUT III, Definition 1.1 and Remark 1.2.2 (log-shell
  and Frobenius action); IUT III, Proposition 1.2; IUT IV, Proposition 1.2(i).
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36LogShellLattice
import LeanFormal.IUT.IUTII.Frobenioid.Example36PrimeStripBridge

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 800000

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace LogShellFrobeniusAction

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

local instance gaussianPolynomialIrreducibleFactLogShellFrobenius :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactLogShellFrobenius : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactLogShellFrobenius (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

noncomputable section

/-! ## 1. The p-power Frobenius on principal units H -/

/-- The actual p-power Frobenius candidate on the principal units H:
x |-> x^p, with p the actual rational prime below the concrete place. -/
noncomputable def principalUnitFrobenius :
    principalUnits (K := concreteLogShellField) →
      principalUnits (K := concreteLogShellField) :=
  fun u => u ^ concreteRationalPrime

@[simp] theorem principalUnitFrobenius_apply
    (u : principalUnits (K := concreteLogShellField)) :
    (principalUnitFrobenius u : (Integers concreteLogShellField)ˣ) =
      (u : (Integers concreteLogShellField)ˣ) ^ concreteRationalPrime :=
  rfl

/-- The p-power Frobenius is an endomorphism of the principal-unit group H. -/
noncomputable def principalUnitFrobeniusMonoidHom :
    principalUnits (K := concreteLogShellField) →*
      principalUnits (K := concreteLogShellField) where
  toFun := principalUnitFrobenius
  map_one' := by
    ext
    simp [principalUnitFrobenius]
  map_mul' := by
    intro u v
    ext
    simp [principalUnitFrobenius, mul_pow]

@[simp] theorem principalUnitFrobeniusMonoidHom_apply
    (u : principalUnits (K := concreteLogShellField)) :
    principalUnitFrobeniusMonoidHom u = principalUnitFrobenius u :=
  rfl

/-- **Log of the p-power Frobenius.**  On principal units the actual p-adic
logarithm satisfies log(x^p) = p * log(x). -/
theorem unitLog_principalUnitFrobenius_log
    (u : principalUnits (K := concreteLogShellField)) :
    unitLog (K := concreteLogShellField)
        (principalUnitFrobenius u : (Integers concreteLogShellField)ˣ) =
      (concreteRationalPrime : concreteLogShellField) *
        unitLog (K := concreteLogShellField)
          (u : (Integers concreteLogShellField)ˣ) := by
  rw [principalUnitFrobenius_apply]
  exact unitLog_pow (K := concreteLogShellField) (p := concreteRationalPrime)
    (u : (Integers concreteLogShellField)ˣ) concreteRationalPrime

/-! ## 2. The induced p-fold scaling on the log-shell additive image -/

/-- The p-fold scaling on the principal-unit log-shell, induced by the p-power
Frobenius through the p-adic logarithm: x |-> p * x. -/
noncomputable def principalUnitLogShellFrobenius :
    principalUnitLogShell →+ principalUnitLogShell where
  toFun x :=
    ⟨(concreteRationalPrime : concreteLogShellField) * (x : concreteLogShellField),
      by
        obtain ⟨u, hu⟩ :=
          (principalUnitLogShell_mem_iff (x : concreteLogShellField)).mp x.2
        refine (principalUnitLogShell_mem_iff
          ((concreteRationalPrime : concreteLogShellField) * (x : concreteLogShellField))).mpr
          ⟨principalUnitFrobenius u, ?_⟩
        rw [unitLog_principalUnitFrobenius_log, ← hu]⟩
  map_zero' := by
    ext
    simp
  map_add' := by
    intro x y
    ext
    simp [mul_add]

@[simp] theorem principalUnitLogShellFrobenius_apply
    (x : principalUnitLogShell) :
    (principalUnitLogShellFrobenius x : concreteLogShellField) =
      (concreteRationalPrime : concreteLogShellField) * (x : concreteLogShellField) :=
  rfl

/-- The p-fold scaling preserves the principal-unit log-shell. -/
theorem principalUnitLogShell_p_mul_mem
    {x : concreteLogShellField} (hx : x ∈ principalUnitLogShell) :
    (concreteRationalPrime : concreteLogShellField) * x ∈ principalUnitLogShell :=
  (principalUnitLogShellFrobenius ⟨x, hx⟩).2

/-- The p-fold scaling on the principal-unit log-shell implements exactly the
p-power Frobenius on principal units. -/
theorem principalUnitLogShellFrobenius_mk
    (u : principalUnits (K := concreteLogShellField)) :
    principalUnitLogShellFrobenius
        ⟨unitLog (K := concreteLogShellField)
            (u : (Integers concreteLogShellField)ˣ),
          (principalUnitLogShell_mem_iff _).mpr ⟨u, rfl⟩⟩ =
      ⟨unitLog (K := concreteLogShellField)
          (principalUnitFrobenius u : (Integers concreteLogShellField)ˣ),
        (principalUnitLogShell_mem_iff _).mpr ⟨principalUnitFrobenius u, rfl⟩⟩ := by
  apply Subtype.ext
  simp only [principalUnitLogShellFrobenius_apply]
  rw [unitLog_principalUnitFrobenius_log]

/-! ## 3. Compatibility with the integral log-shell and its lattice -/

/-- The p-fold scaling preserves the actual integral log-shell. -/
theorem integralLogShell_p_mul_mem
    {x : concreteLogShellField}
    (hx : x ∈ integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime)) :
    (concreteRationalPrime : concreteLogShellField) * x ∈
      integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) := by
  have hscalar := integralLogShell_padicInt_mul_mem (K := concreteLogShellField)
    (p := concreteRationalPrime)
    (z := (concreteRationalPrime : ℤ_[concreteRationalPrime])) hx
  simpa only [PadicInt.coe_natCast, map_natCast] using hscalar

/-- The p-fold scaling preserves the actual integral log-shell lattice. -/
theorem integralLogShellLattice_p_smul_mem
    (x : concreteLogShellField)
    (hx : x ∈ integralLogShellLattice (K := concreteLogShellField)
      (p := concreteRationalPrime)) :
    (concreteRationalPrime : ℤ_[concreteRationalPrime]) • x ∈
      integralLogShellLattice (K := concreteLogShellField) (p := concreteRationalPrime) :=
  Submodule.smul_mem _ _ hx

/-- The p-fold scaling is nontrivial on the actual integral log-shell: it moves
the unit element. -/
theorem integralLogShell_p_scaling_nontrivial :
    ∃ x : concreteLogShellField,
      x ∈ integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) ∧
        (concreteRationalPrime : concreteLogShellField) * x ≠ x := by
  refine ⟨1, ?_, ?_⟩
  · exact integers_subset_integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime)
      ((mem_integers_iff (1 : concreteLogShellField)).mpr (by simp))
  · rw [mul_one]
    exact_mod_cast (Fact.out : concreteRationalPrime.Prime).ne_one

/-! ## 4. Degree and realification of the p-power Frobenius -/

/-- The task-21 finite-place unit value kernel realification of an n-th power is
n times the realification: this is the realified Frobenius power action. -/
theorem concretePlace_unitValueKernel_realification_pow
    (x : finitePlaceUnitValueMonoid (F := GaussianField) concreteHeightOneSpectrum)
    (n : ℕ) :
    (finitePlaceUnitValueKernel (F := GaussianField)
        concreteHeightOneSpectrum).realification (x ^ n) =
      (n : ℝ) *
        (finitePlaceUnitValueKernel (F := GaussianField)
          concreteHeightOneSpectrum).realification x :=
  finitePlaceUnitValueKernel_realification_pow (F := GaussianField)
    concreteHeightOneSpectrum x n

/-- The realified p-power Frobenius action at the concrete place. -/
theorem concretePlace_unitValueKernel_realification_frobenius
    (x : finitePlaceUnitValueMonoid (F := GaussianField) concreteHeightOneSpectrum) :
    (finitePlaceUnitValueKernel (F := GaussianField)
        concreteHeightOneSpectrum).realification (x ^ concreteRationalPrime) =
      (concreteRationalPrime : ℝ) *
        (finitePlaceUnitValueKernel (F := GaussianField)
          concreteHeightOneSpectrum).realification x :=
  concretePlace_unitValueKernel_realification_pow x concreteRationalPrime

/-! ## 5. The frozen source Frobenius/log-Kummer card -/

/-- **Frozen card for the missing source Frobenius/log-Kummer carrier.**  The
tree constructs the actual p-power map on the principal units of the concrete
completion, the induced p-fold scaling on the actual log-shell and its
compatibility with the integral log-shell and lattice.  The source's Frobenius
action together with its log-Kummer operator, and the identification of the
tree's p-power/ldquo p-fold scaling with that source operator, are not
constructed in the tree.  The card records the shape of the missing data: a
source principal-unit carrier with its Frobenius, a source log-shell with its
p-fold scaling, a log-Kummer map between them, commutation of the log-Kummer map
with Frobenius/scaling, and nontriviality of the scaling.  No inhabitant is
constructed in this file and no theorem consumes one; in particular no fake
Frobenius or log-Kummer action is substituted. -/
structure SourceFrobeniusLogKummerCard (l : PrimeGeFive) where
  /-- The source principal-unit carrier H. -/
  sourcePrincipalUnits : Type
  /-- The source Frobenius map on H. -/
  sourceFrobenius : sourcePrincipalUnits → sourcePrincipalUnits
  /-- The source log-shell carrier. -/
  sourceLogShell : Type
  /-- The source log-Kummer map from H to the log-shell. -/
  logKummer : sourcePrincipalUnits → sourceLogShell
  /-- The p-fold scaling on the source log-shell. -/
  pScaling : sourceLogShell → sourceLogShell
  /-- The log-Kummer map commutes with Frobenius and the p-fold scaling. -/
  logKummer_frobenius : ∀ h : sourcePrincipalUnits,
    logKummer (sourceFrobenius h) = pScaling (logKummer h)
  /-- The p-fold scaling is genuinely nontrivial. -/
  pScaling_nontrivial : ∃ x : sourceLogShell, pScaling x ≠ x

/-! ## 6. Summary -/

/-- **Summary of the actual p-power Frobenius and its log-shell action.**
The p-power map is an endomorphism of the actual principal units H; its
p-adic logarithm is p times the logarithm; it induces a p-fold scaling
endomorphism of the principal-unit log-shell, preserving the integral
log-shell and its Z_p-lattice; the scaling is nontrivial on the integral
log-shell; and the realified task-21 Frobenius power action is n times the
realification (in particular p times for the p-power Frobenius).  The source
Frobenius/log-Kummer carrier is frozen as a card. -/
theorem example36LogShellFrobeniusAction_summary :
    (∀ u : principalUnits (K := concreteLogShellField),
      (principalUnitFrobeniusMonoidHom u : (Integers concreteLogShellField)ˣ) =
        (u : (Integers concreteLogShellField)ˣ) ^ concreteRationalPrime) ∧
    (∀ u : principalUnits (K := concreteLogShellField),
      unitLog (K := concreteLogShellField)
          (principalUnitFrobenius u : (Integers concreteLogShellField)ˣ) =
        (concreteRationalPrime : concreteLogShellField) *
          unitLog (K := concreteLogShellField)
            (u : (Integers concreteLogShellField)ˣ)) ∧
    (∀ x : principalUnitLogShell,
      (principalUnitLogShellFrobenius x : concreteLogShellField) =
        (concreteRationalPrime : concreteLogShellField) *
          (x : concreteLogShellField)) ∧
    (∀ x : concreteLogShellField,
      x ∈ integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) →
        (concreteRationalPrime : concreteLogShellField) * x ∈
          integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)) ∧
    (∃ x : concreteLogShellField,
      x ∈ integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) ∧
        (concreteRationalPrime : concreteLogShellField) * x ≠ x) ∧
    (∀ (x : finitePlaceUnitValueMonoid (F := GaussianField) concreteHeightOneSpectrum)
      (n : ℕ),
      (finitePlaceUnitValueKernel (F := GaussianField)
          concreteHeightOneSpectrum).realification (x ^ n) =
        (n : ℝ) *
          (finitePlaceUnitValueKernel (F := GaussianField)
            concreteHeightOneSpectrum).realification x) :=
  ⟨fun u => rfl,
    fun u => unitLog_principalUnitFrobenius_log u,
    fun x => principalUnitLogShellFrobenius_apply x,
    fun x hx => integralLogShell_p_mul_mem hx,
    integralLogShell_p_scaling_nontrivial,
    fun x n => concretePlace_unitValueKernel_realification_pow x n⟩

end

end LogShellFrobeniusAction
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the actual p-power Frobenius on principal units and its
action on the local log-shell at the concrete Gaussian place.  The p-power map
is an endomorphism of the actual principal units; log(x^p) = p log(x); the
induced map on the principal-unit log-shell is p-fold scaling, preserving the
integral log-shell and its lattice; the scaling is nontrivial on the integral
log-shell; the task-21 realified Frobenius power action is n times the
realification; the source Frobenius/log-Kummer carrier is frozen as
SourceFrobeniusLogKummerCard.  No fake Frobenius or log-Kummer action is
claimed. -/
def example36LogShellFrobeniusAction : Obligation :=
  { id := "IUT-II.example36-log-shell-frobenius-action"
    source :=
      "IUT III, Definition 1.1 and Remark 1.2.2 (log-shell and Frobenius " ++
        "action); IUT III, Proposition 1.2; IUT IV, Proposition 1.2(i)"
    status := VerificationStatus.interface
    note :=
      "At the actual finite place of the concrete Example 3.6 carrier: the " ++
        "p-power Frobenius candidate x |-> x^p on the actual principal units H " ++
        "of the concrete completion is an endomorphism of H " ++
        "(principalUnitFrobenius, principalUnitFrobeniusMonoidHom).  The actual " ++
        "p-adic logarithm satisfies log(x^p) = p * log(x) " ++
        "(unitLog_principalUnitFrobenius_log).  The induced action on the " ++
        "principal-unit log-shell is p-fold scaling x |-> p * x " ++
        "(principalUnitLogShellFrobenius, principalUnitLogShellFrobenius_apply, " ++
        "principalUnitLogShellFrobenius_mk), with membership closure " ++
        "(principalUnitLogShell_p_mul_mem).  Compatibility with the tree's " ++
        "integral log-shell and lattice: p-fold scaling preserves the actual " ++
        "integral log-shell (integralLogShell_p_mul_mem) and the integral " ++
        "log-shell lattice (integralLogShellLattice_p_smul_le).  Nontriviality: " ++
        "the p-fold scaling moves the unit element in the integral log-shell " ++
        "(integralLogShell_p_scaling_nontrivial).  Degree/realification: the " ++
        "task-21 finite-place unit value kernel realification of an n-th power " ++
        "is n times the realification (concretePlace_unitValueKernel_realification_pow), " ++
        "in particular p times for the p-power Frobenius " ++
        "(concretePlace_unitValueKernel_realification_frobenius).  NOT " ++
        "provided: the source Frobenius action together with its log-Kummer " ++
        "operator and the identification of the tree's p-power/p-fold scaling " ++
        "with that source operator; frozen as SourceFrobeniusLogKummerCard with " ++
        "no inhabitant and no substitution.  No theta-pilot/q-pilot/Tate claim."
    dependsOn :=
      [ "IUT-II.example36-log-shell-lattice",
        "IUT-II.example36-prime-strip-bridge",
        "IUT-III.local-log-shell-frobenius-action",
        "IUT-III.log-shell-index-arithmetic" ] }

end LeanFormal.IUT.Audit
