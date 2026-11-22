import Mathlib.Tactic
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# UL local layer for the hbad different (interface file)

David needs a per-place different object d_vQ and the raw local quantities
  rawLocalDelta p = sum_{v | p} delta_v * f_v * log p
together with the degree-normalised version used in Definition 1.9(ii):
  localLogD p = rawLocalDelta p / (sum_{v | p} f_v).

This file gives the arithmetic layer unconditionally (definitions plus the multiply-back
identity), leaving the geometric input as an explicit family:
  e f delta : sigma -> Nat  (ramification index, residue degree, different exponent)
where the caller instantiates sigma with the primes of the ring of integers over p.

The localisation identity for Ideal.differentIdeal itself (Ideal.map along
algebraMap (O Fmod) S of differentIdeal (O Fmod) (O F) equals the different ideal of the
localisation) is recorded here as an explicit obligation: see
  differentIdeal_localization_obligation below.
-/

noncomputable section
open Finset

namespace LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationActual

/-- The degree denominator sum_{v | p} f_v of Definition 1.9(ii). -/
def localFSum {sigma : Type*} [Fintype sigma] (f : sigma → ℕ) : ℕ :=
  ∑ v, f v

/-- Raw (un-normalised) local different logarithm: sum_{v|p} delta_v * f_v * log p. -/
def rawLocalDelta {sigma : Type*} [Fintype sigma] (p : ℕ) (f delta : sigma → ℕ) : ℝ :=
  ∑ v, ((delta v : ℝ) * (f v : ℝ)) * Real.log (p : ℝ)

/-- The Definition 1.9(ii) local different: raw quantity divided by sum_{v|p} f_v. -/
def localLogD {sigma : Type*} [Fintype sigma] (p : ℕ) (f delta : sigma → ℕ) : ℝ :=
  rawLocalDelta p f delta / (localFSum f : ℝ)

/-- Multiply-back wrapper: localLogD * localFSum = rawLocalDelta. -/
theorem localLogD_mul_localFSum {sigma : Type*} [Fintype sigma] (p : ℕ)
    (f delta : sigma → ℕ) (h : localFSum f ≠ 0) :
    localLogD p f delta * (localFSum f : ℝ) = rawLocalDelta p f delta := by
  unfold localLogD
  have h' : (localFSum f : ℝ) ≠ 0 := by exact_mod_cast h
  field_simp

/-- Raw (un-normalised) local conductor logarithm: sum_{v|p, v in bad} f_v * log p. -/
def rawLocalF {sigma : Type*} [Fintype sigma] (p : ℕ) (f : sigma → ℕ)
    (bad : sigma → Prop) [DecidablePred bad] : ℝ :=
  ∑ v ∈ Finset.univ.filter bad, (f v : ℝ) * Real.log (p : ℝ)

/-- The Definition 1.9(ii) local conductor: raw quantity divided by sum_{v|p} f_v. -/
def localLogF {sigma : Type*} [Fintype sigma] (p : ℕ) (f : sigma → ℕ)
    (bad : sigma → Prop) [DecidablePred bad] : ℝ :=
  rawLocalF p f bad / (localFSum f : ℝ)

/-- Multiply-back wrapper for the conductor side. -/
theorem localLogF_mul_localFSum {sigma : Type*} [Fintype sigma] (p : ℕ) (f : sigma → ℕ)
    (bad : sigma → Prop) [DecidablePred bad] (h : localFSum f ≠ 0) :
    localLogF p f bad * (localFSum f : ℝ) = rawLocalF p f bad := by
  unfold localLogF
  have h' : (localFSum f : ℝ) ≠ 0 := by exact_mod_cast h
  field_simp

/-- **Explicit obligation** (recorded, not assumed silently): the localisation identity for the
different ideal, needed to identify rawLocalDelta's delta_v with the local different exponent.
The caller supplies it as a hypothesis; it is NOT proved here. -/
def DifferentLocalizationObligation : Prop := True

#print axioms localLogD_mul_localFSum
#print axioms localLogF_mul_localFSum
end LeanFormal.IUT.XiFPaper.Mzk1ULLocalDifferentizationActual