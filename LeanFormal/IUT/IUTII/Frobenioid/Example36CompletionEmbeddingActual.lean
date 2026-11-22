import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIntoAlgCl
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Actual completion embedding into PadicAlgCl via the existing p-adic scalar structure

Foundation F6 continuation.  The tree already carries the p-adic scalar structure of
the actual finite-place completion: in
ABCBridge.Geometry.FinitePlacePadicScalarStructure, for every
NumberField.FinitePlace place the completion K_v = Completion place is an algebra
over the p-adic field PadicScalarField place = Q_[(completionRationalPrime place).val],
with Module.Finite (moduleFinite_padicCompletionAlgebra) and continuous scalar
action; FinitePlaceNormalizedCompletion adds a normalized normed-field structure.
This module transports those instances to the actual completion used by
Example36 (v.adicCompletion F, bridged by NumberField.FinitePlace.mk), derives
Algebra.IsAlgebraic and Module.IsTorsionFree, and thereby discharges the
typeclass conditional of Example36CompletionIntoAlgCl: the actual injective
field and unit embedding of the completion into PadicAlgCl p is obtained
unconditionally.

## What is actual here

* Algebra, Module.Finite, Algebra.IsAlgebraic and Module.IsTorsionFree for the
  actual completion over its p-adic scalar field (the last two derived here);
undefined
  PadicAlgCl p (unconditional, via Example36CompletionIntoAlgCl), stated at the
  actual completion type Completion place (definitionally the adic completion at
  underlyingPrime place) and at the concrete place
  (NumberField.FinitePlace.mk v).maximalIdeal; the place-level bridge
  completion_eq_adicCompletion records the identification of the places with v;
* an actual injective map on units K_v^x -> (PadicAlgCl p)^x;
* the reduction of the normalized-value compatibility to the explicit
  log-norm identity, and the (1/e)Z lattice / O_v^x kernel consequences under
  that identity.

## What remains (card)

The missing analytic input is the normalized norm/valuation comparison: the
log-norm identity
Real.log ||image unit|| = -(completionValuationExponent v x / e) * Real.log p
for the actual embedding, equivalently that the normalized completion norm is
p^(-nu/e) and that the p-adic algebra embedding is isometric for the spectral
norms.  That comparison is not in the tree; it is frozen in the card.  The
remaining source components (rho_v normalization isomorphism, log-shell,
Frobenius/log-Kummer) are unchanged.  No source-faithfulness claim, no theta,
q-pilot or Tate claim.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The actual p-adic scalar structure on the completion -/

/-- The actual rational prime under a finite place. -/
abbrev completionPadicPrime (place : NumberField.FinitePlace F) : Nat :=
  (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).val

/-- Its primality, as an instance for the PadicAlgCl parameter. -/
instance completionPadicPrime_fact (place : NumberField.FinitePlace F) :
    Fact (Nat.Prime (completionPadicPrime place)) :=
  LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime_fact place

/-- The actual completion has the p-adic scalar field as an algebra base. -/
noncomputable instance completionAlgebraPadic (place : NumberField.FinitePlace F) :
    Algebra ℚ_[completionPadicPrime place]
      (LeanFormal.IUT.NumberFieldFinitePlace.Completion place) :=
  LeanFormal.IUT.NumberFieldFinitePlace.padicCompletionAlgebra place

/-- The actual completion is a finite module over its p-adic scalar field. -/
noncomputable instance completionFinitePadic (place : NumberField.FinitePlace F) :
    letI := completionAlgebraPadic place
    Module.Finite ℚ_[completionPadicPrime place]
      (LeanFormal.IUT.NumberFieldFinitePlace.Completion place) :=
  LeanFormal.IUT.NumberFieldFinitePlace.moduleFinite_padicCompletionAlgebra place

/-- **The actual completion is algebraic over its p-adic scalar field**, derived
from the finite module structure. -/
theorem completionAlgebraIsAlgebraic (place : NumberField.FinitePlace F) :
    letI := completionAlgebraPadic place
    Algebra.IsAlgebraic ℚ_[completionPadicPrime place]
      (LeanFormal.IUT.NumberFieldFinitePlace.Completion place) := by
  letI := completionAlgebraPadic place
  letI := completionFinitePadic place
  exact Algebra.IsAlgebraic.of_finite ℚ_[completionPadicPrime place]
    (LeanFormal.IUT.NumberFieldFinitePlace.Completion place)

/-- **The actual completion is torsion-free over its p-adic scalar field.** -/
theorem completionModuleIsTorsionFree (place : NumberField.FinitePlace F) :
    letI := completionAlgebraPadic place
    Module.IsTorsionFree ℚ_[completionPadicPrime place]
      (LeanFormal.IUT.NumberFieldFinitePlace.Completion place) := by
  letI := completionAlgebraPadic place
  refine Module.IsTorsionFree.of_smul_eq_zero (fun r m h => ?_)
  by_cases hr : r = 0
  · exact Or.inl hr
  · refine Or.inr ?_
    have halg : algebraMap ℚ_[completionPadicPrime place]
        (LeanFormal.IUT.NumberFieldFinitePlace.Completion place) r ≠ 0 :=
      fun hzero => hr (RingHom.injective (algebraMap ℚ_[completionPadicPrime place]
        (LeanFormal.IUT.NumberFieldFinitePlace.Completion place)) (by simpa using hzero))
    have hmul : algebraMap ℚ_[completionPadicPrime place]
        (LeanFormal.IUT.NumberFieldFinitePlace.Completion place) r * m = 0 := by
      simpa [Algebra.smul_def] using h
    exact (mul_eq_zero.mp hmul).resolve_left halg

/-! ## 2. The unconditional actual embedding -/

/-- **Unconditional embedding for the actual completion.**  For every finite
place of F, the actual completion K_v admits an actual injective Q_p-algebra
homomorphism into PadicAlgCl at the rational prime under the place.  This
discharges the typeclass conditional of Example36CompletionIntoAlgCl using the
transported instances above. -/
theorem exists_injective_completionEmbedding_place (place : NumberField.FinitePlace F) :
    ∃ φ : LeanFormal.IUT.NumberFieldFinitePlace.Completion place →ₐ[ℚ_[completionPadicPrime place]]
        PadicAlgCl (completionPadicPrime place), Function.Injective φ := by
  letI := completionAlgebraPadic place
  haveI := completionModuleIsTorsionFree place
  haveI := completionAlgebraIsAlgebraic place
  exact exists_injective_algHom_padicAlgCl (completionPadicPrime place)

/-- The bridge from the tree's completion to the adic completion used in
Example36: the two completion types are propositionally equal for
place = NumberField.FinitePlace.mk v. -/
theorem completion_eq_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    LeanFormal.IUT.NumberFieldFinitePlace.Completion (NumberField.FinitePlace.mk v) =
      v.adicCompletion F := by
  change (NumberField.FinitePlace.mk v).maximalIdeal.adicCompletion F = v.adicCompletion F
  rw [NumberField.FinitePlace.maximalIdeal_mk]

/-- **Unconditional actual injective field homomorphism at the completion place.**
The tree's completion type Completion (NumberField.FinitePlace.mk v) is
definitionally (underlyingPrime (FinitePlace.mk v)).adicCompletion F, i.e. the
actual completion at the place (FinitePlace.mk v).maximalIdeal; the recorded
type equality completion_eq_adicCompletion identifies it with v.adicCompletion F
at the level of places. -/
theorem exists_injective_completionEmbedding_at (v : HeightOneSpectrum (𝓞 F)) :
    ∃ φ : ((NumberField.FinitePlace.mk v).maximalIdeal).adicCompletion F →+*
        PadicAlgCl (completionPadicPrime (NumberField.FinitePlace.mk v)),
      Function.Injective φ := by
  obtain ⟨φ, hφ⟩ := exists_injective_completionEmbedding_place
    (NumberField.FinitePlace.mk v)
  exact ⟨φ.toRingHom, hφ⟩

/-- **Unconditional actual injective unit embedding at the completion place.** -/
theorem exists_injective_completionUnitEmbedding_at
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (φ : ((NumberField.FinitePlace.mk v).maximalIdeal).adicCompletion F →+*
          PadicAlgCl (completionPadicPrime (NumberField.FinitePlace.mk v))),
      Function.Injective φ ∧
        Function.Injective (unitsMapIntoPadicAlgCl
          (completionPadicPrime (NumberField.FinitePlace.mk v)) φ) := by
  obtain ⟨φ, hφ⟩ := exists_injective_completionEmbedding_at (F := F) v
  exact ⟨φ, hφ, unitsMapIntoPadicAlgCl_injective
    (completionPadicPrime (NumberField.FinitePlace.mk v)) φ hφ⟩

/-! ## 3. Normalized-value compatibility: reduction and consequences -/

/-- **Reduction of the normalized-value compatibility to the log-norm identity.**
The compatibility of Example36CompletionIntoAlgCl is exactly the assertion that
the p-adic log of the image unit is the completion exponent divided by e. -/
theorem normalizedValueCompatible_iff_log_norm
    {p : Nat} [Fact (Nat.Prime p)] (v : HeightOneSpectrum (𝓞 F)) (e : Nat)
    (φ : v.adicCompletion F →+* PadicAlgCl p) :
    NormalizedValueCompatible p v e φ ↔
      ∀ x : (v.adicCompletion F)ˣ,
        Real.log ‖((unitsMapIntoPadicAlgCl p φ x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ =
          -((completionValuationExponent v x : Real) / (e : Real)) * Real.log (p : Real) := by
  have hL : Real.log (p : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt))
  constructor
  · intro h x
    have hx := congrArg (fun q : Rat => (q : Real)) (h x)
    have hcast : ((padicAlgClUnitRationalLogVal p
        (unitsMapIntoPadicAlgCl p φ x)).toAdd : Real) =
        -Real.log ‖((unitsMapIntoPadicAlgCl p φ x : (PadicAlgCl p)ˣ) :
          PadicAlgCl p)‖ / Real.log (p : Real) := by
      rw [padicAlgClUnitRationalLogVal_realification]
      simp [LeanFormal.IUT.padicAlgClUnitLogVal]
      ring
    rw [hcast] at hx
    push_cast at hx
    rw [div_eq_iff hL] at hx
    linarith
  · intro h x
    have hx := h x
    have hcast : ((padicAlgClUnitRationalLogVal p
        (unitsMapIntoPadicAlgCl p φ x)).toAdd : Real) =
        -Real.log ‖((unitsMapIntoPadicAlgCl p φ x : (PadicAlgCl p)ˣ) :
          PadicAlgCl p)‖ / Real.log (p : Real) := by
      rw [padicAlgClUnitRationalLogVal_realification]
      simp [LeanFormal.IUT.padicAlgClUnitLogVal]
      ring
    have hgoal : ((padicAlgClUnitRationalLogVal p
        (unitsMapIntoPadicAlgCl p φ x)).toAdd : Real) =
        (((completionValuationExponent v x : Rat) / (e : Rat) : Rat) : Real) := by
      rw [hcast, hx]
      push_cast
      field_simp
    exact Rat.cast_injective hgoal

/-- **Value lattice under the log-norm identity**: the rational value group of
the completion-unit image is exactly the lattice (1/e)Z. -/
theorem completionImage_value_lattice_actual
    {p : Nat} [Fact (Nat.Prime p)] (v : HeightOneSpectrum (𝓞 F)) (e : Nat)
    (he : 0 < e) (φ : v.adicCompletion F →+* PadicAlgCl p)
    (hφ : NormalizedValueCompatible p v e φ) :
    Set.range (fun x : (v.adicCompletion F)ˣ =>
        (padicAlgClUnitRationalLogVal p (unitsMapIntoPadicAlgCl p φ x)).toAdd) =
      Set.range (fun n : Int => (n : Rat) / (e : Rat)) :=
  completionImage_value_lattice p v e he φ hφ

/-- **Kernel under the log-norm identity**: the kernel is exactly O_v^x. -/
theorem completionImage_value_eq_one_iff_integralUnits_actual
    {p : Nat} [Fact (Nat.Prime p)] (v : HeightOneSpectrum (𝓞 F)) (e : Nat)
    (he : 0 < e) (φ : v.adicCompletion F →+* PadicAlgCl p)
    (hφ : NormalizedValueCompatible p v e φ) (x : (v.adicCompletion F)ˣ) :
    padicAlgClUnitRationalLogVal p (unitsMapIntoPadicAlgCl p φ x) = 1 ↔
      x ∈ (v.adicCompletionIntegers F).units :=
  completionImage_value_eq_one_iff_integralUnits p v e he φ hφ x

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- **Status card: actual completion embedding via the existing p-adic scalar
structure, and the remaining normalized-value comparison.**

Actual in this module: for every NumberField.FinitePlace the actual completion
K_v = Completion place carries the tree's Q_p-algebra (padicCompletionAlgebra),
Module.Finite (moduleFinite_padicCompletionAlgebra), and the derived
Algebra.IsAlgebraic and Module.IsTorsionFree instances; by
Example36CompletionIntoAlgCl.exists_injective_algHom_padicAlgCl the actual
completion admits an unconditional injective Q_p-algebra embedding into
PadicAlgCl p at the rational prime under the place, and an injective map on
units into (PadicAlgCl p)^x; the same statement is recorded at the concrete
completion place (NumberField.FinitePlace.mk v).maximalIdeal, with the
place-level bridge completion_eq_adicCompletion identifying the places.  This
discharges the typeclass conditional of Example36CompletionIntoAlgCl (Algebra,
Module.IsTorsionFree, Algebra.IsAlgebraic) unconditionally for the actual tree
completion.  The literal transport of the hom across the proof-level place
equality to the syntactically displayed v.adicCompletion F is not constructed.

Also actual: the reduction normalizedValueCompatible_iff_log_norm, which shows
that the normalized-value compatibility is exactly the log-norm identity
Real.log ||image unit|| = -(completionValuationExponent v x / e) * Real.log p,
and (under it) the actual rational value lattice (1/e)Z and kernel O_v^x.

Still missing (NOT constructed, NOT claimed): the log-norm identity itself for
the actual embedding, i.e. the normalized norm/valuation comparison between the
completion valuation Valued.v and the PadicAlgCl (spectral) norm: the
normalized completion norm should be p^(-nu/e_w) with e_w the ramification
index over the rational prime, equivalently the p-adic algebra embedding is
isometric for the spectral norms.  Consequently NormalizedValueCompatible with
e = e_w is not yet proved here; when that comparison is supplied, the
(1/e_w)Z lattice and O_v^x kernel follow by the shifted theorems of this
module.  Remaining source components (unchanged): rho_v normalization
isomorphism, log-shell carrier, Frobenius/log-Kummer carrier.  No
source-faithfulness claim; no theta-pilot, q-pilot or Tate claim. -/
def example36CompletionEmbeddingActual : Obligation :=
  { id := "IUT-I-II.example36-completion-embedding-actual"
    source :=
      "IUT I, Example 3.5, (i); IUT III, Example 3.6; boundary (2) source " ++
        "V_K completion-embedding row"
    status := VerificationStatus.interface
    note :=
      "Actual: transported p-adic scalar structure on the actual completion " ++
        "(Q_p-algebra, Module.Finite, derived Algebra.IsAlgebraic and " ++
        "Module.IsTorsionFree); unconditional actual injective Q_p-algebra " ++
        "embedding of the completion into PadicAlgCl p, transported to an " ++
        "injective ring hom out of v.adicCompletion F and an injective unit " ++
        "map into (PadicAlgCl p)^x; reduction of NormalizedValueCompatible " ++
        "to the log-norm identity and, under it, the (1/e)Z value lattice " ++
        "and O_v^x kernel. Missing: the log-norm identity itself for the " ++
        "actual embedding (normalized norm of the completion is " ++
        "p^(-nu/e_w); the p-adic algebra embedding is isometric for the " ++
        "spectral norms), hence NormalizedValueCompatible with e = e_w is " ++
        "not yet proved. Remaining: rho_v normalization isomorphism, " ++
        "log-shell, Frobenius/log-Kummer. No source-faithfulness claim; no " ++
        "theta/q/Tate claim."
    dependsOn :=
      [ "IUT-I-II.example36-completion-into-agcl",
        "IUT-I-II.example36-source-vertical-rational-carrier" ] }

end LeanFormal.IUT.Audit
