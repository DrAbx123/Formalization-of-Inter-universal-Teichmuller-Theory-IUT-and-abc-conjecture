import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceVerticalRationalCarrier
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation
import LeanFormal.IUT.Audit.Status
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Embedding the finite-place completion into the algebraic closure of Q_p

Group-1 continuation of boundary (2) (source V_K).  The frozen card of
Example36SourceVerticalRationalCarrier left open the identification of the
source value group with the rational value group of (Qbar_p)^x.  This module
constructs, from Mathlib's universal property of algebraic closures, an
actual injective Q_p-algebra embedding of any algebraic extension of Q_p into
the tree's carrier PadicAlgCl p = AlgebraicClosure Q_[p] (Mathlib
IsAlgClosed.lift), pushes it to units, and proves the value-group
compatibility of the image lattice under the explicitly named normalization
hypothesis.  For the *actual* completion K_v = v.adicCompletion F the Q_p-
algebra structure, the finite/algebraic extension instance and the
valuation-normalization compatibility are NOT in the tree; the exact missing
API is frozen in the card at the end.  No source-faithfulness claim.

## What is actual in this module

* PadicAlgCl p is definitionally AlgebraicClosure Q_[p], with Field,
  IsAlgClosed, Q_[p]-Algebra and Algebra.IsAlgebraic instances;
* for every field K with Q_[p]-algebra, torsion-free module and algebraic
  extension instances, there is an actual Q_p-algebra hom K -> PadicAlgCl p
  and it is injective (IsAlgClosed.lift plus RingHom.injective);
* the induced monoid hom on units K^x -> (PadicAlgCl p)^x is injective;
* for the actual completion units of v.adicCompletion F, assuming the
  missing Q_p-algebra/algebraic instances and the explicitly named normalized-
  valuation compatibility, the rational value group of the image is exactly
  the lattice (1/e)Z and the kernel is the integral units O_v^x.
* the base-field case K = Q_[p] itself gives an actual injective
  Q_p-algebra embedding Q_[p] -> PadicAlgCl p (the universal property is
  applied for real).

## What remains missing

For the actual K_v = v.adicCompletion F, the tree does not provide: the
rational prime p under v with Fact (Nat.Prime p), the Q_[p]-algebra structure
on K_v compatible with the F-algebra structure, the Module.IsTorsionFree and
Algebra.IsAlgebraic instances (finiteness of K_v over Q_p), and the
valuation-normalization compatibility producing the exponent identity (the
isometry/normalization of the two nonarchimedean absolute values).  The
frozen source rho_v normalization, log-shell and Frobenius/log-Kummer carrier
remain open as before.  See LeanFormal.IUT.Audit.example36CompletionIntoAlgCl.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

/-! ## 1. The target algebraic closure and the universal embedding -/

/-- PadicAlgCl is the algebraic closure of Q_[p]: consumer of the reducible
definition, recorded so that the target field structure is explicit. -/
theorem padicAlgCl_eq_algebraicClosure (p : Nat) [Fact (Nat.Prime p)] :
    PadicAlgCl p = AlgebraicClosure ℚ_[p] :=
  rfl

/-- The target rational carrier of the algebraic closure is actual: the
rational value-group map of (PadicAlgCl p)^x is onto Q. -/
theorem padicAlgCl_unitRationalValue_actual (p : Nat) [Fact (Nat.Prime p)] :
    Function.Surjective (padicAlgClUnitRationalLogVal p) ∧
      Set.range (fun u : (PadicAlgCl p)ˣ =>
        (((padicAlgClUnitRationalLogVal p u).toAdd : Rat) : Real)) =
        Set.range (fun q : Rat => (q : Real)) :=
  ⟨padicAlgClUnitRationalLogVal_surjective p,
    padicAlgClUnitRationalLogVal_range_realification p⟩

/-- **The universal-property embedding.**  Every algebraic extension of Q_p
admits an actual Q_p-algebra homomorphism into PadicAlgCl p, and it is
injective (a field homomorphism into a nontrivial field). -/
theorem exists_injective_algHom_padicAlgCl (p : Nat) [Fact (Nat.Prime p)]
    {K : Type u} [Field K] [Algebra ℚ_[p] K]
    [Module.IsTorsionFree ℚ_[p] K] [Algebra.IsAlgebraic ℚ_[p] K] :
    ∃ φ : K →ₐ[ℚ_[p]] PadicAlgCl p, Function.Injective φ := by
  let φ : K →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift
  exact ⟨φ, RingHom.injective φ.toRingHom⟩

/-- The chosen universal embedding of an algebraic extension of Q_p. -/
noncomputable def padicAlgClEmbedding (p : Nat) [Fact (Nat.Prime p)]
    {K : Type u} [Field K] [Algebra ℚ_[p] K]
    [Module.IsTorsionFree ℚ_[p] K] [Algebra.IsAlgebraic ℚ_[p] K] :
    K →ₐ[ℚ_[p]] PadicAlgCl p :=
  IsAlgClosed.lift

/-- The chosen embedding is injective. -/
theorem padicAlgClEmbedding_injective (p : Nat) [Fact (Nat.Prime p)]
    {K : Type u} [Field K] [Algebra ℚ_[p] K]
    [Module.IsTorsionFree ℚ_[p] K] [Algebra.IsAlgebraic ℚ_[p] K] :
    Function.Injective (fun x : K => padicAlgClEmbedding p x) := by
  intro x y h
  exact RingHom.injective (padicAlgClEmbedding p).toRingHom h

/-- The actual base-field embedding Q_[p] -> PadicAlgCl p, obtained from the
universal property (not an assumed map). -/
theorem exists_injective_baseEmbedding_padicAlgCl (p : Nat) [Fact (Nat.Prime p)] :
    ∃ φ : ℚ_[p] →ₐ[ℚ_[p]] PadicAlgCl p, Function.Injective φ :=
  exists_injective_algHom_padicAlgCl p (K := ℚ_[p])

/-! ## 2. The induced map on units -/

/-- The monoid homomorphism on units induced by a ring homomorphism into the
algebraic closure. -/
def unitsMapIntoPadicAlgCl (p : Nat) [Fact (Nat.Prime p)] {K : Type u} [Field K]
    (φ : K →+* PadicAlgCl p) : Kˣ →* (PadicAlgCl p)ˣ :=
  Units.map φ.toMonoidHom

/-- The unit map is the ring map on representatives. -/
@[simp]
theorem unitsMapIntoPadicAlgCl_apply_coe (p : Nat) [Fact (Nat.Prime p)]
    {K : Type u} [Field K] (φ : K →+* PadicAlgCl p) (x : Kˣ) :
    ((unitsMapIntoPadicAlgCl p φ x : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      φ (x : K) :=
  rfl

/-- The unit map is injective when the ring map is. -/
theorem unitsMapIntoPadicAlgCl_injective (p : Nat) [Fact (Nat.Prime p)]
    {K : Type u} [Field K] (φ : K →+* PadicAlgCl p)
    (hφ : Function.Injective φ) :
    Function.Injective (unitsMapIntoPadicAlgCl p φ) :=
  Units.map_injective hφ

/-- The rational value of an image unit is a rational number (the target
rational carrier is actual). -/
theorem unitsMapIntoPadicAlgCl_rationalValue (p : Nat) [Fact (Nat.Prime p)]
    {K : Type u} [Field K] (φ : K →+* PadicAlgCl p) (x : Kˣ) :
    ∃ q : Rat,
      ((padicAlgClUnitRationalLogVal p (unitsMapIntoPadicAlgCl p φ x)).toAdd : Real) =
        (q : Real) :=
  ⟨(padicAlgClUnitRationalLogVal p (unitsMapIntoPadicAlgCl p φ x)).toAdd, rfl⟩

/-! ## 3. Value-group compatibility for the actual completion units -/

/-- The normalized-value compatibility hypothesis for the actual completion
units: the rational value of the image unit is the completion exponent divided
by the local ramification degree e.  This is exactly the compatibility that
the missing Q_p/valuation API of the actual completion must supply; it is an
explicit hypothesis, not an asserted identification. -/
def NormalizedValueCompatible (p : Nat) [Fact (Nat.Prime p)]
    {F : Type u} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (e : Nat) (φ : v.adicCompletion F →+* PadicAlgCl p) : Prop :=
  ∀ x : (v.adicCompletion F)ˣ,
    (padicAlgClUnitRationalLogVal p (unitsMapIntoPadicAlgCl p φ x)).toAdd =
      (completionValuationExponent v x : Rat) / (e : Rat)

/-- **Value-group compatibility (1/e)Z lattice.**  Under the normalized-value
compatibility, the rational value group of the image of the completion units
is exactly the lattice (1/e)Z inside Q. -/
theorem completionImage_value_lattice (p : Nat) [Fact (Nat.Prime p)]
    {F : Type u} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (e : Nat) (_he : 0 < e) (φ : v.adicCompletion F →+* PadicAlgCl p)
    (hφ : NormalizedValueCompatible p v e φ) :
    Set.range (fun x : (v.adicCompletion F)ˣ =>
        (padicAlgClUnitRationalLogVal p (unitsMapIntoPadicAlgCl p φ x)).toAdd) =
      Set.range (fun n : Int => (n : Rat) / (e : Rat)) := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨completionValuationExponent v x, (hφ x).symm⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨x, hx⟩ := completionValuationExponent_surjective (K := F) v n
    refine ⟨x, ?_⟩
    change (padicAlgClUnitRationalLogVal p (unitsMapIntoPadicAlgCl p φ x)).toAdd =
      (n : Rat) / (e : Rat)
    rw [hφ x, hx]

/-- **Kernel compatibility.**  Under the normalized-value compatibility, the
kernel of the rational value of the image is exactly the group O_v^x of
integral units of the completion. -/
theorem completionImage_value_eq_one_iff_integralUnits (p : Nat)
    [Fact (Nat.Prime p)] {F : Type u} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (e : Nat) (he : 0 < e)
    (φ : v.adicCompletion F →+* PadicAlgCl p)
    (hφ : NormalizedValueCompatible p v e φ) (x : (v.adicCompletion F)ˣ) :
    padicAlgClUnitRationalLogVal p (unitsMapIntoPadicAlgCl p φ x) = 1 ↔
      x ∈ (v.adicCompletionIntegers F).units := by
  have heq : (e : Rat) ≠ 0 := by
    exact_mod_cast (ne_of_gt he)
  constructor
  · intro h
    have h0 : (padicAlgClUnitRationalLogVal p
        (unitsMapIntoPadicAlgCl p φ x)).toAdd = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this
    rw [hφ x] at h0
    have hzero : (completionValuationExponent v x : Rat) = 0 := by
      have := h0
      field_simp at this
      simpa [heq] using this
    have hz : completionValuationExponent v x = 0 := by
      exact_mod_cast hzero
    rwa [completionValuationExponent_eq_zero_iff_mem_integralUnits] at hz
  · intro h
    have hz : completionValuationExponent v x = 0 :=
      (completionValuationExponent_eq_zero_iff_mem_integralUnits v x).mpr h
    apply Multiplicative.toAdd.injective
    rw [hφ x, hz, toAdd_one]
    simp

/-- **The conditional actual completion embedding.**  For the actual
completion v.adicCompletion F, assuming the missing Q_p-algebra and algebraic
instances, the universal property gives an actual injective field
homomorphism into PadicAlgCl p. -/
theorem exists_injective_completionEmbedding (p : Nat) [Fact (Nat.Prime p)]
    {F : Type u} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [Algebra ℚ_[p] (v.adicCompletion F)]
    [Module.IsTorsionFree ℚ_[p] (v.adicCompletion F)]
    [Algebra.IsAlgebraic ℚ_[p] (v.adicCompletion F)] :
    ∃ φ : v.adicCompletion F →ₐ[ℚ_[p]] PadicAlgCl p, Function.Injective φ :=
  exists_injective_algHom_padicAlgCl p (K := v.adicCompletion F)

/-- **Actual injective field homomorphism, conditional form.**  Same as the
previous theorem, with the ring-homomorphism presentation and the unit map. -/
theorem completionEmbedding_units (p : Nat) [Fact (Nat.Prime p)]
    {F : Type u} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [Algebra ℚ_[p] (v.adicCompletion F)]
    [Module.IsTorsionFree ℚ_[p] (v.adicCompletion F)]
    [Algebra.IsAlgebraic ℚ_[p] (v.adicCompletion F)] :
    ∃ (φ : v.adicCompletion F →+* PadicAlgCl p),
      Function.Injective φ ∧ Function.Injective (unitsMapIntoPadicAlgCl p φ) := by
  obtain ⟨φ, hφ⟩ := exists_injective_completionEmbedding (p := p) v
  exact ⟨φ.toRingHom, hφ, unitsMapIntoPadicAlgCl_injective p φ.toRingHom hφ⟩

/-! ## 4. What is actual and what remains; exact missing API card -/

/-- **Status of the frozen source value-group identification.**  Actual in the
tree: the target rational value group of (Qbar_p)^x (onto Q, rational line),
the universal-property embedding of any algebraic extension of Q_p into
PadicAlgCl p (injective) and the induced injective unit map; for the actual
completion units, under the named normalized-value compatibility the image
value group is the lattice (1/e)Z with kernel O_v^x.  The actual embedding of
the number-field completion itself still needs the missing Q_p-algebra /
finiteness / valuation-normalization API (card). -/
theorem sourceValueGroupIdentification_status (p : Nat) [Fact (Nat.Prime p)] :
    (∃ φ : ℚ_[p] →+* PadicAlgCl p, Function.Injective φ) ∧
      Function.Surjective (padicAlgClUnitRationalLogVal p) ∧
      Set.range (fun u : (PadicAlgCl p)ˣ =>
        (((padicAlgClUnitRationalLogVal p u).toAdd : Rat) : Real)) =
        Set.range (fun q : Rat => (q : Real)) := by
  obtain ⟨φ, hφ⟩ := exists_injective_baseEmbedding_padicAlgCl p
  exact ⟨⟨φ.toRingHom, hφ⟩, padicAlgClUnitRationalLogVal_surjective p,
    padicAlgClUnitRationalLogVal_range_realification p⟩

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- **Exact missing-API card for the embedding of the completion into the
algebraic closure of Q_p, and the partial source value-group identification.**

Actual in this module: PadicAlgCl p is definitionally AlgebraicClosure Q_[p]
with Field, IsAlgClosed, Q_[p]-Algebra and Algebra.IsAlgebraic instances; the
target rational value group of (PadicAlgCl p)^x is onto Q (from the frozen
rational carrier); for every algebraic extension K of Q_p (with Q_p-algebra,
torsion-free module and algebraic instances) the universal property
IsAlgClosed.lift produces an actual Q_p-algebra hom K -> PadicAlgCl p, proved
injective via RingHom.injective; the induced hom on units K^x -> (PadicAlgCl
p)^x is injective; for the actual completion units of v.adicCompletion F,
under the explicitly named normalized-value compatibility, the rational value
group of the image is exactly the lattice (1/e)Z and the kernel is the group
of integral units O_v^x; the base-field case Q_[p] -> PadicAlgCl p is an
actual injective embedding.

Missing (NOT constructed, NOT claimed) for the actual completion K_v =
v.adicCompletion F of a number field: (i) the rational prime p under v with a
Fact (Nat.Prime p) instance and the LiesOver relation of v above (p); (ii) a
Q_[p]-algebra structure on K_v compatible with the F-algebra structure
(scalar tower over Q); (iii) the Module.IsTorsionFree Q_[p] K_v instance and
the Algebra.IsAlgebraic Q_[p] K_v instance (finiteness of the local field
K_v over Q_p); (iv) the valuation-normalization compatibility between the
completion valuation Valued.v and the PadicAlgCl norm, which yields the
normalized-value identity with e = e_w (the local ramification degree).
Until these are supplied, the embedding theorem is conditional for the actual
completion; no fake embedding or assumed identification is used.

Remaining frozen source components (unchanged): the rho_v normalization
isomorphism, the log-shell carrier, and the Frobenius/log-Kummer carrier.  No
source-faithfulness claim; no theta-pilot, q-pilot or Tate claim. -/
def example36CompletionIntoAlgCl : Obligation :=
  { id := "IUT-I-II.example36-completion-into-agcl"
    source :=
      "IUT I, Example 3.5, (i); IUT III, Example 3.6; boundary (2) source " ++
        "V_K value-group identification row"
    status := VerificationStatus.interface
    note :=
      "Actual: PadicAlgCl p = AlgebraicClosure Q_[p] with Field/IsAlgClosed/ " ++
        "Algebra/IsAlgebraic instances; target rational value group of " ++
        "(PadicAlgCl p)^x onto Q; universal-property IsAlgClosed.lift gives " ++
        "an actual injective Q_p-algebra embedding of every algebraic " ++
        "extension of Q_p into PadicAlgCl p, with an injective induced map " ++
        "on units; for the actual completion units, under the explicitly " ++
        "named NormalizedValueCompatible hypothesis, the rational value " ++
        "group of the image is the lattice (1/e)Z and the kernel is the " ++
        "integral units O_v^x; Q_[p] -> PadicAlgCl p is an actual " ++
        "injective embedding. Missing for the actual completion " ++
        "v.adicCompletion F: rational prime p under v with Fact " ++
        "(Nat.Prime p) and LiesOver; Q_[p]-algebra structure compatible " ++
        "with the F-algebra (scalar tower over Q); Module.IsTorsionFree " ++
        "and Algebra.IsAlgebraic Q_[p] K_v (local finiteness); the " ++
        "valuation-normalization compatibility between Valued.v and the " ++
        "PadicAlgCl norm giving e = e_w. Until supplied the embedding is " ++
        "conditional for the actual completion; no fake embedding or " ++
        "assumed identification. Still frozen: rho_v normalization, " ++
        "log-shell, Frobenius/log-Kummer. No source-faithfulness claim; " ++
        "no theta/q/Tate claim."
    dependsOn :=
      [ "IUT-I-II.example36-source-vertical-rational-carrier",
        "IUT-I-II.example36-vertical-value-carrier" ] }

end LeanFormal.IUT.Audit
