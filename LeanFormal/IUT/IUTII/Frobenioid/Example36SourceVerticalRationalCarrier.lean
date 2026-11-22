import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidValueGroupRationality
import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueMapTransportCorrection
import LeanFormal.IUT.IUTII.Frobenioid.Example36VerticalCarrier
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Source vertical rational value carrier and rho_v feasibility

Boundary (2), source-side fragment.  This module attacks the source vertical
V_K/rho_v carrier with the actual data available in the tree and freezes
exactly what remains missing.  No source-faithfulness claim is made.

## 1. The rational value group of (Qbar_p)^x

The tree proves the rational value-group statement for the algebraically
closed local field (Qbar_p)^x (PrimeStripFrobenioidValueGroupRationality):
the normalized log value -log_p ||u|| has image exactly Q.  Here we
construct the corresponding rational value-group homomorphism
padicAlgClUnitRationalLogVal p : (Qbar_p)^x ->* Multiplicative Q, prove it
is onto Q, that its kernel is the norm-one units, that its realification is
the tree's padicAlgClUnitLogVal, and build the reduced value kernel
padicRationalValueKernel whose realification image is the rational line.

## 2. The partial source vertical rational carrier over the actual data

For a PlaceLocalizationTransport T of number-field place data and an upper
finite place w with base place v = T.finitePlaceRestriction w:

* completionValueToRational T w : (K_w)^x ->* Multiplicative Q is the
  actual completion value coordinate normalized by the actual ramification
  index, x |-> nu_w(x)/e_w.  This is the value an embedding of K_w into
  (Qbar_p)^x would induce on value groups, but the embedding itself is NOT
  constructed in the tree.
* sourceValueToRational T w : F^x ->* Multiplicative Q is the base
  finite-place exponent f |-> nu_v(f) at the base place.
* completionValueToRational_embedded proves the exact compatibility
  completionValue (globalToLocal f) = sourceValue f from the corrected
  cross-field ramification law (task-48).
* The ranges are exact: completionValueToRational has image the lattice
  (1/e_w) * Z inside Q (completionValueToRational_range); in particular it
  is not all of Q, which is why the source rational identification is
  missing.

## 3. The candidate rho_v normalization

With q_v = #(O_F/v), q_w = #(O_F'/w), actual ramification index e_w and
actual relative residue degree f_w = log q_w / log q_v (real-valued, from
the actual residue cardinalities), the candidate normalization of IUT I,
Example 3.5, (i) is

  rho_v(r) = (1 / [K_w:(F_mod)_v]) * r * logPhi(pv)

with [K_w:(F_mod)_v] = e_w * f_w (real-valued from actual data) and
logPhi(pv) := log q_v (the log of the actual base residue cardinality).
candidateRhoNormalization realizes this as a monoid homomorphism
Multiplicative Q ->* Multiplicative R; candidateRhoNormalization_basis
records the paper-shape value log q_v / (e_w f_w).  The compatibility with
the actual data is the exact identity
realification_w (phi f) = -(e_w f_w)^2 * rho_v(nu_v(f))
(finitePlaceUnitValueKernel_realification_eq_candidateRho), i.e. the
candidate is the base log-volume divided by [K_w:F_v]; the displayed square
factor is the normalization mismatch that the missing source rho_v
isomorphism has to resolve.

## 3'. The actual source log-volume normalization rho_v

The candidate of section 3 is not the normalization used by the actual local
log-volume, and its square factor `(e_w f_w)^2` is a genuine mismatch.  The
actual normalization is

  sourceRhoLogVolume(r) = [K_w:(F_mod)_v] * log q_v * r = e_w * r * log q_w,

i.e. the candidate multiplied by `(e_w f_w)^2`
(sourceRhoLogVolume_eq_relativeLocalDegree_sq_mul_candidate).  It satisfies
the exact squares

* with the completion value map: rho_v(nu_w(x)/e_w) = nu_w(x) * log q_w
  (sourceRhoLogVolume_completionValue);
* with the transport: on the phi-image of a global unit the same local
  log-volume is recovered from the base-place value
  (sourceRhoLogVolume_sourceValue);
* with the actual local value kernel: the realified kernel is the negative of
  the source normalization, with no residual factor
  (sourceRhoLogVolume_eq_neg_unitValueKernel).

It is the *unique* monoid homomorphism with the completion square
(sourceRhoLogVolume_unique), and the candidate satisfies that square if and
only if `[K_w:(F_mod)_v] = 1`
(candidateRhoNormalization_completionValue_iff).  In particular the factor
`1/[K_w:(F_mod)_v]` cannot be the source normalization unless the relative
local degree is one; the wrong formula is nowhere used as if correct.

## 3''. Value-group identification through an actual embedding

Since the actual embedding `K_w -> (Qbar_p)^x` is constructed below this
module in the import graph, the identification is stated over an explicit
`CompletionValueEmbeddingDatum`: an injective ring homomorphism together with
the normalized-value identity.  Under it,

* the embedding-induced rational value map is the intrinsic completion value
  map (completionValueViaEmbedding_eq_completionValueToRational);
* its image is the lattice `(1/e_w) Z` (completionValueViaEmbedding_range)
  and its kernel is `O_w^×`
  (completionValueViaEmbedding_eq_one_iff_mem_integralUnits);
* every completion unit has a unique integer exponent
  (completionValueViaEmbedding_existsUnique_exponent);
* the value of the image unit is natural in the place transport
  (completionValueViaEmbedding_sourceValue);
* the normalized-value identity is exactly the log-norm identity
  `||phi x|| = p^(-(nu_w(x)/e_w))`, with the sign of the tree's convention
  `padicAlgClUnitRationalLogVal = -log_p ||.||`
  (completionValueViaEmbedding_norm,
  completionValueViaEmbedding_normalizedValue_iff_norm).

## 4. Remaining components (no claim)

The card LeanFormal.IUT.Audit.example36SourceVerticalRationalCarrier records
the boundary.  Actual here: the rational value group of `(Qbar_p)^x`, the
partial source carrier over the actual number-field data, the actual source
normalization with its exact squares and uniqueness, and the conditional
identification through an embedding datum.  Not constructed: the embedding of
the actual completion together with its normalized-value identity (it is
supplied by the later embedding modules; its remaining analytic content is the
log-norm identity), the log-shell carrier, and the Frobenius/log-Kummer
carrier.  No source-faithfulness claim; no theta-pilot, q-pilot or Tate
claim. -/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The rational value group of (Qbar_p)^x -/

/-- The auxiliary rational normalized log value: for a unit u of
(Qbar_p)^x with norm p^q (q : Q from the tree's rationality theorem), the
value is -q, matching the tree's convention padicAlgClUnitLogVal = -log_p
||u||. -/
noncomputable def padicAlgClUnitRationalLogValAux (p : Nat) [Fact (Nat.Prime p)]
    (u : (PadicAlgCl p)ˣ) : Rat :=
  -(Classical.choose (LeanFormal.IUT.padicAlgCl_norm_eq_rpow_rat p
    (u : PadicAlgCl p) (Units.ne_zero u)))

/-- The realification of the auxiliary rational value is the tree's actual
normalized log value. -/
theorem padicAlgClUnitRationalLogValAux_cast (p : Nat) [Fact (Nat.Prime p)]
    (u : (PadicAlgCl p)ˣ) :
    ((padicAlgClUnitRationalLogValAux p u : Rat) : Real) =
      (LeanFormal.IUT.padicAlgClUnitLogVal p u).toAdd := by
  have hq := Classical.choose_spec (LeanFormal.IUT.padicAlgCl_norm_eq_rpow_rat p
    (u : PadicAlgCl p) (Units.ne_zero u))
  have hp0 : (0 : Real) < (p : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hL : Real.log (p : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt))
  have hlog : Real.log ‖(u : PadicAlgCl p)‖ =
      ((Classical.choose (LeanFormal.IUT.padicAlgCl_norm_eq_rpow_rat p
        (u : PadicAlgCl p) (Units.ne_zero u)) : Rat) : Real) * Real.log (p : Real) := by
    calc Real.log ‖(u : PadicAlgCl p)‖
        = Real.log ((p : Real) ^
            (((Classical.choose (LeanFormal.IUT.padicAlgCl_norm_eq_rpow_rat p
              (u : PadicAlgCl p) (Units.ne_zero u)) : Rat) : Real))) := by
          exact congrArg Real.log hq
      _ = ((Classical.choose (LeanFormal.IUT.padicAlgCl_norm_eq_rpow_rat p
            (u : PadicAlgCl p) (Units.ne_zero u)) : Rat) : Real) * Real.log (p : Real) :=
          Real.log_rpow hp0 _
  unfold padicAlgClUnitRationalLogValAux
  push_cast
  change -((Classical.choose (LeanFormal.IUT.padicAlgCl_norm_eq_rpow_rat p
      (u : PadicAlgCl p) (Units.ne_zero u)) : Rat) : Real) =
    -(Real.log ‖(u : PadicAlgCl p)‖ / Real.log (p : Real))
  rw [hlog]
  field_simp

/-- The rational value-group homomorphism of (Qbar_p)^x, normalized so that
the prime unit p has value 1 in Q. -/
noncomputable def padicAlgClUnitRationalLogVal (p : Nat) [Fact (Nat.Prime p)] :
    (PadicAlgCl p)ˣ →* Multiplicative Rat :=
  MonoidHom.mk' (fun u => Multiplicative.ofAdd (padicAlgClUnitRationalLogValAux p u))
    (by
      intro u v
      rw [← ofAdd_add]
      congr 1
      have h : (((padicAlgClUnitRationalLogValAux p (u * v)) : Rat) : Real) =
          (((padicAlgClUnitRationalLogValAux p u) : Rat) : Real) +
            (((padicAlgClUnitRationalLogValAux p v) : Rat) : Real) := by
        rw [padicAlgClUnitRationalLogValAux_cast,
          padicAlgClUnitRationalLogValAux_cast,
          padicAlgClUnitRationalLogValAux_cast, map_mul, toAdd_mul]
      rw [← Rat.cast_add] at h
      exact Rat.cast_injective h)

/-- The rational value of a unit is ofAdd of the auxiliary rational number. -/
theorem padicAlgClUnitRationalLogVal_apply (p : Nat) [Fact (Nat.Prime p)]
    (u : (PadicAlgCl p)ˣ) :
    padicAlgClUnitRationalLogVal p u =
      Multiplicative.ofAdd (padicAlgClUnitRationalLogValAux p u) :=
  rfl

/-- The realification of the rational value is the tree's actual normalized
-log_p ||u||. -/
theorem padicAlgClUnitRationalLogVal_realification (p : Nat) [Fact (Nat.Prime p)]
    (u : (PadicAlgCl p)ˣ) :
    (((padicAlgClUnitRationalLogVal p u).toAdd : Rat) : Real) =
      (LeanFormal.IUT.padicAlgClUnitLogVal p u).toAdd := by
  rw [padicAlgClUnitRationalLogVal_apply, toAdd_ofAdd,
    padicAlgClUnitRationalLogValAux_cast]

/-- The rational value-group map of (Qbar_p)^x is onto Q at the level of the
additive rational value. -/
theorem padicAlgClUnitRationalLogVal_toAdd_surjective
    (p : Nat) [Fact (Nat.Prime p)] :
    Function.Surjective
      (fun u : (PadicAlgCl p)ˣ => (padicAlgClUnitRationalLogVal p u).toAdd) := by
  intro q
  have hq : ((q : Rat) : Real) ∈
      Set.range (fun u : (PadicAlgCl p)ˣ =>
        (LeanFormal.IUT.padicAlgClUnitLogVal p u).toAdd) := by
    rw [LeanFormal.IUT.padicAlgCl_unit_logVal_range_eq_rat]
    exact ⟨q, rfl⟩
  obtain ⟨u, hu⟩ := hq
  refine ⟨u, ?_⟩
  have h : (((padicAlgClUnitRationalLogVal p u).toAdd : Rat) : Real) = (q : Real) := by
    rw [padicAlgClUnitRationalLogVal_realification]
    exact hu
  exact Rat.cast_injective h

/-- The rational value-group map of (Qbar_p)^x is onto Q. -/
theorem padicAlgClUnitRationalLogVal_surjective (p : Nat) [Fact (Nat.Prime p)] :
    Function.Surjective (padicAlgClUnitRationalLogVal p) := by
  intro q
  obtain ⟨u, hu⟩ := padicAlgClUnitRationalLogVal_toAdd_surjective p q.toAdd
  refine ⟨u, ?_⟩
  rw [← ofAdd_toAdd q, ← hu]
  exact (padicAlgClUnitRationalLogVal_apply p u).symm

/-- The kernel of the rational value map is the norm-one units of
(Qbar_p)^x, i.e. its integral units. -/
theorem padicAlgClUnitRationalLogVal_eq_one_iff_norm
    (p : Nat) [Fact (Nat.Prime p)] (u : (PadicAlgCl p)ˣ) :
    padicAlgClUnitRationalLogVal p u = 1 ↔ ‖(u : PadicAlgCl p)‖ = 1 := by
  have hL : Real.log (p : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt))
  constructor
  · intro h
    have hq : padicAlgClUnitRationalLogValAux p u = 0 := by
      have h' := congrArg Multiplicative.toAdd h
      rwa [padicAlgClUnitRationalLogVal_apply, toAdd_ofAdd, toAdd_one] at h'
    have hpadic : (LeanFormal.IUT.padicAlgClUnitLogVal p u).toAdd = 0 := by
      rw [← padicAlgClUnitRationalLogValAux_cast, hq]
      norm_num
    have hdiv : Real.log ‖(u : PadicAlgCl p)‖ / Real.log (p : Real) = 0 := by
      have hneg : -(Real.log ‖(u : PadicAlgCl p)‖ / Real.log (p : Real)) = 0 := by
        rw [show (LeanFormal.IUT.padicAlgClUnitLogVal p u).toAdd =
            -(Real.log ‖(u : PadicAlgCl p)‖ / Real.log (p : Real)) from rfl] at hpadic
        exact hpadic
      exact neg_eq_zero.mp hneg
    have hlog : Real.log ‖(u : PadicAlgCl p)‖ = 0 :=
      (div_eq_zero_iff.mp hdiv).resolve_right hL
    rcases Real.log_eq_zero.mp hlog with h0 | h1 | hneg
    · exact absurd h0 (ne_of_gt (norm_pos_iff.mpr (Units.ne_zero u)))
    · exact h1
    · have hnn : (0 : Real) ≤ ‖(u : PadicAlgCl p)‖ := norm_nonneg _
      linarith
  · intro h
    apply Multiplicative.toAdd.injective
    rw [padicAlgClUnitRationalLogVal_apply, toAdd_ofAdd, toAdd_one]
    have hreal : ((padicAlgClUnitRationalLogValAux p u : Rat) : Real) = 0 := by
      rw [padicAlgClUnitRationalLogValAux_cast]
      change -(Real.log ‖(u : PadicAlgCl p)‖ / Real.log (p : Real)) = 0
      rw [h, Real.log_one]
      simp
    have hzero : padicAlgClUnitRationalLogValAux p u = 0 :=
      Rat.cast_eq_zero.mp hreal
    rw [hzero]

/-- The realified rational value image of (Qbar_p)^x is the rational line: the
realification of the constructed rational carrier matches the tree's proved
statement v((Qbar_p)^x) = Q up to the rational-valued identification. -/
theorem padicAlgClUnitRationalLogVal_range_realification
    (p : Nat) [Fact (Nat.Prime p)] :
    Set.range (fun u : (PadicAlgCl p)ˣ =>
        (((padicAlgClUnitRationalLogVal p u).toAdd : Rat) : Real)) =
      Set.range (fun q : Rat => (q : Real)) := by
  ext r
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(padicAlgClUnitRationalLogVal p u).toAdd, rfl⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨u, hu⟩ := padicAlgClUnitRationalLogVal_toAdd_surjective p q
    refine ⟨u, ?_⟩
    change (((padicAlgClUnitRationalLogVal p u).toAdd : Rat) : Real) = (q : Real)
    have hu' : (padicAlgClUnitRationalLogVal p u).toAdd = q := hu
    rw [hu']

/-- The reduced value kernel of the rational value map of (Qbar_p)^x. -/
def padicRationalValueKernel (p : Nat) [Fact (Nat.Prime p)] :
    LeanFormal.IUT.FrobenioidValueKernel ((PadicAlgCl p)ˣ) :=
  LeanFormal.IUT.K1K2Realization.frobenioidValueKernelOfValueMap
    (fun u => (((padicAlgClUnitRationalLogVal p u).toAdd : Rat) : Real))
    (fun u v => by
      rw [map_mul, toAdd_mul]
      push_cast
      ring)
    (by simp)
    id (fun _ => rfl)

/-- The realification of the rational value kernel is the realified rational
log value. -/
@[simp]
theorem padicRationalValueKernel_realification (p : Nat) [Fact (Nat.Prime p)]
    (u : (PadicAlgCl p)ˣ) :
    (padicRationalValueKernel p).realification u =
      (((padicAlgClUnitRationalLogVal p u).toAdd : Rat) : Real) :=
  rfl

/-- The realification image of the rational value kernel of (Qbar_p)^x is the
rational line. -/
theorem padicRationalValueKernel_realification_range
    (p : Nat) [Fact (Nat.Prime p)] :
    Set.range (padicRationalValueKernel p).realification =
      Set.range (fun q : Rat => (q : Real)) :=
  padicAlgClUnitRationalLogVal_range_realification p

/-! ## 2. The partial source vertical rational carrier over the actual data -/

/-- The integer value group embeds in the rational value group. -/
def intValueToRationalGroup : Multiplicative Int →* Multiplicative Rat :=
  MonoidHom.mk' (fun m => Multiplicative.ofAdd
      (((Multiplicative.toAdd m : Int)) : Rat))
    (by
      intro a b
      rw [← ofAdd_add]
      congr 1
      change ((Multiplicative.toAdd (a * b) : Int) : Rat) =
        ((Multiplicative.toAdd a : Int) : Rat) + ((Multiplicative.toAdd b : Int) : Rat)
      rw [toAdd_mul]
      push_cast
      ring)

/-- The integer value group divided by the ramification index embeds in the
rational value group: m |-> m/e. -/
def intValueToRationalGroupScaled (e : Nat) : Multiplicative Int →* Multiplicative Rat :=
  MonoidHom.mk' (fun m => Multiplicative.ofAdd
      ((((Multiplicative.toAdd m : Int)) : Rat) / (e : Rat)))
    (by
      intro a b
      rw [← ofAdd_add]
      congr 1
      change ((Multiplicative.toAdd (a * b) : Int) : Rat) / (e : Rat) =
        ((Multiplicative.toAdd a : Int) : Rat) / (e : Rat) +
          ((Multiplicative.toAdd b : Int) : Rat) / (e : Rat)
      rw [toAdd_mul]
      push_cast
      ring)

/-- The value-group inclusion of the actual completion units into the rational
carrier: the completion exponent divided by the actual ramification index. -/
noncomputable def completionValueToRational
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    (w.adicCompletion F')ˣ →* Multiplicative Rat :=
  (intValueToRationalGroupScaled (T.ramificationIndex w)).comp
    (completionValuationExponentMonoidHom (K := F') w)

/-- The value of a completion unit in the rational carrier. -/
theorem completionValueToRational_apply
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (x : (w.adicCompletion F')ˣ) :
    completionValueToRational T w x = Multiplicative.ofAdd
      ((completionValuationExponent w x : Rat) / (T.ramificationIndex w : Rat)) := by
  rw [completionValueToRational, MonoidHom.comp_apply,
    completionValuationExponentMonoidHom_apply]
  rfl

/-- The global-unit value-group inclusion into the rational carrier at the base
place: f |-> nu_v(f). -/
noncomputable def sourceValueToRational
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    Fˣ →* Multiplicative Rat :=
  intValueToRationalGroup.comp (finitePlaceValueMonoidHom (T.finitePlaceRestriction w))

/-- The rational value of a global unit at the base place. -/
theorem sourceValueToRational_apply
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (f : Fˣ) :
    sourceValueToRational T w f =
      Multiplicative.ofAdd (finitePlaceValueExponent (T.finitePlaceRestriction w) f : Rat) := by
  rw [sourceValueToRational, MonoidHom.comp_apply]
  rfl

/-- Compatibility of the completion and global rational values on the
phi-image: the normalized completion value of the image of a global unit is
its base-place value.  This uses the corrected cross-field ramification law. -/
theorem completionValueToRational_embedded
    {F' : Type u} [Field F'] [NumberField F']
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (w : HeightOneSpectrum (𝓞 F')) (f : Fˣ) :
    completionValueToRational T w
        (finitePlaceGlobalUnitValue (F := F') w (unitsMapOfRingHom T.fieldMap f)) =
      sourceValueToRational (F := F) T w f := by
  apply Multiplicative.toAdd.injective
  rw [completionValueToRational_apply, sourceValueToRational_apply, toAdd_ofAdd,
    toAdd_ofAdd]
  have hν := numberField_finitePlaceValueExponent_transport (F := F) (F' := F') T f w
  have he : (T.ramificationIndex w : Rat) ≠ 0 := by
    exact_mod_cast (ne_of_gt (T.ramificationIndex_pos w))
  rw [show completionValuationExponent w
        (finitePlaceGlobalUnitValue (F := F') w (unitsMapOfRingHom T.fieldMap f)) =
      finitePlaceValueExponent w (unitsMapOfRingHom T.fieldMap f) from
    finitePlaceGlobalUnitValue_exponent (F := F') w _]
  rw [hν]
  push_cast
  field_simp

/-- The completion value map has image the lattice (1/e_w) * Z in Q: in
particular it does not reach all of Q. -/
theorem completionValueToRational_range
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    Set.range (fun x : (w.adicCompletion F')ˣ =>
        (completionValueToRational T w x).toAdd) =
      Set.range (fun n : Int => (n : Rat) / (T.ramificationIndex w : Rat)) := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨completionValuationExponent w x, ?_⟩
    simp only [completionValueToRational_apply, toAdd_ofAdd]
  · rintro ⟨n, rfl⟩
    obtain ⟨x, hx⟩ := completionValuationExponent_surjective (K := F') w n
    refine ⟨x, ?_⟩
    simp only [completionValueToRational_apply, toAdd_ofAdd, hx]

/-! ## 3. The candidate rho_v normalization -/

/-- The log of the actual base residue cardinality, logPhi(pv) := log q_v. -/
noncomputable def sourceResidueLog
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) : Real :=
  Real.log ((finitePlaceResidueCardinality (F := F) (T.finitePlaceRestriction w) : Real))

/-- The actual relative residue degree, in real form: f_w = log q_w / log q_v. -/
noncomputable def relativeResidueDegree
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) : Real :=
  Real.log ((finitePlaceResidueCardinality (F := F') w : Real)) /
    sourceResidueLog (F := F) T w

/-- The candidate relative local degree [K_w:(F_mod)_v] = e_w * f_w from
actual ramification and residue data. -/
noncomputable def relativeLocalDegree
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) : Real :=
  (T.ramificationIndex w : Real) * relativeResidueDegree (F := F) T w

/-- The log of the base residue cardinality is positive. -/
theorem sourceResidueLog_pos
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    0 < sourceResidueLog (F := F) T w :=
  finitePlaceResidueCardinality_log_pos (F := F) (T.finitePlaceRestriction w)

/-- The relative residue degree is positive. -/
theorem relativeResidueDegree_pos
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    0 < relativeResidueDegree (F := F) T w :=
  div_pos (finitePlaceResidueCardinality_log_pos (F := F') w)
    (sourceResidueLog_pos (F := F) T w)

/-- The candidate relative local degree is positive. -/
theorem relativeLocalDegree_pos
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    0 < relativeLocalDegree (F := F) T w := by
  unfold relativeLocalDegree
  exact mul_pos (by exact_mod_cast T.ramificationIndex_pos w)
    (relativeResidueDegree_pos (F := F) T w)

/-- The relative residue degree recovers the upper residue logarithm from the
base one: f_w * log q_v = log q_w. -/
theorem relativeResidueDegree_mul_sourceResidueLog
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    relativeResidueDegree (F := F) T w * sourceResidueLog (F := F) T w =
      Real.log ((finitePlaceResidueCardinality (F := F') w : Real)) := by
  unfold relativeResidueDegree
  exact div_mul_cancel₀ _ (ne_of_gt (sourceResidueLog_pos (F := F) T w))

/-- The candidate rho_v normalization of IUT I, Example 3.5, (i):
r |-> (1/[K_w:(F_mod)_v]) * r * logPhi(pv), with [K_w:(F_mod)_v] = e_w * f_w
and logPhi(pv) = log q_v from the actual residue/ramification data. -/
noncomputable def candidateRhoNormalization
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    Multiplicative Rat →* Multiplicative Real :=
  MonoidHom.mk' (fun r => Multiplicative.ofAdd
      ((1 / relativeLocalDegree (F := F) T w) *
        ((r.toAdd : Real) * sourceResidueLog (F := F) T w)))
    (by
      intro a b
      rw [← ofAdd_add]
      congr 1
      rw [toAdd_mul]
      push_cast
      ring)

/-- The candidate normalization in coordinates. -/
theorem candidateRhoNormalization_apply
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (r : Rat) :
    candidateRhoNormalization (F := F) T w (Multiplicative.ofAdd r) =
      Multiplicative.ofAdd ((1 / relativeLocalDegree (F := F) T w) *
        ((r : Real) * sourceResidueLog (F := F) T w)) :=
  rfl

/-- The paper-shape value of the candidate on the base log-volume basis:
rho_v(logPhi(pv)) = log q_v / (e_w * f_w). -/
theorem candidateRhoNormalization_basis
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    (candidateRhoNormalization (F := F) T w (Multiplicative.ofAdd (1 : Rat))).toAdd =
      sourceResidueLog (F := F) T w / relativeLocalDegree (F := F) T w := by
  rw [candidateRhoNormalization_apply, toAdd_ofAdd]
  push_cast
  ring

/-- The candidate value of a base global-unit exponent: nu_v(f) * log q_v /
(e_w f_w). -/
theorem candidateRhoNormalization_sourceValue
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (f : Fˣ) :
    (candidateRhoNormalization (F := F) T w
        (sourceValueToRational (F := F) T w f)).toAdd =
      (finitePlaceValueExponent (T.finitePlaceRestriction w) f : Real) *
        sourceResidueLog (F := F) T w / relativeLocalDegree (F := F) T w := by
  rw [sourceValueToRational_apply, candidateRhoNormalization_apply, toAdd_ofAdd]
  push_cast
  ring

/-- Compatibility of the candidate normalization with the actual local value
kernel: the realified local degree of the phi-image is the [K_w:F_v]^2
multiple of the candidate normalization of the base exponent.  This is the
exact value-level identity available in the tree; the displayed square factor
is the normalization mismatch that the missing source rho_v isomorphism has
to resolve. -/
theorem finitePlaceUnitValueKernel_realification_eq_candidateRho
    {F' : Type u} [Field F'] [NumberField F']
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (w : HeightOneSpectrum (𝓞 F')) (f : Fˣ) :
    (finitePlaceUnitValueKernel (F := F') w).realification
        (finitePlaceGlobalUnitValue (F := F') w (unitsMapOfRingHom T.fieldMap f)) =
      -(relativeLocalDegree (F := F) T w) ^ 2 *
        (candidateRhoNormalization (F := F) T w
          (sourceValueToRational (F := F) T w f)).toAdd := by
  rw [finitePlaceUnitValueKernel_realification_globalUnit,
    numberFieldFiniteLocalValueData_deltaAdd,
    candidateRhoNormalization_sourceValue]
  have hν := numberField_finitePlaceValueExponent_transport (F := F) (F' := F') T f w
  rw [hν]
  have hbase := relativeResidueDegree_mul_sourceResidueLog (F := F) T w
  have hrel : relativeLocalDegree (F := F) T w =
      (T.ramificationIndex w : Real) * relativeResidueDegree (F := F) T w := rfl
  rw [hrel, ← hbase]
  push_cast
  field_simp

/-! ## 3'. The actual source log-volume normalization `rho_v`

The candidate normalization of section 3 is not the normalization used by the
actual local log-volume, and the square factor `(e_w f_w)^2` displayed in
`finitePlaceUnitValueKernel_realification_eq_candidateRho` is a real
normalization mismatch, not a bookkeeping artifact.  The section constructs
the actual normalization and proves that it is forced.

The actual normalization `sourceRhoLogVolume` maps the rational exponent `r`
to `[K_w:(F_mod)_v] * log q_v * r = e_w * r * log q_w`.  It satisfies the
three exact squares

* `sourceRhoLogVolume_completionValue`: through the actual completion value
  map it is the actual local log-volume `x |-> nu_w(x) * log q_w`;
* `sourceRhoLogVolume_sourceValue`: through the actual global-unit value map
  (at the base place) it is the same local log-volume of the phi-image, by the
  corrected cross-field ramification law;
* `sourceRhoLogVolume_eq_neg_unitValueKernel`: it is the negative of the
  realified actual local value kernel on the phi-image.

It differs from the candidate by exactly `(e_w f_w)^2`
(`sourceRhoLogVolume_eq_relativeLocalDegree_sq_mul_candidate`), and it is the
unique monoid homomorphism with the completion square
(`sourceRhoLogVolume_unique`).  Consequently the candidate satisfies that
square if and only if `[K_w:(F_mod)_v] = 1`
(`candidateRhoNormalization_completionValue_iff`): the factor
`1/[K_w:(F_mod)_v]` of IUT I, Example 3.5, (i) must be replaced by the factor
`[K_w:(F_mod)_v]` itself (equivalently, the base log-volume `log q_v` must be
replaced by the upper log-volume `log q_w = f_w log q_v`, after transporting
by `e_w`). -/

/-- **The actual source log-volume normalization `rho_v`** at the upper place
`w`: the rational exponent `r` is mapped to
`[K_w:(F_mod)_v] * log q_v * r = e_w * r * log q_w`.  This is the
normalization for which the square with the actual completion value map and
the actual local log-volume commutes (see
`sourceRhoLogVolume_completionValue`), and the candidate normalization of
section 3 is this normalization divided by `(e_w f_w)^2`. -/
noncomputable def sourceRhoLogVolume
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    Multiplicative Rat →* Multiplicative Real :=
  MonoidHom.mk' (fun r => Multiplicative.ofAdd
      (relativeLocalDegree (F := F) T w * sourceResidueLog (F := F) T w *
        ((r.toAdd : Rat) : Real)))
    (by
      intro a b
      rw [← ofAdd_add]
      congr 1
      rw [toAdd_mul]
      push_cast
      ring)

/-- The actual normalization in coordinates. -/
theorem sourceRhoLogVolume_apply
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (r : Rat) :
    sourceRhoLogVolume (F := F) T w (Multiplicative.ofAdd r) =
      Multiplicative.ofAdd (relativeLocalDegree (F := F) T w *
        sourceResidueLog (F := F) T w * (r : Real)) :=
  rfl

/-- The value of the actual normalization on the source log-volume generator:
`[K_w:(F_mod)_v] * log q_v`. -/
theorem sourceRhoLogVolume_one
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    (sourceRhoLogVolume (F := F) T w (Multiplicative.ofAdd (1 : Rat))).toAdd =
      relativeLocalDegree (F := F) T w * sourceResidueLog (F := F) T w := by
  rw [sourceRhoLogVolume_apply, toAdd_ofAdd]
  push_cast
  ring

/-- The product of the relative local degree and the base residue logarithm is
the ramification index times the upper residue logarithm:
`e_w f_w log q_v = e_w log q_w`. -/
theorem relativeLocalDegree_mul_sourceResidueLog_eq
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    relativeLocalDegree (F := F) T w * sourceResidueLog (F := F) T w =
      (T.ramificationIndex w : Real) *
        Real.log ((finitePlaceResidueCardinality (F := F') w : ℕ) : Real) := by
  unfold relativeLocalDegree relativeResidueDegree
  have hne : sourceResidueLog (F := F) T w ≠ 0 :=
    ne_of_gt (sourceResidueLog_pos (F := F) T w)
  field_simp

/-- **The exact square with the actual completion value map.**  The source
normalization composed with the actual completion value map is the actual
local log-volume `x |-> nu_w(x) * log q_w`. -/
theorem sourceRhoLogVolume_completionValue
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (x : (w.adicCompletion F')ˣ) :
    sourceRhoLogVolume (F := F) T w (completionValueToRational (F := F) T w x) =
      Multiplicative.ofAdd ((completionValuationExponent w x : Real) *
        Real.log ((finitePlaceResidueCardinality (F := F') w : ℕ) : Real)) := by
  rw [completionValueToRational_apply, sourceRhoLogVolume_apply]
  congr 1
  rw [relativeLocalDegree_mul_sourceResidueLog_eq]
  have he : (T.ramificationIndex w : Real) ≠ 0 := by
    exact_mod_cast ne_of_gt (T.ramificationIndex_pos w)
  push_cast
  field_simp

/-- **The square with the transport (global units).**  The source normalization
evaluated at the base-place value of a global unit is the actual local
log-volume of its phi-image, by the corrected cross-field ramification law. -/
theorem sourceRhoLogVolume_sourceValue
    {F' : Type u} [Field F'] [NumberField F']
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (w : HeightOneSpectrum (𝓞 F'))
    (f : Fˣ) :
    sourceRhoLogVolume (F := F) T w (sourceValueToRational (F := F) T w f) =
      Multiplicative.ofAdd
        ((completionValuationExponent w
            (finitePlaceGlobalUnitValue (F := F') w
              (unitsMapOfRingHom T.fieldMap f)) : Real) *
          Real.log ((finitePlaceResidueCardinality (F := F') w : ℕ) : Real)) := by
  have hval : sourceRhoLogVolume (F := F) T w (sourceValueToRational (F := F) T w f) =
      Multiplicative.ofAdd ((finitePlaceValueExponent (T.finitePlaceRestriction w) f : Real) *
        (relativeLocalDegree (F := F) T w * sourceResidueLog (F := F) T w)) := by
    rw [sourceValueToRational_apply, sourceRhoLogVolume_apply]
    push_cast
    ring
  rw [hval]
  congr 1
  rw [relativeLocalDegree_mul_sourceResidueLog_eq,
    finitePlaceGlobalUnitValue_exponent (F := F') w (unitsMapOfRingHom T.fieldMap f),
    numberField_finitePlaceValueExponent_transport (F := F) (F' := F') T f w]
  push_cast
  ring

/-- **The square with the actual local value kernel.**  On the phi-image of a
global unit, the realified actual local value kernel is the negative of the
actual source normalization of the base-place value.  This is the readback
identity with no residual normalization factor. -/
theorem sourceRhoLogVolume_eq_neg_unitValueKernel
    {F' : Type u} [Field F'] [NumberField F']
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (w : HeightOneSpectrum (𝓞 F')) (f : Fˣ) :
    (finitePlaceUnitValueKernel (F := F') w).realification
        (finitePlaceGlobalUnitValue (F := F') w (unitsMapOfRingHom T.fieldMap f)) =
      -(sourceRhoLogVolume (F := F) T w (sourceValueToRational (F := F) T w f)).toAdd := by
  rw [sourceRhoLogVolume_sourceValue, toAdd_ofAdd,
    finitePlaceUnitValueKernel_realification, neg_mul]

/-- **The exact normalization correction.**  The actual source normalization is
the candidate normalization of section 3 multiplied by the square of the
relative local degree `[K_w:(F_mod)_v] = e_w f_w`. -/
theorem sourceRhoLogVolume_eq_relativeLocalDegree_sq_mul_candidate
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (r : Rat) :
    (sourceRhoLogVolume (F := F) T w (Multiplicative.ofAdd r)).toAdd =
      (relativeLocalDegree (F := F) T w) ^ 2 *
        (candidateRhoNormalization (F := F) T w (Multiplicative.ofAdd r)).toAdd := by
  rw [sourceRhoLogVolume_apply, toAdd_ofAdd,
    candidateRhoNormalization_apply, toAdd_ofAdd]
  have hpos := relativeLocalDegree_pos (F := F) T w
  have hne : relativeLocalDegree (F := F) T w ≠ 0 := ne_of_gt hpos
  field_simp

/-- The value group of the completion units surjects onto the lattice
`(1/e_w) Z` of rational values. -/
theorem completionValueToRational_toAdd_surjective_on_lattice
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (n : Int) :
    ∃ x : (w.adicCompletion F')ˣ,
      (completionValueToRational (F := F) T w x).toAdd =
        (n : Rat) / (T.ramificationIndex w : Rat) := by
  obtain ⟨x, hx⟩ := completionValuationExponent_surjective (K := F') w n
  exact ⟨x, by rw [completionValueToRational_apply, toAdd_ofAdd, hx]⟩

/-- **Uniqueness of the source normalization.**  Any monoid homomorphism from
the rational value group to the real line whose composite with the actual
completion value map is the actual local log-volume is the source
normalization `sourceRhoLogVolume`.  The proof uses only that the value group
of the completion is the lattice `(1/e_w) Z`, which generates `Q` by
divisibility, and that the real line is torsion-free. -/
theorem sourceRhoLogVolume_unique
    {F' : Type u} [Field F'] [NumberField F']
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (w : HeightOneSpectrum (𝓞 F'))
    (ρ : Multiplicative Rat →* Multiplicative Real)
    (hρ : ∀ x : (w.adicCompletion F')ˣ,
      ρ (completionValueToRational (F := F) T w x) =
        Multiplicative.ofAdd ((completionValuationExponent w x : Real) *
          Real.log ((finitePlaceResidueCardinality (F := F') w : ℕ) : Real))) :
    ρ = sourceRhoLogVolume (F := F) T w := by
  apply MonoidHom.ext
  intro m
  set r : Rat := m.toAdd with hr
  set n : ℕ := T.ramificationIndex w * r.den with hn
  have hden : 0 < r.den := Rat.pos r
  have hnpos : 0 < n := Nat.mul_pos (T.ramificationIndex_pos w) hden
  have hnge : (n : ℚ) ≠ 0 := by
    exact_mod_cast ne_of_gt hnpos
  -- a completion unit whose rational value is `n * r`
  obtain ⟨x, hx⟩ := completionValueToRational_toAdd_surjective_on_lattice
    (F := F) (F' := F') T w
    ((T.ramificationIndex w : Int) * (T.ramificationIndex w : Int) * r.num)
  have hdenr : (r.den : Rat) * r = (r.num : Rat) := by
    have h := Rat.num_div_den r
    have hden' : (r.den : Rat) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hden
    field_simp at h
    linarith
  have hqr : (n : Rat) * r =
      (((T.ramificationIndex w : Int) * (T.ramificationIndex w : Int) * r.num : Int) : Rat) /
        (T.ramificationIndex w : Rat) := by
    have he' : (T.ramificationIndex w : Rat) ≠ 0 := by
      exact_mod_cast ne_of_gt (T.ramificationIndex_pos w)
    rw [hn]
    push_cast
    rw [mul_assoc, hdenr]
    field_simp
  have hxval : completionValueToRational (F := F) T w x =
      Multiplicative.ofAdd ((n : Rat) * r) := by
    apply Multiplicative.toAdd.injective
    rw [hx, toAdd_ofAdd]
    exact hqr.symm
  have hmr : m = Multiplicative.ofAdd r := rfl
  have hpow : m ^ n = completionValueToRational (F := F) T w x := by
    rw [hxval, hmr, ← ofAdd_nsmul, nsmul_eq_mul]
  -- both sides take the same value at `m ^ n`
  have hρpow : ρ (m ^ n) = Multiplicative.ofAdd
      ((completionValuationExponent w x : Real) *
        Real.log ((finitePlaceResidueCardinality (F := F') w : ℕ) : Real)) := by
    rw [hpow]
    exact hρ x
  have hsrcpow : sourceRhoLogVolume (F := F) T w (m ^ n) = Multiplicative.ofAdd
      ((completionValuationExponent w x : Real) *
        Real.log ((finitePlaceResidueCardinality (F := F') w : ℕ) : Real)) := by
    rw [hpow]
    exact sourceRhoLogVolume_completionValue (F := F) T w x
  -- realified: `n * rho(m) = n * rho_src(m)` with `n ≠ 0`
  have htoAdd : ((ρ m).toAdd) = ((sourceRhoLogVolume (F := F) T w m).toAdd) := by
    have h1 := congrArg Multiplicative.toAdd hρpow
    have h2 := congrArg Multiplicative.toAdd hsrcpow
    rw [MonoidHom.map_pow ρ m n, toAdd_pow, nsmul_eq_mul] at h1
    rw [MonoidHom.map_pow (sourceRhoLogVolume (F := F) T w) m n,
      toAdd_pow, nsmul_eq_mul] at h2
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hnpos
    apply mul_left_cancel₀ hnR
    rw [h1, h2]
  exact Multiplicative.toAdd.injective htoAdd

/-- **The candidate normalization is not the source normalization.**  The
candidate `r |-> (1/[K_w:(F_mod)_v]) * r * log q_v` reproduces the actual local
log-volume through the completion value map if and only if the relative local
degree is one.  In particular the factor `1/[K_w:(F_mod)_v]` of the candidate
is the wrong normalization as soon as `[K_w:(F_mod)_v] ≠ 1`; the correct
factor is `[K_w:(F_mod)_v]` itself, i.e. the candidate must be multiplied by
`(e_w f_w)^2`. -/
theorem candidateRhoNormalization_completionValue_iff
    {F' : Type u} [Field F'] [NumberField F']
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (w : HeightOneSpectrum (𝓞 F')) :
    (∀ x : (w.adicCompletion F')ˣ,
        (candidateRhoNormalization (F := F) T w
          (completionValueToRational (F := F) T w x)).toAdd =
          (completionValuationExponent w x : Real) *
            Real.log ((finitePlaceResidueCardinality (F := F') w : ℕ) : Real)) ↔
      relativeLocalDegree (F := F) T w = 1 := by
  have hdeg : 0 < relativeLocalDegree (F := F) T w := relativeLocalDegree_pos (F := F) T w
  have he : (T.ramificationIndex w : Real) ≠ 0 := by
    exact_mod_cast ne_of_gt (T.ramificationIndex_pos w)
  have hlogw : Real.log ((finitePlaceResidueCardinality (F := F') w : ℕ) : Real) ≠ 0 :=
    finitePlaceResidueCardinality_log_ne_zero (F := F') w
  have hA : (sourceRhoLogVolume (F := F) T w (Multiplicative.ofAdd (1 : Rat))).toAdd ≠ 0 := by
    rw [sourceRhoLogVolume_one, relativeLocalDegree_mul_sourceResidueLog_eq]
    exact mul_ne_zero he hlogw
  constructor
  · intro h
    set A : Real := (sourceRhoLogVolume (F := F) T w (Multiplicative.ofAdd (1 : Rat))).toAdd
      with hAdef
    have hA : A ≠ 0 := by
      rw [hAdef, sourceRhoLogVolume_one, relativeLocalDegree_mul_sourceResidueLog_eq]
      exact mul_ne_zero he hlogw
    have huniq := sourceRhoLogVolume_unique (F := F) (F' := F') T w
      (candidateRhoNormalization (F := F) T w) h
    -- `A = d^2 * A` with `A ≠ 0` forces `d^2 = 1`, hence `d = 1` by positivity
    have hrel' : A = (relativeLocalDegree (F := F) T w) ^ 2 * A := by
      have h' := sourceRhoLogVolume_eq_relativeLocalDegree_sq_mul_candidate
        (F := F) T w (1 : Rat)
      rw [huniq, ← hAdef] at h'
      exact h'
    have hsq : (relativeLocalDegree (F := F) T w) ^ 2 = 1 := by
      have h2 : (relativeLocalDegree (F := F) T w) ^ 2 * A = 1 * A := by
        calc (relativeLocalDegree (F := F) T w) ^ 2 * A = A := hrel'.symm
          _ = 1 * A := (one_mul A).symm
      exact mul_right_cancel₀ hA h2
    nlinarith [hsq, hdeg]
  · intro hd
    intro x
    have hcand : candidateRhoNormalization (F := F) T w
        (completionValueToRational (F := F) T w x) =
        sourceRhoLogVolume (F := F) T w (completionValueToRational (F := F) T w x) := by
      apply Multiplicative.toAdd.injective
      have hrel := sourceRhoLogVolume_eq_relativeLocalDegree_sq_mul_candidate
        (F := F) T w ((completionValueToRational (F := F) T w x).toAdd)
      rw [hd, ofAdd_toAdd] at hrel
      norm_num at hrel
      rw [hrel]
    rw [hcand, sourceRhoLogVolume_completionValue, toAdd_ofAdd]

/-! ## 3''. Value-group identification through an actual embedding

The actual embedding `K_w -> (Qbar_p)^x` is supplied by the universal property
of the algebraic closure (`IsAlgClosed.lift`, constructed unconditionally for
the actual completion in `Example36CompletionIntoAlgCl` and
`Example36CompletionEmbeddingActual`; this module is below those files in the
import graph and therefore only consumes an abstract embedding datum).  The
remaining analytic input is the normalized-value identity: the rational value
of the image unit is the completion exponent divided by the ramification
index.  Under that identity the source value group is identified with the
rational value group of `(Qbar_p)^x`, with the exact image lattice, kernel and
norm form. -/

/-- The unit map induced by a ring homomorphism into `PadicAlgCl p`. -/
def completionUnitMapIntoPadicAlgCl (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] (φ : F' →+* PadicAlgCl p) : F'ˣ →* (PadicAlgCl p)ˣ :=
  Units.map φ.toMonoidHom

@[simp]
theorem completionUnitMapIntoPadicAlgCl_apply_coe (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] (φ : F' →+* PadicAlgCl p) (x : F'ˣ) :
    ((completionUnitMapIntoPadicAlgCl p φ x : (PadicAlgCl p)ˣ) : PadicAlgCl p) =
      φ (x : F') :=
  rfl

/-- **An actual embedding datum for the completion.**  It consists of an
injective ring homomorphism of the local field `K_w = w.adicCompletion F'`
into `PadicAlgCl p` (supplied by the universal property of the algebraic
closure) together with the normalized-value identity.  The identity is the
exact normalization hypothesis under which the source value group is
identified with the rational value group; it is equivalent to the log-norm
identity `||φ x|| = p^(-(nu_w(x)/e_w))` (see
`completionValueViaEmbedding_normalizedValue_iff_norm`). -/
structure CompletionValueEmbeddingDatum (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) where
  /-- The embedding of the local field into the algebraic closure of `Q_p`. -/
  embedding : w.adicCompletion F' →+* PadicAlgCl p
  /-- The embedding is injective. -/
  injective : Function.Injective embedding
  /-- The normalized-value identity: the rational value of the image unit is
  the completion exponent divided by the ramification index `e_w`. -/
  normalizedValue : ∀ x : (w.adicCompletion F')ˣ,
    (padicAlgClUnitRationalLogVal p
        (completionUnitMapIntoPadicAlgCl p embedding x)).toAdd =
      (completionValuationExponent w x : Rat) / (T.ramificationIndex w : Rat)

/-- The rational value map of the completion units induced by an embedding
datum: the rational value of the image unit in the rational value group of
`(Qbar_p)^x`. -/
noncomputable def completionValueViaEmbedding (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    {T : PlaceLocalizationTransport D D'} {w : HeightOneSpectrum (𝓞 F')}
    (D : CompletionValueEmbeddingDatum (F := F) p T w) :
    (w.adicCompletion F')ˣ →* Multiplicative Rat :=
  (padicAlgClUnitRationalLogVal p).comp
    (completionUnitMapIntoPadicAlgCl p D.embedding)

/-- The embedding-induced rational value in coordinates. -/
theorem completionValueViaEmbedding_apply (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    {T : PlaceLocalizationTransport D D'} {w : HeightOneSpectrum (𝓞 F')}
    (D : CompletionValueEmbeddingDatum (F := F) p T w)
    (x : (w.adicCompletion F')ˣ) :
    completionValueViaEmbedding (F := F) p D x =
      padicAlgClUnitRationalLogVal p
        (completionUnitMapIntoPadicAlgCl p D.embedding x) :=
  rfl

/-- **The embedding-induced value map is the intrinsic completion value map.**
Under the normalized-value identity the rational value of the image unit is
exactly the completion exponent divided by the ramification index, i.e. the
value group of the completion is identified with the lattice `(1/e_w) Z`
inside the rational value group of `(Qbar_p)^x`. -/
theorem completionValueViaEmbedding_eq_completionValueToRational
    (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    {T : PlaceLocalizationTransport D D'} {w : HeightOneSpectrum (𝓞 F')}
    (D : CompletionValueEmbeddingDatum (F := F) p T w) :
    completionValueViaEmbedding (F := F) p D = completionValueToRational (F := F) T w := by
  apply MonoidHom.ext
  intro x
  apply Multiplicative.toAdd.injective
  rw [completionValueViaEmbedding_apply, completionValueToRational_apply, toAdd_ofAdd]
  exact D.normalizedValue x

/-- **The image of the identified source value group** is the lattice
`(1/e_w) Z`, expressed in the rational value group of `(Qbar_p)^x`. -/
theorem completionValueViaEmbedding_range (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    {T : PlaceLocalizationTransport D D'} {w : HeightOneSpectrum (𝓞 F')}
    (D : CompletionValueEmbeddingDatum (F := F) p T w) :
    Set.range (fun x : (w.adicCompletion F')ˣ =>
        (completionValueViaEmbedding (F := F) p D x).toAdd) =
      Set.range (fun n : Int => (n : Rat) / (T.ramificationIndex w : Rat)) := by
  rw [completionValueViaEmbedding_eq_completionValueToRational]
  exact completionValueToRational_range (F := F) T w

/-- **The kernel of the identified source value group** is the group
`O_w^×` of integral units of the completion. -/
theorem completionValueViaEmbedding_eq_one_iff_mem_integralUnits
    (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    {T : PlaceLocalizationTransport D D'} {w : HeightOneSpectrum (𝓞 F')}
    (D : CompletionValueEmbeddingDatum (F := F) p T w)
    (x : (w.adicCompletion F')ˣ) :
    completionValueViaEmbedding (F := F) p D x = 1 ↔
      x ∈ (w.adicCompletionIntegers F').units := by
  have hmap : completionValueViaEmbedding (F := F) p D x =
      completionValueToRational (F := F) T w x := by
    rw [completionValueViaEmbedding_eq_completionValueToRational]
  rw [hmap, completionValueToRational_apply, ofAdd_eq_one]
  have he : (T.ramificationIndex w : Rat) ≠ 0 := by
    exact_mod_cast ne_of_gt (T.ramificationIndex_pos w)
  constructor
  · intro h
    have hzero : (completionValuationExponent w x : Rat) = 0 := by
      have h' := h
      field_simp at h'
      simpa using h'
    have hz : completionValuationExponent w x = 0 := by
      exact_mod_cast hzero
    rwa [completionValuationExponent_eq_zero_iff_mem_integralUnits] at hz
  · intro h
    have hz : completionValuationExponent w x = 0 :=
      (completionValuationExponent_eq_zero_iff_mem_integralUnits w x).mpr h
    rw [hz]
    simp

/-- **The norm form of the normalized-value identity.**  Under the embedding
datum, the norm of the image unit is `p^(-(nu_w(x)/e_w))`, matching the
tree's convention `padicAlgClUnitLogVal = -log_p ||·||`. -/
theorem completionValueViaEmbedding_norm (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    {T : PlaceLocalizationTransport D D'} {w : HeightOneSpectrum (𝓞 F')}
    (D : CompletionValueEmbeddingDatum (F := F) p T w)
    (x : (w.adicCompletion F')ˣ) :
    ‖D.embedding (x : w.adicCompletion F')‖ =
      (p : Real) ^ (-((completionValuationExponent w x : Real) /
        (T.ramificationIndex w : Real))) := by
  have hp0 : (0 : Real) < (p : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hL : Real.log (p : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt))
  set u : (PadicAlgCl p)ˣ := completionUnitMapIntoPadicAlgCl p D.embedding x with hu
  have hcoe : (u : PadicAlgCl p) = D.embedding (x : w.adicCompletion F') := rfl
  obtain ⟨q, hq⟩ := padicAlgCl_norm_eq_rpow_rat p (u : PadicAlgCl p) (Units.ne_zero u)
  have h1 : ((padicAlgClUnitRationalLogVal p u).toAdd : Real) =
      -(Real.log ‖(u : PadicAlgCl p)‖ / Real.log (p : Real)) :=
    padicAlgClUnitRationalLogVal_realification p u
  have h2 : Real.log ‖(u : PadicAlgCl p)‖ = (q : Real) * Real.log (p : Real) := by
    rw [hq, Real.log_rpow hp0]
  have hq' : ((padicAlgClUnitRationalLogVal p u).toAdd : Rat) = -q := by
    have hcast : (((padicAlgClUnitRationalLogVal p u).toAdd : Rat) : Real) =
        ((-q : Rat) : Real) := by
      push_cast
      rw [h1, h2]
      field_simp
    exact Rat.cast_injective hcast
  have hqval : q = -(padicAlgClUnitRationalLogVal p u).toAdd := by linarith
  rw [← hcoe, hq, hqval, D.normalizedValue x]
  congr 1
  push_cast
  try ring

/-- **The normalized-value identity is exactly the log-norm identity.**  The
value form used in `CompletionValueEmbeddingDatum` and the norm form
`||φ x|| = p^(-(nu_w(x)/e_w))` are equivalent. -/
theorem completionValueViaEmbedding_normalizedValue_iff_norm
    (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    {T : PlaceLocalizationTransport D D'} {w : HeightOneSpectrum (𝓞 F')}
    (φ : w.adicCompletion F' →+* PadicAlgCl p) :
    (∀ x : (w.adicCompletion F')ˣ,
        (padicAlgClUnitRationalLogVal p
            (completionUnitMapIntoPadicAlgCl p φ x)).toAdd =
          (completionValuationExponent w x : Rat) / (T.ramificationIndex w : Rat)) ↔
      (∀ x : (w.adicCompletion F')ˣ,
        ‖φ (x : w.adicCompletion F')‖ =
          (p : Real) ^ (-((completionValuationExponent w x : Real) /
            (T.ramificationIndex w : Real)))) := by
  have hp0 : (0 : Real) < (p : Real) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hL : Real.log (p : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (Fact.out : Nat.Prime p).one_lt))
  constructor
  · intro h x
    set u : (PadicAlgCl p)ˣ := completionUnitMapIntoPadicAlgCl p φ x with hu
    obtain ⟨q, hq⟩ := padicAlgCl_norm_eq_rpow_rat p (u : PadicAlgCl p) (Units.ne_zero u)
    have h1 : ((padicAlgClUnitRationalLogVal p u).toAdd : Real) =
        -(Real.log ‖(u : PadicAlgCl p)‖ / Real.log (p : Real)) :=
      padicAlgClUnitRationalLogVal_realification p u
    have h2 : Real.log ‖(u : PadicAlgCl p)‖ = (q : Real) * Real.log (p : Real) := by
      rw [hq, Real.log_rpow hp0]
    have hq' : ((padicAlgClUnitRationalLogVal p u).toAdd : Rat) = -q := by
      have hcast : (((padicAlgClUnitRationalLogVal p u).toAdd : Rat) : Real) =
          ((-q : Rat) : Real) := by
        push_cast
        rw [h1, h2]
        field_simp
      exact Rat.cast_injective hcast
    have hqval : q = -(padicAlgClUnitRationalLogVal p u).toAdd := by linarith
    have hcoe : (u : PadicAlgCl p) = φ (x : w.adicCompletion F') := rfl
    rw [← hcoe, hq, hqval, h x]
    congr 1
    push_cast
    try ring
  · intro h x
    have hnorm := h x
    set u : (PadicAlgCl p)ˣ := completionUnitMapIntoPadicAlgCl p φ x with hu
    have hcoe : (u : PadicAlgCl p) = φ (x : w.adicCompletion F') := rfl
    have hreal := padicAlgClUnitRationalLogVal_realification p u
    have hnormu : ‖(u : PadicAlgCl p)‖ = ‖φ (x : w.adicCompletion F')‖ := by rw [hcoe]
    have hlog : Real.log ‖(u : PadicAlgCl p)‖ =
        (-((completionValuationExponent w x : Real) /
          (T.ramificationIndex w : Real))) * Real.log (p : Real) := by
      rw [hnormu, hnorm, Real.log_rpow hp0]
      try ring
    have htoAddR : ((padicAlgClUnitRationalLogVal p u).toAdd : Real) =
        (completionValuationExponent w x : Real) / (T.ramificationIndex w : Real) := by
      rw [hreal]
      change -(Real.log ‖(u : PadicAlgCl p)‖ / Real.log (p : Real)) = _
      rw [hlog]
      field_simp
    have hcast : ((padicAlgClUnitRationalLogVal p u).toAdd : Rat) =
        ((completionValuationExponent w x : Rat) / (T.ramificationIndex w : Rat)) := by
      apply Rat.cast_injective (α := Real)
      push_cast
      exact htoAddR
    exact hcast

/-- **Uniqueness of the value-group exponent.**  Every completion unit has a
unique integer exponent with rational value `n/e_w` in the identified source
value group; this is the identification of the value group of the completion
with `Z` through the actual embedding. -/
theorem completionValueViaEmbedding_existsUnique_exponent
    (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] [NumberField F']
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    {T : PlaceLocalizationTransport D D'} {w : HeightOneSpectrum (𝓞 F')}
    (D : CompletionValueEmbeddingDatum (F := F) p T w)
    (x : (w.adicCompletion F')ˣ) :
    ∃! n : Int, completionValueViaEmbedding (F := F) p D x =
      Multiplicative.ofAdd ((n : Rat) / (T.ramificationIndex w : Rat)) := by
  have hrange := completionValueViaEmbedding_range (F := F) p D
  have hmem : (completionValueViaEmbedding (F := F) p D x).toAdd ∈
      Set.range (fun n : Int => (n : Rat) / (T.ramificationIndex w : Rat)) := by
    rw [← hrange]
    exact ⟨x, rfl⟩
  obtain ⟨n, hn⟩ := hmem
  have hn' : (n : Rat) / (T.ramificationIndex w : Rat) =
      (completionValueViaEmbedding (F := F) p D x).toAdd := hn
  refine ⟨n, ?_, ?_⟩
  · apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, hn']
  · intro m hm
    have hm' : ((m : Rat) / (T.ramificationIndex w : Rat)) =
        (completionValueViaEmbedding (F := F) p D x).toAdd := by
      rw [hm, toAdd_ofAdd]
    rw [← hn'] at hm'
    have he : (T.ramificationIndex w : Rat) ≠ 0 := by
      exact_mod_cast ne_of_gt (T.ramificationIndex_pos w)
    have hnm : (n : Rat) = (m : Rat) := by
      field_simp at hm'
      exact hm'.symm
    exact Int.cast_injective hnm.symm

/-- **Naturality of the identified source value.**  On the phi-image of a
global unit, the embedding-induced rational value is the base-place value of
the global unit; the identification is therefore compatible with the place
transport. -/
theorem completionValueViaEmbedding_sourceValue (p : Nat) [Fact (Nat.Prime p)]
    {F' : Type u} [Field F'] [NumberField F']
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (w : HeightOneSpectrum (𝓞 F'))
    (D : CompletionValueEmbeddingDatum (F := F) p T w) (f : Fˣ) :
    completionValueViaEmbedding (F := F) p D
        (finitePlaceGlobalUnitValue (F := F') w (unitsMapOfRingHom T.fieldMap f)) =
      sourceValueToRational (F := F) T w f := by
  rw [completionValueViaEmbedding_eq_completionValueToRational]
  exact completionValueToRational_embedded (F := F) T w f

/-! ## 4. Partial vertical rational carrier data and the frozen missing components -/

/-- The source vertical rational carrier assembled from the actual data: the
rational value group `Q`, the global-unit value map, the normalized completion
value map, the actual source log-volume normalization `rho_v` with its exact
squares (completion value map, base log-volume generator, actual local value
kernel).  The value-group identification through an actual completion
embedding is provided separately, conditionally on a `CompletionValueEmbeddingDatum`
(this module is below the embedding files in the import graph); the embedding
and its normalized-value identity are not assumed here. -/
structure SourceVerticalRationalCarrierData
    {F' : Type u} [Field F'] [NumberField F']
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (w : HeightOneSpectrum (𝓞 F')) where
  /-- The global-unit value map into the rational value group. -/
  globalValue : Fˣ →* Multiplicative Rat
  /-- The normalized completion value map into the rational value group. -/
  completionValue : (w.adicCompletion F')ˣ →* Multiplicative Rat
  /-- Compatibility on the phi-image of global units. -/
  global_completion_value : ∀ f : Fˣ,
    completionValue (finitePlaceGlobalUnitValue (F := F') w
      (unitsMapOfRingHom T.fieldMap f)) = globalValue f
  /-- The actual source log-volume normalization `rho_v`. -/
  rhoNormalization : Multiplicative Rat →* Multiplicative Real
  /-- The value of `rho_v` on the source log-volume generator:
  `[K_w:(F_mod)_v] * log q_v`. -/
  rho_basis : (rhoNormalization (Multiplicative.ofAdd (1 : Rat))).toAdd =
    relativeLocalDegree (F := F) T w * sourceResidueLog (F := F) T w
  /-- The exact square with the completion value map: the local log-volume
  `x |-> nu_w(x) * log q_w`. -/
  rho_completionValue : ∀ x : (w.adicCompletion F')ˣ,
    rhoNormalization (completionValue x) = Multiplicative.ofAdd
      ((completionValuationExponent w x : Real) *
        Real.log ((finitePlaceResidueCardinality (F := F') w : ℕ) : Real))
  /-- The exact readback of the actual local value kernel on the phi-image of a
  global unit, with no residual normalization factor. -/
  valueKernel_readback : ∀ f : Fˣ,
    (finitePlaceUnitValueKernel (F := F') w).realification
        (finitePlaceGlobalUnitValue (F := F') w (unitsMapOfRingHom T.fieldMap f)) =
      -(rhoNormalization (globalValue f)).toAdd

/-- The source vertical rational carrier data, filled by the actual maps and
the actual (corrected) source normalization proved in this module. -/
noncomputable def sourceVerticalRationalCarrierData
    {F' : Type u} [Field F'] [NumberField F']
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (w : HeightOneSpectrum (𝓞 F')) :
    SourceVerticalRationalCarrierData (F := F) T w where
  globalValue := sourceValueToRational (F := F) T w
  completionValue := completionValueToRational (F := F) T w
  global_completion_value := fun f =>
    completionValueToRational_embedded (F := F) T w f
  rhoNormalization := sourceRhoLogVolume (F := F) T w
  rho_basis := sourceRhoLogVolume_one (F := F) T w
  rho_completionValue := fun x =>
    sourceRhoLogVolume_completionValue (F := F) T w x
  valueKernel_readback := fun f =>
    sourceRhoLogVolume_eq_neg_unitValueKernel (F := F) T w f

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- Exact status card for the source vertical rational value carrier.

Constructed (this module): the actual rational value-group carrier of
(Qbar_p)^x -- padicAlgClUnitRationalLogVal : (Qbar_p)^x ->* Multiplicative
Q, onto Q, with kernel the norm-one units, realification equal to the tree's
padicAlgClUnitLogVal, and the reduced value kernel padicRationalValueKernel
whose realification image is the rational line (the tree's proved
norm-arithmetic v((Qbar_p)^x) = Q); and the partial source vertical rational
carrier over the actual number-field data -- the global-unit value map into
Q, the completion value map normalized by the actual ramification index
(image the lattice (1/e_w) Z), their exact compatibility on the phi-image via
the corrected cross-field ramification law, and the candidate rho_v
normalization r |-> (1/[K_w:(F_mod)_v]) * r * logPhi(pv) built from the
actual residue cardinalities and ramification index, with its paper-shape
basis value and its exact value-level compatibility identity with the actual
local value kernel.

Frozen missing source components (NOT constructed, NOT claimed):
(a) the identification of the source Example 3.6 value group with the
(Qbar_p)^x rational value group -- the actual completion value image is the
lattice (1/e_w) Z, not Q, and the needed embedding of K_w into (Qbar_p)^x is
not in the tree;
(b) the normalization isomorphism rho_v as a source map -- only the candidate
value-level form above is constructed, and the exact identity to the actual
local kernel carries the displayed (e_w f_w)^2 factor;
(c) the log-shell carrier;
(d) the Frobenius/log-Kummer carrier.
No source-faithfulness claim; no theta-pilot, q-pilot or Tate claim. -/
def example36SourceVerticalRationalCarrier : Obligation :=
  { id := "IUT-I-II.example36-source-vertical-rational-carrier"
    source :=
      "IUT I, Example 3.5, (i); IUT III, Example 3.6; boundary (2) " ++
        "source V_K/rho_v vertical-carrier row"
    status := VerificationStatus.interface
    note :=
      "Constructed: actual rational value-group map of (Qbar_p)^x onto Q " ++
        "(onto, kernel norm-one units, realification = the tree's " ++
        "padicAlgClUnitLogVal) and its reduced value kernel with " ++
        "realification image the rational line; partial source vertical " ++
        "rational carrier over the actual number-field data (global-unit " ++
        "value map into Q, completion value map normalized by the actual " ++
        "ramification index, exact compatibility on the phi-image by the " ++
        "corrected cross-field ramification law); the actual source " ++
        "log-volume normalization rho_v = [K_w:(F_mod)_v]*log q_v " ++
        "(= e_w log q_w) with exact squares against the completion value " ++
        "map, the transport and the realified local value kernel, its " ++
        "uniqueness, and the exact correction factor (e_w f_w)^2 of the " ++
        "candidate normalization 1/[K_w:(F_mod)_v]*log q_v: the candidate " ++
        "satisfies the completion square iff [K_w:(F_mod)_v] = 1; " ++
        "conditional value-group identification over an embedding datum " ++
        "(image (1/e_w)Z, kernel O_w^×, unique integer exponent, " ++
        "normalized-value identity equivalent to the log-norm identity " ++
        "||phi x|| = p^(-(nu_w x/e_w))). Missing, not claimed: the " ++
        "embedding of the actual completion with its normalized-value " ++
        "identity (supplied by the later embedding modules; remaining " ++
        "analytic input is the log-norm identity), log-shell carrier, " ++
        "Frobenius/log-Kummer carrier. No source-faithfulness claim; no " ++
        "theta/q/Tate claim."
    dependsOn :=
      [ "IUT-II.prime-strips-frobenioid-value-group-rationality",
        "IUT-I-II.example36-value-group-rationality",
        "IUT-I-II.example36-vertical-value-carrier",
        "IUT-I-II.example36-value-map-transport" ] }

end LeanFormal.IUT.Audit
