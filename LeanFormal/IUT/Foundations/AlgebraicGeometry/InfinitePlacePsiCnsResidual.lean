/-
  Exact residual for the source Psi^cns carrier beyond the green infinite-place
  log dictionary.

  The green `InfinitePlaceLogDictionary` supplies only the completion-level
  radius/log/kernel carrier at one infinite place.  The full source Psi^cns also
  needs the actual source object, integral units, theta divisor/degree, global
  product-formula normalization and Galois action.  They are stated below over
  the actual Definition 3.1 source contract; no arbitrary carrier type is
  introduced and no inhabitant of the residual is claimed.
-/
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTII.Frobenioid.Example36ArchimedeanLocal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Tactic

open scoped BigOperators

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.InfinitePlacePsiCnsResidual

open LeanFormal.IUT Theorem311Source

universe u

variable {l : PrimeGeFive}

/-- The actual integral-unit group of the source field F: units of its ring of
integers.  This is a concrete existing group, not a placeholder carrier. -/
abbrev SourceIntegralUnits (S : SourceDefinition31Data l) : Type u :=
  (NumberField.RingOfIntegers S.arithmetic.F)ˣ

/-- The archimedean logarithm of a source integral unit at an infinite place. -/
def sourceIntegralUnitLog (S : SourceDefinition31Data l)
    (w : NumberField.InfinitePlace S.arithmetic.F) (u : SourceIntegralUnits S) : ℝ :=
  Real.log (w ((u : NumberField.RingOfIntegers S.arithmetic.F) : S.arithmetic.F))

/-- The source theta divisor, as integer coefficients on the actual infinite
places of F.  The degree is the weighted sum with local multiplicities. -/
abbrev SourceThetaDivisor (S : SourceDefinition31Data l) : Type u :=
  NumberField.InfinitePlace S.arithmetic.F → ℤ

def sourceThetaDegree (S : SourceDefinition31Data l) (D : SourceThetaDivisor S) : ℤ :=
  ∑ w : NumberField.InfinitePlace S.arithmetic.F,
    (NumberField.InfinitePlace.mult w : ℤ) * D w

/-- Exact global product-formula normalization required of source integral units. -/
def sourceGlobalNormalization (S : SourceDefinition31Data l)
    (u : SourceIntegralUnits S) : Prop :=
  ∑ w : NumberField.InfinitePlace S.arithmetic.F,
    (NumberField.InfinitePlace.mult w : ℝ) * sourceIntegralUnitLog S w u = 0

/-- Exact Galois invariance required of the source theta divisor, under the
actual Galois group of F over the base field Fmod. -/
def sourceGaloisInvariant (S : SourceDefinition31Data l)
    (D : SourceThetaDivisor S) : Prop :=
  ∀ σ : S.arithmetic.F ≃ₐ[S.arithmetic.Fmod] S.arithmetic.F,
    ∀ w : NumberField.InfinitePlace S.arithmetic.F,
      D (w.comap σ.toRingHom) = D w

/-- The missing source Psi^cns data, stated over the actual source contract.
All fields are actual source objects/properties; no arbitrary carrier type. -/
structure SourcePsiCnsTerms (S : SourceDefinition31Data l) where
  /-- The actual integral units used by the source Psi^cns. -/
  integralUnits : Subgroup (SourceIntegralUnits S) := ⊤
  /-- The theta divisor/degree data on the actual infinite places. -/
  thetaDivisor : SourceThetaDivisor S
  thetaDegree : ℤ
  thetaDegree_eq : thetaDegree = sourceThetaDegree S thetaDivisor
  /-- The exact global product-formula normalization. -/
  globalNormalization : ∀ u : SourceIntegralUnits S,
    sourceGlobalNormalization S u
  /-- The exact Galois invariance of the theta divisor. -/
  galoisInvariant : sourceGaloisInvariant S thetaDivisor

/-- The precise residual Prop: an inhabitant would be exactly the missing
source Psi^cns terms above.  No inhabitant is constructed or assumed. -/
def InfinitePlacePsiCnsSourceResidual (S : SourceDefinition31Data l) : Prop :=
  Nonempty (SourcePsiCnsTerms S)

/-- Partial theorem exposing the exact normalization term of a residual datum. -/
theorem sourcePsiCns_globalNormalization (S : SourceDefinition31Data l)
    (T : SourcePsiCnsTerms S) (u : SourceIntegralUnits S) :
    sourceGlobalNormalization S u :=
  T.globalNormalization u

/-- Partial theorem exposing the exact theta-degree term of a residual datum. -/
theorem sourcePsiCns_thetaDegree (S : SourceDefinition31Data l)
    (T : SourcePsiCnsTerms S) :
    T.thetaDegree = sourceThetaDegree S T.thetaDivisor :=
  T.thetaDegree_eq

/-- Partial theorem exposing the exact Galois-invariance term. -/
theorem sourcePsiCns_galoisInvariant (S : SourceDefinition31Data l)
    (T : SourcePsiCnsTerms S) :
    sourceGaloisInvariant S T.thetaDivisor :=
  T.galoisInvariant

/-! ## Exact residual statement

The green `InfinitePlaceLogDictionary` proves the completion-level radius,
norm-one kernel and additive log at one infinite place.  It does NOT provide:

1. the actual source object/curve data (`S.arithmetic.F`, `S.arithmetic.curve`
   are available in the contract, but their Psi^cns identification is missing);
2. the source integral units and their comparison with the completion units
   (the concrete candidate group is `(O_F)^×` above);
3. the source theta divisor and its weighted degree (the concrete type and
   formula are `SourceThetaDivisor`/`sourceThetaDegree` above);
4. the exact global product-formula normalization over all infinite places
   (`sourceGlobalNormalization` above; this is not the single-place log);
5. the actual Galois action/invariance of the divisor (`sourceGaloisInvariant`
   above, using the actual Galois group of F/Fmod).

`InfinitePlacePsiCnsSourceResidual S` is the exact unresolved gap.  No arbitrary
`Type` carrier, no concrete Q5 substitution and no inhabitant is claimed. -/

end LeanFormal.IUT.InfinitePlacePsiCnsResidual

end