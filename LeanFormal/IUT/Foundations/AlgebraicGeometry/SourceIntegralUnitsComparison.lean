/-
  Actual source integral units and their canonical comparison with completion
  integral units.

  The source group is the actual `(O_F)^×` of the Definition 3.1 source field F.
  At an actual finite place v, the completion integral units are the units of
  Mathlib's actual `v.adicCompletionIntegers F`.  The canonical ring map
  `O_F -> v.adicCompletionIntegers F` induces the unit comparison.  No arbitrary
  carrier type is introduced; the residual image/surjectivity comparison is
  stated at the end.
-/
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.SourceIntegralUnitsComparison

open LeanFormal.IUT Theorem311Source

universe u

variable {l : PrimeGeFive}

/-- The actual source integral-unit group of the Definition 3.1 source field. -/
abbrev SourceIntegralUnits (S : SourceDefinition31Data l) : Type u :=
  (NumberField.RingOfIntegers S.arithmetic.F)ˣ

/-- The actual integral units of the completion at a finite place v. -/
abbrev CompletionIntegralUnits (S : SourceDefinition31Data l)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F)) : Type u :=
  (v.adicCompletionIntegers S.arithmetic.F)ˣ

/-- Canonical comparison of source integral units with completion integral units,
induced by the actual algebra map into the adic completion integers. -/
noncomputable def sourceIntegralUnitsToCompletion (S : SourceDefinition31Data l)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F)) :
    SourceIntegralUnits S →* CompletionIntegralUnits S v :=
  Units.map (algebraMap (NumberField.RingOfIntegers S.arithmetic.F)
    (v.adicCompletionIntegers S.arithmetic.F)).toMonoidHom

/-- The comparison map is a homomorphism of the actual unit groups by
construction; this records its multiplication law. -/
theorem sourceIntegralUnitsToCompletion_mul (S : SourceDefinition31Data l)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F)) (u w : SourceIntegralUnits S) :
    sourceIntegralUnitsToCompletion S v (u * w) =
      sourceIntegralUnitsToCompletion S v u * sourceIntegralUnitsToCompletion S v w :=
  map_mul (sourceIntegralUnitsToCompletion S v) u w

/-! ## Exact comparison residual

The canonical comparison map above is actual.  The unresolved comparison is
not a new carrier: it is the image/quotient comparison inside the actual
completion integral-unit group.  In particular this file does not claim:

* that the source integral units surject onto all completion integral units
  (the completion contains principal units not coming from `O_F`);
* that the source units are exactly the norm-one/unit subgroup of the
  completion under this map;
* any identification with the source Psi^cns integral units, which still
  requires the actual source cover/integral-unit comparison.

The next exact object is the image subgroup of `sourceIntegralUnitsToCompletion`
inside `CompletionIntegralUnits`, together with its quotient/units comparison.
-/

end LeanFormal.IUT.SourceIntegralUnitsComparison

end