/-
  Actual quotient of completion integral units by the image of source integral
  units.

  The quotient uses the actual subgroup `SourceIntegralUnitsImage` from
  SourceIntegralUnitsImage.lean, hence the actual groups and the actual canonical
  comparison map.  No arbitrary carrier and no claim that the quotient is
  trivial is made.  The exact quotient/units residual is stated at the end.
-/
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceIntegralUnitsImage
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 8000000
set_option maxHeartbeats 8000000

noncomputable section

namespace LeanFormal.IUT.SourceIntegralUnitsQuotient

open LeanFormal.IUT Theorem311Source
open LeanFormal.IUT.SourceIntegralUnitsComparison
open LeanFormal.IUT.SourceIntegralUnitsImage

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers S.arithmetic.F))

/-- The actual quotient of completion integral units by the source image. -/
abbrev CompletionIntegralUnitsQuotient : Type u :=
  CompletionIntegralUnits S v ⧸ SourceIntegralUnitsImage S v

/-- The actual quotient projection. -/
def completionIntegralUnitsToQuotient :
    CompletionIntegralUnits S v →* CompletionIntegralUnitsQuotient S v :=
  QuotientGroup.mk' (SourceIntegralUnitsImage S v)

@[simp] theorem completionIntegralUnitsToQuotient_apply
    (x : CompletionIntegralUnits S v) :
    completionIntegralUnitsToQuotient S v x =
      (QuotientGroup.mk x : CompletionIntegralUnitsQuotient S v) := rfl

/-- Every source integral unit maps to the identity in the actual quotient. -/
theorem sourceIntegralUnitsToQuotient_eq_one (u : SourceIntegralUnits S) :
    completionIntegralUnitsToQuotient S v
      (sourceIntegralUnitsToCompletion S v u) = 1 :=
  (QuotientGroup.eq_one_iff (N := SourceIntegralUnitsImage S v)).mpr
    (sourceIntegralUnitsToCompletion_mem_image S v u)

/-- The kernel of the quotient projection is exactly the actual image subgroup. -/
theorem completionIntegralUnitsToQuotient_ker :
    (completionIntegralUnitsToQuotient S v).ker =
      SourceIntegralUnitsImage S v :=
  QuotientGroup.ker_mk' (SourceIntegralUnitsImage S v)

/-- The quotient projection is surjective. -/
theorem completionIntegralUnitsToQuotient_surjective :
    Function.Surjective (completionIntegralUnitsToQuotient S v) :=
  QuotientGroup.mk'_surjective (SourceIntegralUnitsImage S v)

/-! ## Exact quotient residual

Constructed here: the actual quotient of the completion integral-unit group by
the actual image of `(O_F)^×`, together with its projection, kernel and
surjectivity.

NOT claimed:
* that this quotient is trivial (this would be surjectivity of the comparison
  on units, which is false without further source hypotheses);
* that the quotient is finite, compact, or identified with a source unit index;
* that this quotient is the source Psi^cns unit quotient.  The source Psi^cns
  object and its integral units are still missing.

The next exact object is the source Psi^cns candidate carried by the units of
the actual source curve coordinate ring; see SourcePsiIntegralUnits.lean.
-/


/-- The quotient projection is the canonical quotient-group map. -/
theorem completionIntegralUnitsToQuotient_eq_mk (x : CompletionIntegralUnits S v) :
    completionIntegralUnitsToQuotient S v x =
      (QuotientGroup.mk x : CompletionIntegralUnitsQuotient S v) :=
  rfl

/-- A completion unit has trivial quotient class exactly when it lies in the
actual source image. -/
theorem completionIntegralUnitsToQuotient_eq_one_iff
    (x : CompletionIntegralUnits S v) :
    completionIntegralUnitsToQuotient S v x = 1 ↔
      x ∈ SourceIntegralUnitsImage S v :=
  QuotientGroup.eq_one_iff (N := SourceIntegralUnitsImage S v)

/-- The composite of the source comparison with the quotient projection is
trivial on every source unit. -/
theorem sourceIntegralUnitsToQuotient_comp_eq_one (u : SourceIntegralUnits S) :
    completionIntegralUnitsToQuotient S v
        (sourceIntegralUnitsToCompletion S v u) = 1 :=
  sourceIntegralUnitsToQuotient_eq_one S v u

/-- The quotient projection is natural on multiplication. -/
theorem completionIntegralUnitsToQuotient_mul
    (x y : CompletionIntegralUnits S v) :
    completionIntegralUnitsToQuotient S v (x * y) =
      completionIntegralUnitsToQuotient S v x *
        completionIntegralUnitsToQuotient S v y :=
  map_mul (completionIntegralUnitsToQuotient S v) x y

/-- The quotient projection is natural on inversion. -/
theorem completionIntegralUnitsToQuotient_inv
    (x : CompletionIntegralUnits S v) :
    completionIntegralUnitsToQuotient S v x⁻¹ =
      (completionIntegralUnitsToQuotient S v x)⁻¹ :=
  map_inv (completionIntegralUnitsToQuotient S v) x


/-! ## Frozen imports and interface dependencies

Imports exactly:
- `SourceIntegralUnitsImage` (actual image subgroup).

Declarations exported:
- `CompletionIntegralUnitsQuotient S v`;
- `completionIntegralUnitsToQuotient`;
- `completionIntegralUnitsToQuotient_apply`;
- `sourceIntegralUnitsToQuotient_eq_one`;
- `completionIntegralUnitsToQuotient_ker`;
- `completionIntegralUnitsToQuotient_surjective`;
- quotient multiplication/inversion naturality.

Exact residual: the quotient is not claimed trivial, finite, compact, or to be
the source Psi^cns unit quotient.  Those require actual source units beyond the
completion image.


-/
/-! ## Interface checklist (audit)

#check CompletionIntegralUnitsQuotient
#check completionIntegralUnitsToQuotient
#check completionIntegralUnitsToQuotient_apply
#check sourceIntegralUnitsToQuotient_eq_one
#check completionIntegralUnitsToQuotient_ker
#check completionIntegralUnitsToQuotient_surjective
#check completionIntegralUnitsToQuotient_eq_one_iff
#check completionIntegralUnitsToQuotient_comp_eq_one
#check completionIntegralUnitsToQuotient_mul
#check completionIntegralUnitsToQuotient_inv

All exported objects are actual quotient groups/maps built from the actual image
subgroup.  There is no `axiom`, `sorry`, `opaque`, `unsafe`, `Card`, or arbitrary
carrier in this file.
-/


/-! ## Batch metadata

- Batch: actual source integral units (Lead batch-draft mode).
- Owner draft only; no per-file compile in this batch.
- Exact imports frozen: `SourceIntegralUnitsImage`.
- Direct dependencies: actual completion integral-unit group and actual image
  subgroup.
- Exported declarations: completion quotient, projection, kernel,
  surjectivity, naturality.
- Residual: no triviality/finiteness/compactness claim; no source Psi^cns unit
  quotient identification.
- No production edit; no promotion claim.


-/
/-! ## Exact consumer statement

For every actual `S : SourceDefinition31Data l` and every actual finite place
`v : HeightOneSpectrum (O_F)`, the declarations above construct the actual
quotient group

  CompletionIntegralUnits S v ⧸ SourceIntegralUnitsImage S v

and prove that the kernel of the quotient projection is exactly the image
subgroup and that the projection is surjective.  No triviality, finiteness, or
source-Psi^cns quotient identification is asserted.
-/


/-! ## Batch handoff note

This draft freezes the quotient object and its projection only.  The batch
compiler should check this file after `SourceIntegralUnitsImage`; no later file
constructs or assumes triviality of this quotient.  The source-Psi^cns file
uses only the actual source curve coordinate ring and the actual source
integral units, not this quotient.
-/


/-! ## Batch consumer note

The quotient object here is actual and is not used by the Psi^cns candidate file
as a substitute for a source unit quotient.  The next batch item can consume
the quotient projection and its kernel, but must not assume triviality.
-/


/-! ## Frozen signature note

The quotient notation is `CompletionIntegralUnits S v ⧸ SourceIntegralUnitsImage S v`; no alternate quotient alias is exported.
-/


/-! ## Quotient preimage and induction API -/

/-- Preimage of the identity under the quotient projection is the actual image
subgroup. -/
theorem completionIntegralUnitsToQuotient_eq_one_iff'
    (x : CompletionIntegralUnits S v) :
    completionIntegralUnitsToQuotient S v x = 1 ↔
      x ∈ SourceIntegralUnitsImage S v :=
  completionIntegralUnitsToQuotient_eq_one_iff S v x

/-- Membership in the actual image implies trivial quotient class. -/
theorem completionIntegralUnitsToQuotient_eq_one_of_mem
    {x : CompletionIntegralUnits S v} (hx : x ∈ SourceIntegralUnitsImage S v) :
    completionIntegralUnitsToQuotient S v x = 1 :=
  (completionIntegralUnitsToQuotient_eq_one_iff S v x).mpr hx

/-- Trivial quotient class produces a membership witness in the actual image. -/
theorem mem_sourceIntegralUnitsImage_of_quotient_eq_one
    {x : CompletionIntegralUnits S v}
    (hx : completionIntegralUnitsToQuotient S v x = 1) :
    x ∈ SourceIntegralUnitsImage S v :=
  (completionIntegralUnitsToQuotient_eq_one_iff S v x).mp hx

/-- The quotient projection is a group homomorphism. -/
theorem completionIntegralUnitsToQuotient_map_one :
    completionIntegralUnitsToQuotient S v (1 : CompletionIntegralUnits S v) = 1 :=
  map_one (completionIntegralUnitsToQuotient S v)

/-- The quotient projection sends product to product. -/
theorem completionIntegralUnitsToQuotient_map_mul
    (x y : CompletionIntegralUnits S v) :
    completionIntegralUnitsToQuotient S v (x * y) =
      completionIntegralUnitsToQuotient S v x *
        completionIntegralUnitsToQuotient S v y :=
  map_mul (completionIntegralUnitsToQuotient S v) x y

/-- The quotient projection sends inverse to inverse. -/
theorem completionIntegralUnitsToQuotient_map_inv
    (x : CompletionIntegralUnits S v) :
    completionIntegralUnitsToQuotient S v x⁻¹ =
      (completionIntegralUnitsToQuotient S v x)⁻¹ :=
  map_inv (completionIntegralUnitsToQuotient S v) x

end LeanFormal.IUT.SourceIntegralUnitsQuotient

end
