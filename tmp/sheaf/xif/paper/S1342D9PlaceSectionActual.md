# S1342: D9 place/section-related compatibility pairs over S1280

Date: 2026-10-30. Actual section pair; exact first field for reduction.
No kummer/D5 touched.

## Actual item

For the actual S1280 Gaussian selection S1280Selection l:

  s1342SectionCompatibility_actual :
    ArithmeticSectionCompatibility (S1280Selection l)

proved by arithmeticSectionCompatibility_canonical.  This is the
Definition 3.1(e) place/section half: the canonical restriction section,
bijection V ~ V_mod, V_bad/V_good and V_non/V_arc decompositions, and the
bad-selection correspondence.  It is actual and depends only on the place
selection, not on D5/kummer.

## Conditional actual item

Given the exact bad-place q-parameter cards

  Q : BadPlaceQParameterCards (S1280Selection l),

  s1342ReductionCompatibility_of_Q l Q :
    ArithmeticReductionCompatibility (S1280Selection l)
      (S1280ReductionCards l) Q

using the actual S1280ReductionCards (stable/multiplicative/split
multiplicative reduction at the actual place above 5) and
arithmeticReductionCompatibility_of_supply.

## Exact first field

For the place/reduction-related D9 pair the exact first field is

  S1342ReductionFirstField l := BadPlaceQParameterCards (S1280Selection l).

The tree's D9 supply constructor D9CompatibilitySupply.ofArithmeticSlots takes
this Q as an explicit source input; no actual Q card bundle for the S1280
singleton selection is constructed here.  (The residue-characteristic
coprimality is not available at l = 5; S1280_clauseC_refuted_at_five records
that obstruction.  The sourceQParameterOrder coprime fields are also not
supplied.)

The section pair needs no Q and is actual.

## Full D9 supply

D9CompatibilitySupply also has torsion/orbicurve/cusp slots.  Per instruction
kummer/D5 are not touched; no full D9CompatibilitySupply is constructed.  The
place/section-related items are exactly:
  sections: actual;
  reduction: actual conditional on Q; first exact field Q.
Consumer: S1280SourceData_of_remaining / SourceDefinition31Data D11 assembly.

No weak Prop/Nonempty gate; no kummer/D5 modifications.
