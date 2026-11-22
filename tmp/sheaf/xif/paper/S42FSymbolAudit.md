# S42: audit of the F signifiers and S40 field map

Date: 2026-10-29. Source/Lean type audit only.

## Registry distinctions

| Paper signifier | Paper meaning | Lean type in the tree | Collision status |
|---|---|---|---|
| CMMI italic F | number field F | InitialThetaArithmeticData.F / T.arithmetic.F | distinct field type |
| CMMI italic F with subscript mod | base number field F_mod | InitialThetaArithmeticData.Fmod / fieldI.initial.arithmetic.Fmod | distinct number-field type; NOT finite field F_l |
| MSBM blackboard F_l | finite field of l elements | Fl l, defined as ZMod l | distinct from every number field |
| CMSY script F | Frobenioid / script F | Frobenioid objects/interfaces | distinct object family |
| CMSY F with decorations F-prime-strip | prime-strip variants | FPrimeStrip and variants | distinct decorated structures |

## S40 check

S40SourceTheaterFieldMapDirectActual.sourceFieldMap has type

  fieldI.initial.arithmetic.Fmod ->+* fieldI.initial.arithmetic.F.

Both sides are fields of the same InitialThetaArithmeticData:

* Fmod is the base number field F_mod (CMMI italic F with subscript mod);
* F is the extension number field F (CMMI italic F).

The map is the actual algebra embedding F_mod -> F.  It is not a map involving:

* Fl l = ZMod l (MSBM finite field F_l);
* FPrimeStrip (CMSY decorated prime-strip F);
* Frobenioid (CMSY script F).

fieldI is an OriginalInput; its .initial.arithmetic is the source arithmetic
data.  fieldI.initial.arithmetic.F and .Fmod are number fields by their
Field/NumberField instances, not finite fields and not Frobenioid objects.

## Exact name-level collision risks

No type collapse is present in S40.  Remaining risks are name-level only:

1. the field name Fmod can be misread as the finite field F_l; its type is a
   NumberField field, not ZMod l;
2. the field name F inside InitialThetaArithmeticData can be confused with the
   letter used in Fl, FPrimeStrip, and Frobenioid names; these are different
   types in different namespaces;
3. fieldI carries a family : SourceHodgeTheaterFamily, which contains
   F-prime-strip data, but sourceFieldMap only uses
   .initial.arithmetic.Fmod and .initial.arithmetic.F; it does not project a
   prime-strip into a number field.

## Conclusion

No wrapper or type change is required for S40: the actual map is correctly
number-field F_mod -> number-field F.  The F signifiers are separated by their
Lean types.  The only collision to retain in the registry is the name-level
Fmod/Fl risk; no Lean equality between them exists or is asserted.

No fake wrapper, equality, axiom, or sorry.
