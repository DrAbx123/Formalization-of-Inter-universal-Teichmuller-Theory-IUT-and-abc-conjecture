/-!
# AG05: AG infrastructure ids (data only; registry frozen 14041, no registry edits)

Ids for lattice's statement ledger/INDEX after the AG first batch (user order:
build AG from the source; Mathlib FunctionField/OrderOfVanishing reused).

* INDEX.AG.function-field -> AG02FunctionFieldActual:
  AGCodimOnePoint, AGFunctionField, AGRationalFunction, agOrderOfVanishing,
  agOrderOfVanishing_mul, agOrderOfVanishing_zero, agOrderOfVanishing_germ_of_isUnit,
  agFunctionField_isFractionRing_of_isAffineOpen, agGermToFunctionField_injective.
* INDEX.AG.principal-divisor -> AG02bPrincipalDivisorActual:
  WeilDivisor, weilDivisorCoeff, weilDivisorZero, weilDivisorSupport,
  principalDivisor, principalDivisor_zero, principalDivisor_mul, principalDivisor_coeff.
* INDEX.AG.sections-OD -> AG03DivisorsSectionsActual:
  weilDivisorCoeffAt, CodimOneDVR, divisorSections, mem_divisorSections_iff,
  zero_mem_divisorSections, smul_mem_divisorSections.
* INDEX.AG.sections-basic -> AG03bSectionsBasicActual:
  divisorSections_restrict, divisorSections_mono_coeff, unit_germ_mem_divisorSections_zero.
* INDEX.AG.step0 -> AG00bStep0RecordActual.agStep0Record.
Reused Mathlib (no re-proof): FunctionField.lean:37/42/51/65/148,
OrderOfVanishing.lean:35/52/57/61/64/75/81/88/107/119.
Postponed (honestly): finiteness of principal divisors on proper smooth curves,
sum-of-principal-divisor = 0 (degree), Riemann-Roch (genus/lineBundle/coherent
cohomology absent in Mathlib per AG00MathlibAuditActual).
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.AG05IdsActual

/-- AG infrastructure ids: (index id, declarations, file). -/
def agIds : List (String × String × String) :=
  [ ("INDEX.AG.function-field",
      "AGCodimOnePoint, AGFunctionField, AGRationalFunction, agOrderOfVanishing, agOrderOfVanishing_mul, agOrderOfVanishing_zero, agOrderOfVanishing_germ_of_isUnit, agFunctionField_isFractionRing_of_isAffineOpen, agGermToFunctionField_injective",
      "AG02FunctionFieldActual.lean"),
    ("INDEX.AG.principal-divisor",
      "WeilDivisor, weilDivisorCoeff, weilDivisorZero, weilDivisorSupport, principalDivisor, principalDivisor_zero, principalDivisor_mul, principalDivisor_coeff",
      "AG02bPrincipalDivisorActual.lean"),
    ("INDEX.AG.sections-OD",
      "weilDivisorCoeffAt, CodimOneDVR, divisorSections, mem_divisorSections_iff, zero_mem_divisorSections, smul_mem_divisorSections",
      "AG03DivisorsSectionsActual.lean"),
    ("INDEX.AG.sections-basic",
      "divisorSections_restrict, divisorSections_mono_coeff, unit_germ_mem_divisorSections_zero",
      "AG03bSectionsBasicActual.lean"),
    ("INDEX.AG.step0", "agStep0Record", "AG00bStep0RecordActual.lean") ]

end LeanFormal.IUT.XiFPaper.AG05IdsActual
