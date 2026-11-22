/-!
# AG00b: STEP 0 deep-search record for the AG infrastructure batch (policy §7.10)

Queries: FunctionField|OrderOfVanishing|ResidueField|WeilDivisor|PrincipalDivisor|sections|O(D)
Hits: LeanFormal 259 / Iut 15 / tmp/local-cft-port 41 / tmp/sheaf/xif/paper 610 /
gap-exploration 4 / vendor 79 / corpus 207.
Sections read in coord/PRIOR-ART-INDEX.md: A (model), F (tools/traps), G (paper-level).
Mathlib assets (the repository's checkout, reused; no re-proof):
* Mathlib/AlgebraicGeometry/FunctionField.lean:37 Scheme.functionField;
  :42 germToFunctionField; :51 Field instance for IsIntegral;
  :65 germToFunctionField_injective; :148 functionField_isFractionRing_of_isAffineOpen;
  :185 exists_isUnit_germ_eq.
* Mathlib/AlgebraicGeometry/OrderOfVanishing.lean:35 ordHom; :52 ord;
  :57 ord_eq_ordHom_of_coheight_eq_one; :61 ord_eq_zero_of_coheight_neq_one;
  :64 ord_zero; :75 ord_eq_iff; :81 ord_mul; :88 ord_of_isUnit; :107 ord_add;
  :119 ord_le_smul.
* Mathlib has NO scheme Weil divisor / O(D) / Riemann-Roch layer
  (capability matrix AG00MathlibAuditActual:44 lineBundle=false,
  coherentCohomology=false, riemannRoch=false, serdeDuality=false, genus=false);
  the only divisor file is Analysis/Meromorphic/Divisor.lean (unrelated).
  Therefore AG02b/AG03 are new definitions built on the reused function-field/ord layer.
* Production LeanFormal AG files found by the search are affine-etale/quotient
  infrastructure (AffineBaseFiniteEtaleQuotients etc.), not curve divisor theory;
  the completion/residue-field layer is ABCBridge/Geometry/FinitePlace* (adapt, not
  used by this first layer).
* qpilot AG00MathlibAuditActual provides the capability matrix (reused as reference).
New precedents appended to coord/PRIOR-ART-INDEX.md (section H, 2026-11-10 stepxi AG infra).
Pins: registry frozen 14041; no intermediate reopen.
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.AG00bStep0RecordActual

/-- STEP 0 record: (query, hits, reuse/adapt decision). -/
def agStep0Record : List (String × String × String) :=
  [ ("FunctionField|OrderOfVanishing|ResidueField|WeilDivisor|PrincipalDivisor|sections|O(D)",
      "LeanFormal 259 / Iut 15 / cft-port 41 / paper 610 / gap 4 / vendor 79 / corpus 207",
      "reuse: Mathlib FunctionField:37/42/51/65/148; OrderOfVanishing:35/52/57/61/64/75/81/88/107/119"),
    ("WeilDivisor|O(D)|sections", "Mathlib absent (AG00MathlibAuditActual:44-49 all false)",
      "adapt: define new first-layer WeilDivisor/principalDivisor/O(D) on the reused ord layer"),
    ("ResidueField", "LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceCompletionLocalInputs:204",
      "adapt (completion residue-field layer; not needed for the first sections layer)"),
    ("production AG affine-etale", "LeanFormal/IUT/Foundations/AlgebraicGeometry/*",
      "none for curve divisors (affine-etale/quotient infrastructure; out of scope)") ]

end LeanFormal.IUT.XiFPaper.AG00bStep0RecordActual
