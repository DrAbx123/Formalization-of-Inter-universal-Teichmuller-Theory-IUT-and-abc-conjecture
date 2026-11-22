/-!
# AG07: Mathlib/external asset coverage for the AG / FrdI-II / EtTh lines (data only)

STEP 0 addendum per Lead externals guidance: "Mathlib/external already covers ..."
Verified against this repository's Mathlib checkout
(.lake/packages/mathlib/Mathlib) and the local/external ports.

VERIFIED PRESENT (Mathlib):
* Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean
  (also Reduction.lean, NormalForms.lean, ModelsWithJ.lean, IsomOfJ.lean,
  VariableChange.lean, LFunction.lean).  NOTE: DivisionPolynomial/Jacobian/
  AffinePoint are NOT separate modules in this checkout (verify before use).
* Mathlib/NumberTheory/Height/Basic.lean, NumberField.lean, EllipticCurve.lean,
  MvPolynomial.lean, Northcott.lean, Projectivization.lean.
* Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean, Cech.lean,
  MayerVietoris.lean.
* Mathlib/RingTheory/Valuation/Basic.lean (+ Archimedean.lean,
  DiscreteValuativeRel.lean, Extension.lean, Integers.lean, ...).
* Mathlib/NumberTheory/Chebyshev.lean (single module in this checkout).
* Mathlib.NumberTheory.Height.NumberField is already imported by production
  LeanFormal/IUT/ABCBridge/Arithmetic/{RationalPointDictionary,ABCInvariantHeight,
  RationalLocalHeightDecomposition}.lean (reuse in (b), see S3171UniformHeightConsumerActual).
VERIFIED PRESENT (local ports / adapted):
* tmp/local-cft-port: LocalClassFieldTheory (105 files: Brauer/TateNakayama/H2ZHat etc.) — importable.
* tmp/sheaf/xif/paper/AG_FLT_*.lean: 6 adapted FLT modules (DivisorClassGroup,
  Repartitions, AdelicIndex, TwoChartCech, CechSectionsOfDivisor, CoherentBaseChange).
* ported TauCeti (AG_TAUCETI_*) and raw tmp/external/flt-lean (NOT importable directly).
ABSENT (must write ourselves; current tree layers):
* Weil divisor / O(D) / Riemann-Roch / Serre duality / genus (Mathlib absent per
  AG00MathlibAuditActual:44-49) -> our AG02b/AG03/AG03b/AG04/AG04b first-second layers.
* Frobenioid category / model Frobenioid / Frobenius functors (Mathlib absent) ->
  tree production Frobenioid objects (Iut.Foundations + IUTII/Frobenioid) reused;
  our Frd01 statement layer + EtTh05 boundary reuse.
* Étale theta function / theta environments / bi-Kummer theory (Mathlib absent) ->
  tree EtaleThetaQuotient (pre-realization group-theoretic layer) reused; deep
  [EtTh] results are class-B D-inputs (EtTh02DeepInputsActual, proved := false).
Policy: import existing assets first; write only missing definitions/theorems;
never re-prove Mathlib/external results.
**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.AG07MathlibCoverageActual

/-- Coverage row: (asset area, exact module, status). -/
def mathlibCoverage : List (String × String × String) :=
  [ ("elliptic curves", "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass/Reduction/NormalForms/ModelsWithJ/IsomOfJ/VariableChange/LFunction", "PRESENT (DivisionPolynomial/Jacobian/AffinePoint not separate in this checkout)"),
    ("heights", "Mathlib.NumberTheory.Height.Basic/NumberField/EllipticCurve/MvPolynomial/Northcott/Projectivization", "PRESENT (NumberField already used by production (b) dictionary)"),
    ("sheaf cohomology", "Mathlib.CategoryTheory.Sites.SheafCohomology.Basic/Cech/MayerVietoris", "PRESENT (usable for AG-03 line bundles)"),
    ("valuations/adic", "Mathlib.RingTheory.Valuation.Basic (+Archimedean/DiscreteValuativeRel/Extension/Integers)", "PRESENT"),
    ("Chebyshev/PNT", "Mathlib.NumberTheory.Chebyshev", "PRESENT (single module; PNT explicit forms verified earlier in Section2)"),
    ("local CFT", "tmp/local-cft-port (105 files)", "PRESENT (importable)"),
    ("FLT adapted", "tmp/sheaf/xif/paper/AG_FLT_*.lean (6 modules)", "PRESENT (adaptation done)"),
    ("FLT pending", "Def_AlgebraicCurve_RiemannRochRows/SerrePairing/Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData", "PENDING (raw in tmp/external/flt-lean; NOT counted)"),
    ("TauCeti ported", "ported TauCeti (AG_TAUCETI_*)", "PRESENT/partially ported (import only when olean present)"),
    ("Weil divisor/O(D)/RR/Serre/genus", "Mathlib ABSENT", "our AG02b/AG03/AG03b/AG04/AG04b layers"),
    ("Frobenioid objects", "Mathlib ABSENT; tree Iut.Foundations.SourceModelFrobenioid* + IUTII/Frobenioid", "reuse tree (Frd02 audit)"),
    ("etale theta function", "Mathlib ABSENT; tree EtaleThetaQuotient (pre-realization quotient layer)", "reuse A; deep results class B (proved := false)") ]

end LeanFormal.IUT.XiFPaper.AG07MathlibCoverageActual
