import LeanFormal.IUT.Audit.Status

/-! # AG93: Mathlib citation rows for the AG infrastructure

Exact Mathlib paths/declarations audited for AG00/AG90 capability matrix; no
re-proof, no axioms; registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.AG93AgCitationRowsActual

/-- Mathlib citation rows: (capability, path, declaration/line, use). -/
def AGMathlibCitationRows : List (String × String × String × String) :=
  [ ("schemes", "Mathlib/AlgebraicGeometry/Scheme.lean", "Scheme, Scheme.Opens, structure sheaf", "AG01 base carrier"),
    ("morphisms/over/fibers", "Mathlib/AlgebraicGeometry/Over.lean; Fiber.lean", "Over, Fiber", "AG01 curves over a field"),
    ("properties (proper/smooth/integral)", "Mathlib/AlgebraicGeometry/Properties.lean; Limits.lean; Normalization.lean", "IsProper/IsSmooth/IsIntegral etc.", "AG01 geometric curve predicates"),
    ("valuative criterion", "Mathlib/AlgebraicGeometry/ValuativeCriterion.lean", "valuative criteria", "AG01 properness/completeness of curves"),
    ("function field", "Mathlib/AlgebraicGeometry/FunctionField.lean", ":37 Scheme.functionField; :41 Scheme.germToFunctionField; :55 germ_injective_of_isIntegral; :65 scheme.germToFunctionField_injective; :148 functionField_isFractionRing_of_isAffineOpen", "AG02 function field (reuse)"),
    ("order of vanishing", "Mathlib/AlgebraicGeometry/OrderOfVanishing.lean", ":35 ordHom; :52 ord", "AG02 ord (reuse, coheight-1)"),
    ("rational maps", "Mathlib/AlgebraicGeometry/RationalMap.lean", "PartialMap/RationalMap machinery", "AG03 dominant rational maps"),
    ("module sheaves", "Mathlib/AlgebraicGeometry/Modules/Presheaf.lean; Sheaf.lean; Tilde.lean", "PresheafOfModules/SheafOfModules/Tilde", "AG03/AG04 sections/line bundles (partial)"),
    ("abstract sheaf cohomology (corrected)", "Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean; Cech.lean; MayerVietoris.lean", "H, cohomologyPresheafFunctor, H.equiv0, H.map, Cech, Mayer-Vietoris", "AG05 PARTIAL-REUSE (abstract; not only ell-adic)"),
    ("ell-adic cohomology (reference only)", "Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean", ":75 EllAdicCohomology", "reference only; irrelevant to coherent H0/H1"),
    ("external FLT assets (Apache-2.0)", "tmp/external/flt-lean (local clone of github.com/anthropics/fermats-last-theorem; 1450 lean files under Definitions)", "Definitions/Def_AlgebraicCurve_{DivisorClassGroup,AdelicIndex,CechSectionsOfDivisor,SerrePairing,RiemannRochRows}.lean; Def_AlgebraicGeometry_{SmoothProperCurveBase,SmoothProperCurveFiniteMapData}.lean", "AG03-AG08 ADAPT (external, license Apache-2.0)"),
    ("FLT adapted copies (Apache-2.0 headers kept)", "tmp/sheaf/xif/paper/AG_FLT_*.lean (adapted from tmp/external/flt-lean; no import of FLT project)", "AG_FLT_Def_AlgebraicCurve_DivisorClassGroup (72 decls CITABLE), _Repartitions, _AdelicIndex (68 decls CITABLE), AG_FLT_Def_AlgebraicGeometry_CoherentBaseChange; pending _TwoChartCech/_CechSectionsOfDivisor; next _SerrePairing/_RiemannRochRows/_SmoothProperCurveBase/_FiniteMapData", "AG03-AG08 REALIZED/PENDING ADAPT (flat naming; import rewrite only; API fix AddMonoidHom.domRestrict -> mk'; other stream full FLT port tmp/external/ported/flt* duplicated -> use flat AG_FLT_* as citable)"),
    ("upstream Mathlib PRs", "github.com/leanprover-community/mathlib4", "#36218 merged (sheaf cohomology exact sequences); #43392 open (sheaves of modules cohomology API); #41621 open draft (conditional Riemann-Roch chi(O_X(D)) = deg + chi(O_X))", "AG04/AG05/AG06 tracking"),
    ("papers/context", "MHYY Formalization of IUT (2026-04): papers/motizuki_corpus/text/Formalization of IUT (2026-04).txt (corpus + kurims URL); LANA: papers/LANA_report_202607.pdf + text tmp/external/lana_report_202607.txt + github.com/katobungen/LANA_report_202607; Stoll talk (Formalizing Heights); Cambridge Brauer/group cohomology Lean4 seminar; Zulip Belyi/Dessins; arXiv 2606.16679 chip-firing RR graphs Lean4", "roadmap/four-triangle; heights; Brauer cohomology; Belyi status; combinatorial RR reference", "CONTEXT/REFERENCE"),
    ("divisors/line bundles/RR/Serre/pencil", "NO Mathlib file", "n/a", "AG03-AG08 TO BUILD (audited: no divisor/RR/Serre/basepoint-free assets)") ]

theorem AGMathlibCitationRows_length : AGMathlibCitationRows.length = 15 := rfl

end LeanFormal.IUT.XiFPaper.AG93AgCitationRowsActual

namespace LeanFormal.IUT.Audit

/-- INDEX note: AG Mathlib citation rows. -/
def AGMathlibCitationRowsRecord : Obligation :=
  { id := "INDEX.AG.mathlib-citation-rows"
    source := "Mathlib/AlgebraicGeometry/* audited paths; no divisor/RR/Serre/basepoint-free assets"
    status := VerificationStatus.interface
    note := "AG MATHLIB CITATION ROWS (15, incl. FLT adapted copies): Scheme/Over/Properties/Limits/Normalization/ValuativeCriterion available; FunctionField.lean:37/41/55/65/148; OrderOfVanishing.lean:35/52; RationalMap.lean; Modules/Presheaf/Sheaf/Tilde partial; CORRECTION: Mathlib/CategoryTheory/Sites/SheafCohomology/{Basic,Cech,MayerVietoris}.lean provide abstract sheaf cohomology (H/cohomologyPresheafFunctor/H.equiv0/Cech/MV) -> AG04/AG05 PARTIAL-REUSE; external FLT repo anthropics/fermats-last-theorem (Apache-2.0) provides divisor class group/adelic index/Cech sections/Serre pairing/RR rows/curve base/finite map data -> AG03-AG08 ADAPT; upstream PRs #36218 merged/#43392 open/#41621 open draft tracked; papers/context rows added. Basepoint-free pencil + Mzk1 GeometricCore remain to build (paper-input; no Belyi formalization per Zulip). No re-proof; no axioms; registry frozen 14041."
    dependsOn := ["AG93AgCitationRowsActual", "INDEX.AG.mathlib-capability-matrix"] }

end LeanFormal.IUT.Audit