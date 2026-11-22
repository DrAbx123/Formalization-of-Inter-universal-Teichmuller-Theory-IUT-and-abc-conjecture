/-!
# EtFrd06: ids update 2 — Mathlib coverage + A-class reuse wiring (data only; pins 14041)

* INDEX.AG.mathlib-coverage -> AG07MathlibCoverageActual.mathlibCoverage
  ('Mathlib/external already covers' list: EllipticCurve.*, NumberTheory.Height.*,
  SheafCohomology.Basic/Cech/MayerVietoris, RingTheory.Valuation.*, Chebyshev,
  local-cft-port 105 files, AG_FLT_* 6 modules; DivisionPolynomial/Jacobian/
  AffinePoint not separate modules in this checkout; FLT RR/Serre/SmoothProper pending).
* INDEX.ETTH.frobenioid-boundary -> EtTh05FrobenioidBoundaryActual:
  etThFrobenioidBoundary(+_nonempty/_kernel/_model_input_eq), etThFrobenioidModel,
  etThFrobenioidModel_nonempty, etThFrobenioidBoundaryReuse
  (A-class reuse of ConcreteSourceFrobenioidBridge; model : Iut.FrobenioidPresentation).
* INDEX.ETTH.theta-quotient-layer -> EtTh06ThetaQuotientActual:
  EtThThetaQuotientLayer, etThThetaQuotientLayer, etThThetaQuotientReuse
  (A-class reuse of EtaleThetaQuotient; honest pre-realization scope note).
* INDEX.FRD.concrete-model -> Frd03ConcreteModelActual:
  concreteModelFrobenioid(+_nonempty/_eq_boundary_model/_kernel), frdModelReuse
  (A-class reuse of concreteStageModel : Iut.FrobenioidPresentation).
**Component, not paper object.**  No sorry/axiom/True/PUnit/toy carrier (data file).
-/

namespace LeanFormal.IUT.XiFPaper.EtFrd06Ids2Actual

/-- Ids update 2: (index id, declarations, file). -/
def etFrdIds2 : List (String × String × String) :=
  [ ("INDEX.AG.mathlib-coverage", "mathlibCoverage", "AG07MathlibCoverageActual.lean"),
    ("INDEX.ETTH.frobenioid-boundary",
      "etThFrobenioidBoundary, etThFrobenioidBoundary_nonempty, etThFrobenioidModel, etThFrobenioidModel_nonempty, etThFrobenioidBoundary_kernel, etThFrobenioidBoundaryReuse",
      "EtTh05FrobenioidBoundaryActual.lean"),
    ("INDEX.ETTH.theta-quotient-layer",
      "EtThThetaQuotientLayer, etThThetaQuotientLayer, etThThetaQuotientReuse",
      "EtTh06ThetaQuotientActual.lean"),
    ("INDEX.FRD.concrete-model",
      "concreteModelFrobenioid, concreteModelFrobenioid_nonempty, concreteModelFrobenioid_eq_boundary_model, concreteModelFrobenioid_kernel, frdModelReuse",
      "Frd03ConcreteModelActual.lean") ]

end LeanFormal.IUT.XiFPaper.EtFrd06Ids2Actual
