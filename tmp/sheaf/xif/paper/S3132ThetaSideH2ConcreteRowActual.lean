set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# SUPERSEDED: H2 concrete weighted identity row now lives in Hull05WeightedIdentityActual.
Record only; no failing proof remnants. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideH2ConcreteRowActual

/-- Superseded-by record (see Hull05WeightedIdentityActual). -/
def h2SupersededBy : String := "Hull05WeightedIdentityActual"

theorem h2SupersededBy_eq : h2SupersededBy = "Hull05WeightedIdentityActual" := rfl

end LeanFormal.IUT.XiFPaper.S3132ThetaSideH2ConcreteRowActual