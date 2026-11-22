import tmp.sheaf.xif.paper.S1535UniversalRecursionActual
import tmp.sheaf.xif.paper.S1410BivariateOmegaActual
import tmp.sheaf.xif.paper.S1491NormEDSNetActual

noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace WeierstrassCurve
namespace Universal

/-- Exact first missing omega defining identity (S1410 module docstring):
the bivariate omega satisfies
  2 omega_n + a1 phi_n psi_n + a3 psi_n^3 = psi_c n. -/
def S1546OmegaDefiningIdentity (n : Int) : Prop :=
  2 * curve.ω n + C (C curve.a₁) * curve.φ n * curve.ψ n +
      C (C curve.a₃) * (curve.ψ n) ^ 3 =
    curve.ψc n

/-- The omega defining identity in the universal fraction field. -/
def S1546OmegaDefiningIdentityField (n : Int) : Prop :=
  2 * polyToField (curve.ω n) +
      polyToField (C (C curve.a₁)) * polyToField (curve.φ n) *
        polyToField (curve.ψ n) +
      polyToField (C (C curve.a₃)) * (polyToField (curve.ψ n)) ^ 3 =
    polyToField (curve.ψc n)

/-- Exact first missing identity for the universal n-smul recursion. -/
abbrev S1546FirstMissingIdentity : Prop :=
  ∀ n : Int, S1546OmegaDefiningIdentity n

/-- The exact smul-point equation first field from S1535. -/
abbrev S1546SmulPointEquationFirstField (n : Int) : Prop :=
  S1535SmulPointEquation n

end Universal
end WeierstrassCurve

end
