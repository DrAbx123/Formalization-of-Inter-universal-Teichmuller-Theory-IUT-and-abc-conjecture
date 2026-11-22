import tmp.sheaf.xif.paper.S1535UniversalRecursionActual
import tmp.sheaf.xif.paper.S1521OmegaInvariantCancellationActual
import tmp.sheaf.xif.paper.S1472ZSMulOmegaPortActual

noncomputable section
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace WeierstrassCurve
namespace Universal

-- S1521's omega defining identity, at the base-changed universal curve over
-- the universal fraction field.
theorem s1559OmegaSpecBase (n : Int) :
    2 * (curve.baseChange Field).ω n +
        C (C (curve.baseChange Field).a₁) * (curve.baseChange Field).φ n *
          (curve.baseChange Field).ψ n +
        C (C (curve.baseChange Field).a₃) * ((curve.baseChange Field).ψ n) ^ 3 =
      (curve.baseChange Field).ψc n :=
  (curve.baseChange Field).ω_spec n

/-- Exact first missing affine doubling identity (S1472). -/
abbrev S1559UniversalDoublingIdentity : Prop :=
  LeanFormal.IUT.XiFPaper.S1472ZSMulOmegaPortActual.DoublingIdentity (curve.baseChange Field).toAffine

/-- Exact first missing affine addition identity (S1472). -/
abbrev S1559UniversalAdditionIdentity : Prop :=
  LeanFormal.IUT.XiFPaper.S1472ZSMulOmegaPortActual.AdditionIdentity (curve.baseChange Field).toAffine

/-- Exact smul-point equation first field from S1535. -/
abbrev S1559SmulPointEquationFirstField (n : Int) : Prop :=
  S1535SmulPointEquation n

/-- Exact next missing recursion: the affine doubling and addition identities
for the universal triple. These are the first fields left by S1472 after S1521
supplies omega_spec; they are not assumed here. -/
def S1559AffineRecursionMissing : Prop :=
  S1559UniversalDoublingIdentity ∧ S1559UniversalAdditionIdentity

end Universal
end WeierstrassCurve

end
