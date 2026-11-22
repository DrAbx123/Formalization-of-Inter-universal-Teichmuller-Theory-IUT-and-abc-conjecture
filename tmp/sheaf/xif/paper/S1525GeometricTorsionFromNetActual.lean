import tmp.sheaf.xif.paper.S1491NormEDSNetActual
import tmp.sheaf.xif.paper.S1483MulByIntOnFunctionFieldActual
import tmp.sheaf.xif.paper.S1495IsogenyKernelActual
import tmp.sheaf.xif.paper.S1433KernelCardPortActual
/-! # S1525: geometric torsion count from the actual kernel
S1491 gives IsEllipticNet(normEDS); S1483/S1495 give the conditional kernel
identity ker[n] = torsionBy.  The geometric count
  S1433GeometricTorsionCard W n  (Nat.card E[n] = n^2 over AlgebraicClosure)
is still the exact first missing input.  Given it (and rationality), the actual
kernel cardinality follows without fabricating the count. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
namespace LeanFormal.IUT.XiFPaper.S1525GeometricTorsionFromNetActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1433KernelCardPortActual
universe u
variable {F : Type u} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]
variable {n : ℤ}
theorem s1525NatCard_ker_of_geometric
    (hn : TauCeti.Isogeny.psiFunctionField W n ≠ 0)
    (h : TauCeti.Isogeny.EquationMulByInt W n)
    (hm : TauCeti.Isogeny.MapsInfinityMulByInt W hn h)
    (htaut : TauCeti.Isogeny.TautologicalPointMulByInt W hn h)
    (hrat : S1433TorsionRational W n)
    (hgeo : S1433GeometricTorsionCard W n) :
    Nat.card (TauCeti.Isogeny.mulByIntKerActual W hn h hm) = n.natAbs ^ 2 := by
  rw [TauCeti.Isogeny.mulByIntKerActual_eq_torsionBy W hn h hm htaut]
  exact s1433KernelCard_of_torsionRational_of_geometricTorsionCard hrat hgeo
end LeanFormal.IUT.XiFPaper.S1525GeometricTorsionFromNetActual
