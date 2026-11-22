import tmp.external.ported.flt_core.Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed

/-!
# Mzk1RRProvedActual — real (ported) proof of the function-field Riemann–Roch statement

STEP 0 prior-art: the FLT repo's complete proof (Apache-2.0, commit 6e837e75) of
AlgebraicCurve.FunctionFieldRiemannRoch over an algebraically closed base field is ported in
tmp/external/ported/flt_core:
* Definitions/Def_AlgebraicCurve_RiemannRochRows.lean:47 defines the Prop
  AlgebraicCurve.FunctionFieldRiemannRoch;
* P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean proves residueTheoremK;
* P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean
  reduces RR to residueTheoremK;
* P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean gives the solution;
* Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean re-exports it.

THIS FILE: a thin, real (no axiom/sorry) re-export of the ported proof as the named
statement needed by the GeometricCore RR witness.  The hypotheses are the standard ones of
the ported chain (all as typeclass arguments, no extra assumptions); the only change is the
name.  It does NOT import flt_th/flt_test (whose duplicate AlgebraicCurve.Divisor definitions
are incompatible); it uses the self-contained flt_core port only.  Registry frozen 14041.
-/

set_option autoImplicit false

namespace LeanFormal.IUT.XiFPaper.Mzk1RRProvedActual

/-- The function-field Riemann–Roch statement, PROVED from the ported FLT chain
(residueTheoremK + reduction; see module docstring for the exact closure). -/
theorem functionFieldRiemannRoch_proved
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F] :
    AlgebraicCurve.FunctionFieldRiemannRoch K F :=
  AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed

/-- Ported-proof closure rows: (root, file, role, status). -/
def rrProofClosureRows : List (String × String × String × String) :=
  [ ("flt_core", "Definitions/Def_AlgebraicCurve_RiemannRochRows.lean",
      "defines AlgebraicCurve.FunctionFieldRiemannRoch (line 47)", "OLEAN PRESENT (imported by this file)"),
    ("flt_core", "P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean",
      "proves residueTheoremK_of_isAlgClosed", "OLEAN PRESENT; re-asserted in the stable serial log"),
    ("flt_core", "P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean",
      "RR => residueTheoremK reduction", "OLEAN PRESENT; re-asserted in the stable serial log"),
    ("flt_core", "P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean",
      "solution: FunctionFieldRiemannRoch", "OLEAN PRESENT; re-asserted in the stable serial log"),
    ("flt_core", "Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean",
      "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed re-export", "OLEAN PRESENT; imported here"),
    ("flt_th", "P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean",
      "same solution in the flt_th root", "NO OLEAN (blocked; not needed by this file)"),
    ("flt_th", "Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean",
      "same re-export in the flt_th root", "NO OLEAN (blocked; not needed by this file)"),
    ("flt_test", "P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed.lean",
      "same solution in the flt_test root", "NO OLEAN (blocked; flt_test imports incompatible)"),
    ("flt_test", "Theorems/Thm_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean",
      "residueTheoremK wrapper in the flt_test root", "NO OLEAN (chain break reported)") ]

/-- The closure row record has nine rows. -/
theorem rrProofClosureRows_length : rrProofClosureRows.length = 9 := rfl

#check functionFieldRiemannRoch_proved
#check rrProofClosureRows_length

end LeanFormal.IUT.XiFPaper.Mzk1RRProvedActual
