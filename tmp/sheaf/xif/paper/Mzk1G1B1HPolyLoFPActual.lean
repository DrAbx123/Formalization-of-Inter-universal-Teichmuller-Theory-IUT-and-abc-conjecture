/-
# O4 — `LocallyOfFinitePresentation (hPoly h hh)` and `(hPolyL h hh)`, closed

Consumer: `Mzk1G1B1ObligationsActual` (O4 ledger) and, downstream,
`Mzk1G1B1HbObligationsActual` (the `hbH` reduction, which assumes
`[LocallyOfFinitePresentation (hPoly h hh)]`), hence `Mzk1G1PhiFixedLBranchSupportActual`.

## What was missing, and how it is supplied

`Mzk1G1B1HPolyBranchSchemeActual.hPoly_locallyOfFinitePresentation_of_charts` reduces
`LocallyOfFinitePresentation (hPoly h hh)` to the three chart instances, and
`locallyOfFinitePresentation_chartMorphismInf` / `..._chartMorphism0` further reduce each
chart to the ring-theoretic input `RingHom.FinitePresentation (evalAt a)` for the coordinate
`a`.  Here that input is proved, in the clean general form:

* `evalAt_finiteType`: if `R` is a *finitely generated* `ℚ`-algebra, then the substitution
  map `evalAt a : ℚ[λ] →+* R` (`λ ↦ a`) exhibits `R` as a finitely generated
  `ℚ[λ]`-algebra: a finite set of `ℚ`-algebra generators of `R` also generates `R` over
  the subalgebra `ℚ[a] ⊆ R` (the `ℚ[λ]`-algebra structure is the `evalAt a`-structure).
* `evalAt_finitePresentation`: the source `ℚ[λ]` is Noetherian, so
  `RingHom.FiniteType ↔ RingHom.FinitePresentation`
  (`RingHom.FinitePresentation.of_finiteType`), and the substitution map is of finite
  presentation.

The three chart rings are `ℚ[λ]`, `Localization.Away X` and `Localization.Away (hRev h)`;
all three are finitely generated over `ℚ` (they are localizations of `ℚ[λ]`), so the three chart
instances follow without extra input, and `hPoly h hh` / `hPolyL h hh` are locally of finite
presentation **unconditionally**.

**No explicit obligations remain in this file.**  Two honest remarks:

* Noetherianity of `R` alone does *not* give `RingHom.FinitePresentation (evalAt a)`: a
  Noetherian `ℚ`-algebra that is not finitely generated over `ℚ` is a counterexample.  The
  hypothesis actually used is finite generation over `ℚ`, which is exactly what the three chart
  rings satisfy.  This is why the signature of `evalAt_finitePresentation` differs from the
  originally sketched one (`[IsNoetherianRing R]`, `hdeg`, `hmonic_rel`): the
  derivative/nonconstancy data is irrelevant to this ring-theoretic statement.
* Finiteness of `R` over `ℚ[a]` (the `Module.Finite (ℚ[h]) R` route sketched for O4) is not
  needed; finite generation of `R` over `ℚ` is enough, and it holds for the actual chart rings
  without any extra hypothesis.

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1B1HPolyBranchSchemeActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyFinalActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineTransitionActual
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 1600000
-- the `hh : h ≠ 0` arguments are part of the requested signatures but do not occur in the
-- ring-theoretic statements; silence the unused-variable linter for them.
set_option linter.unusedVariables false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyLoFPActual

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineTransitionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyBranchSchemeActual

/-! ## 1. The ring-theoretic input: `evalAt a` is of finite presentation -/

/-- **`evalAt a` is of finite type** when `R` is a finitely generated `ℚ`-algebra.

The `evalAt a`-algebra structure on `R` (`λ • x = a x`) is compatible with the given
`ℚ`-algebra structure (`IsScalarTower ℚ ℚ[λ] R`, because `evalAt a` is a `ℚ`-algebra map), and
a finite generating set of `R` over `ℚ` is also a generating set over the larger base
`ℚ[λ] ↦ ℚ[a] ⊆ R`.  This is
`Algebra.FiniteType.of_restrictScalars_finiteType` for the tower `ℚ → ℚ[λ] → R`. -/
theorem evalAt_finiteType {R : Type} [CommRing R] [Algebra ℚ R] [Algebra.FiniteType ℚ R]
    (a : R) : RingHom.FiniteType (evalAt a) := by
  letI : Algebra (Polynomial ℚ) R := (evalAt a).toAlgebra
  haveI : IsScalarTower ℚ (Polynomial ℚ) R := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    have h1 : algebraMap (Polynomial ℚ) R = evalAt a := RingHom.algebraMap_toAlgebra (evalAt a)
    rw [h1, Polynomial.algebraMap_eq, evalAt_C]
  exact Algebra.FiniteType.of_restrictScalars_finiteType (R := ℚ) (S := Polynomial ℚ) (A := R)

/-- **The substitution map is of finite presentation.**  `ℚ[λ]` is Noetherian, so finite type
and finite presentation agree (`RingHom.FinitePresentation.of_finiteType`).

Input: `R` is a finitely generated `ℚ`-algebra (e.g. a localization of `ℚ[λ]`).  Noetherianity
of `R` is neither needed nor sufficient here; see the file header. -/
theorem evalAt_finitePresentation {R : Type} [CommRing R] [Algebra ℚ R] [Algebra.FiniteType ℚ R]
    (a : R) : RingHom.FinitePresentation (evalAt a) :=
  (RingHom.FinitePresentation.of_finiteType (f := evalAt a)).mp (evalAt_finiteType a)

/-! ## 2. The three chart instances -/

/-- Chart piece 0 of `hPoly` (the `t`-chart, coordinate `h`): locally of finite presentation as
soon as `evalAt h` is of finite presentation (donor
`locallyOfFinitePresentation_chartMorphismInf`; `localChartInf` is an open immersion). -/
theorem hPolyChartInf_locallyOfFinitePresentation (h : Polynomial ℚ) (hh : h ≠ 0)
    (hfp : RingHom.FinitePresentation (evalAt (R := Polynomial ℚ) h)) :
    LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h) :=
  locallyOfFinitePresentation_chartMorphismInf h hfp

/-- Mirror of the donor lemma for the `λ`-chart: `chartMorphism0 a` is locally of finite
presentation as soon as `evalAt a` is (`localChart0` is an open immersion). -/
theorem locallyOfFinitePresentation_chartMorphism0 {R : Type} [CommRing R] [Algebra ℚ R]
    (a : R) (hfp : RingHom.FinitePresentation (evalAt a)) :
    LocallyOfFinitePresentation (chartMorphism0 (R := R) a) := by
  haveI := locallyOfFinitePresentation_specMap a hfp
  show LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (evalAt a)) ≫ localChart0)
  infer_instance

/-- Chart piece 1 of `hPoly` (inside `D(λ)`, `t`-coordinate `hPolyT h`): locally of finite
presentation as soon as `evalAt (hPolyT h)` is. -/
theorem hPolyChart1_locallyOfFinitePresentation (h : Polynomial ℚ) (hh : h ≠ 0)
    (hfp : RingHom.FinitePresentation
      (evalAt (R := Localization.Away (Polynomial.X : Polynomial ℚ)) (hPolyT h))) :
    LocallyOfFinitePresentation
      (chartMorphismInf (R := Localization.Away (Polynomial.X : Polynomial ℚ)) (hPolyT h)) :=
  locallyOfFinitePresentation_chartMorphismInf (hPolyT h) hfp

/-- Chart piece 2 of `hPoly` (inside `D(hRev)`, `λ`-coordinate `hPolyLam h`): locally of
finite presentation as soon as `evalAt (hPolyLam h)` is. -/
theorem hPolyChart0_locallyOfFinitePresentation (h : Polynomial ℚ) (hh : h ≠ 0)
    (hfp : RingHom.FinitePresentation
      (evalAt (R := Localization.Away (hRev h)) (hPolyLam h))) :
    LocallyOfFinitePresentation
      (chartMorphism0 (R := Localization.Away (hRev h)) (hPolyLam h)) :=
  locallyOfFinitePresentation_chartMorphism0 (hPolyLam h) hfp

/-! ## 3. Assembly: `hPoly` and `hPolyL` -/

/-- **O4, chart form**: `hPoly h hh` is locally of finite presentation as soon as its three chart
pieces are (donor `hPoly_locallyOfFinitePresentation_of_charts`, Zariski locality at the source
for the cover `hPolyCover h hh`). -/
theorem hPoly_locallyOfFinitePresentation (h : Polynomial ℚ) (hh : h ≠ 0)
    (H0 : LocallyOfFinitePresentation (chartMorphismInf (R := Polynomial ℚ) h))
    (H1 : LocallyOfFinitePresentation (chartMorphismInf
      (R := Localization.Away (Polynomial.X : Polynomial ℚ)) (hPolyT h)))
    (H2 : LocallyOfFinitePresentation (chartMorphism0
      (R := Localization.Away (hRev h)) (hPolyLam h))) :
    LocallyOfFinitePresentation (hPoly h hh) :=
  hPoly_locallyOfFinitePresentation_of_charts h hh H0 H1 H2

/-- **O5**: `hPolyL = p1Inv ≫ hPoly ≫ p1Inv` is locally of finite presentation as soon as
`hPoly` is (donor lemma; `p1Inv` is an isomorphism). -/
theorem hPolyL_locallyOfFinitePresentation (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)] :
    LocallyOfFinitePresentation (hPolyL h hh) :=
  LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyBranchSchemeActual.hPolyL_locallyOfFinitePresentation
    h hh

/-- **O4, closed**: `hPoly h hh` is locally of finite presentation, with the ring-theoretic
input `RingHom.FinitePresentation (evalAt a)` discharged by `evalAt_finitePresentation` for the
three chart coordinates. -/
theorem hPoly_locallyOfFinitePresentation_of_fp (h : Polynomial ℚ) (hh : h ≠ 0) :
    LocallyOfFinitePresentation (hPoly h hh) :=
  hPoly_locallyOfFinitePresentation h hh
    (locallyOfFinitePresentation_chartMorphismInf h (evalAt_finitePresentation h))
    (locallyOfFinitePresentation_chartMorphismInf (hPolyT h)
      (evalAt_finitePresentation (hPolyT h)))
    (locallyOfFinitePresentation_chartMorphism0 (hPolyLam h)
      (evalAt_finitePresentation (hPolyLam h)))

/-- Alias of `hPoly_locallyOfFinitePresentation_of_fp` under the name used in the O4 task sheet. -/
theorem hPolyLocallyOfFinitePresentation_of_fp (h : Polynomial ℚ) (hh : h ≠ 0) :
    LocallyOfFinitePresentation (hPoly h hh) :=
  hPoly_locallyOfFinitePresentation_of_fp h hh

/-- **O4+O5, closed**: `hPolyL h hh` is locally of finite presentation, unconditionally. -/
theorem hPolyL_locallyOfFinitePresentation_of_fp (h : Polynomial ℚ) (hh : h ≠ 0) :
    LocallyOfFinitePresentation (hPolyL h hh) := by
  haveI := hPoly_locallyOfFinitePresentation_of_fp h hh
  exact hPolyL_locallyOfFinitePresentation h hh

/-! ## Axiom checks -/

#print axioms evalAt_finiteType
#print axioms evalAt_finitePresentation
#print axioms hPolyChartInf_locallyOfFinitePresentation
#print axioms locallyOfFinitePresentation_chartMorphism0
#print axioms hPolyChart1_locallyOfFinitePresentation
#print axioms hPolyChart0_locallyOfFinitePresentation
#print axioms hPoly_locallyOfFinitePresentation
#print axioms hPolyL_locallyOfFinitePresentation
#print axioms hPoly_locallyOfFinitePresentation_of_fp
#print axioms hPolyLocallyOfFinitePresentation_of_fp
#print axioms hPolyL_locallyOfFinitePresentation_of_fp

end LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyLoFPActual
