/-
# B1 / O3: the **equality** form of the `hPolyL` branch locus

Consumer: the B1 branch lane (`Mzk1G1PhiFixedLBranchSupportActual` and the O2/O3 ledger
`Mzk1G1B1ObligationsActual`).  `Mzk1G1B1HbObligationsActual.branch_hPolyL_subset` gives only
the inclusion `Branch (hPolyL h hh) ⊆ p1Inv '' Branch (hPoly h hh) ∪ Branch p1Inv`; this file
proves the **equality**

  `Branch (hPolyL h hh) = p1Inv '' Branch (hPoly h hh)`,

which is grace's `branch_hPolyL_eq` (that proof stalled on synthesising
`LocallyOfFinitePresentation`).

## The iso-cancellation equalities already exist in the donor

grep over `tmp/sheaf/xif/paper` shows that no `branch_isIso_comp_eq` has to be written: the
*equality* versions of both iso-cancellation laws are already in the donor
`Mzk1G1BelyiRamificationActual` (`Branch` at line 173, `branch_comp_subset` at line 249):

* `branch_isIso_comp (e : Z ⟶ X) [IsIso e] [LocallyOfFinitePresentation f] :
    Branch (e ≫ f) = Branch f`                                     (line 399)
* `branch_comp_isIso (e : Y ⟶ Z) [IsIso e] [LocallyOfFinitePresentation f] :
    Branch (f ≫ e) = e '' Branch f`                                (line 412)

So the task's item 1 is vacuous: this file does **not** restate them and uses them directly.

## The proof

`hPolyL h hh = p1Inv ≫ (hPoly h hh ≫ p1Inv)` (`hPolyL_def`, definitional).  Cancelling the
outer `p1Inv` with `branch_isIso_comp` and then the inner one with `branch_comp_isIso`:

  `Branch (p1Inv ≫ (hPoly ≫ p1Inv)) = Branch (hPoly ≫ p1Inv) = p1Inv '' Branch hPoly`.

`Branch p1Inv = ∅` (`branch_p1Inv_empty`) is not needed: the equality follows purely from the
iso-cancellation laws, the emptiness is a special case of it.

## `LocallyOfFinitePresentation`

`LocallyOfFinitePresentation (hPoly h hh)` and `(hPolyL h hh)` are **closed unconditionally**
by `Mzk1G1B1HPolyLoFPActual.hPolyLocallyOfFinitePresentation_of_fp` and
`hPolyL_locallyOfFinitePresentation_of_fp`; `LocallyOfFinitePresentation p1Inv` is synthesised
from `isIso_p1Inv` (`Mzk1G1B1HbObligationsActual`).  They are not registered global instances,
so — exactly as in `Mzk1G1B1HbObligationsActual` — the two `hPoly`/`hPolyL` instances are
carried as explicit typeclass binders on the main theorem (the O4 shape), and the corollary
`branch_hPolyL_eq_of_fp` discharges them from the donor theorems, so a consumer never has to
synthesise them.  (No downgrade of the statement is needed: the statement is the equality.)

No sorry, no admit, no new axioms.
-/
import tmp.sheaf.xif.paper.Mzk1G1B1HbObligationsActual
import tmp.sheaf.xif.paper.Mzk1G1B1HPolyLoFPActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyLambdaActual
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 800000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1BranchIsoEqActual

open LeanFormal.IUT.XiFPaper.BelyiRamification
open LeanFormal.IUT.XiFPaper.Mzk1G1B1HbObligationsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B1HPolyLoFPActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyLambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiP1InvActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual

/-! ## The equality for `hPolyL` -/

/-- **Equality form of the `hPolyL` branch locus**:
`Branch (hPolyL h hh) = p1Inv '' Branch (hPoly h hh)`.

`p1Inv` is an isomorphism (`isIso_p1Inv`), and `hPolyL h hh = p1Inv ≫ (hPoly h hh ≫ p1Inv)`
(`hPolyL_def`).  Two applications of the donor iso-cancellation *equalities* — the outer
`branch_isIso_comp` and the inner `branch_comp_isIso` — yield the result.  The
`LocallyOfFinitePresentation` instances for `hPoly` and `hPolyL` are the explicit O4 binders
(supplied unconditionally by `Mzk1G1B1HPolyLoFPActual`); see `branch_hPolyL_eq_of_fp`. -/
theorem branch_hPolyL_eq (h : Polynomial ℚ) (hh : h ≠ 0)
    [LocallyOfFinitePresentation (hPoly h hh)]
    [LocallyOfFinitePresentation (hPolyL h hh)] :
    Branch (hPolyL h hh) = p1Inv '' Branch (hPoly h hh) := by
  letI : IsIso p1Inv := isIso_p1Inv
  calc Branch (hPolyL h hh)
      = Branch (hPoly h hh ≫ p1Inv) :=
        branch_isIso_comp (f := hPoly h hh ≫ p1Inv) (e := p1Inv)
    _ = p1Inv '' Branch (hPoly h hh) :=
        branch_comp_isIso (f := hPoly h hh) (e := p1Inv)

#print axioms branch_hPolyL_eq

/-- **Consumer form, no instance bookkeeping**: the equality
`Branch (hPolyL h hh) = p1Inv '' Branch (hPoly h hh)` with the two
`LocallyOfFinitePresentation` instances discharged from the O4 theorems
`hPolyLocallyOfFinitePresentation_of_fp` and `hPolyL_locallyOfFinitePresentation_of_fp`.

The instance arguments are passed explicitly (`@Branch`) only because they are not global
instances; `LocallyOfFinitePresentation` is a proposition, so this is the same equality up to
proof irrelevance. -/
theorem branch_hPolyL_eq_of_fp (h : Polynomial ℚ) (hh : h ≠ 0) :
    @LeanFormal.IUT.XiFPaper.BelyiRamification.Branch _ _ (hPolyL h hh)
        (Mzk1G1B1HPolyLoFPActual.hPolyL_locallyOfFinitePresentation_of_fp h hh) =
      p1Inv '' @LeanFormal.IUT.XiFPaper.BelyiRamification.Branch _ _ (hPoly h hh)
        (Mzk1G1B1HPolyLoFPActual.hPolyLocallyOfFinitePresentation_of_fp h hh) := by
  haveI h1 : LocallyOfFinitePresentation (hPoly h hh) :=
    Mzk1G1B1HPolyLoFPActual.hPolyLocallyOfFinitePresentation_of_fp h hh
  haveI h2 : LocallyOfFinitePresentation (hPolyL h hh) :=
    Mzk1G1B1HPolyLoFPActual.hPolyL_locallyOfFinitePresentation_of_fp h hh
  exact branch_hPolyL_eq h hh

#print axioms branch_hPolyL_eq_of_fp

end LeanFormal.IUT.XiFPaper.Mzk1G1B1BranchIsoEqActual
