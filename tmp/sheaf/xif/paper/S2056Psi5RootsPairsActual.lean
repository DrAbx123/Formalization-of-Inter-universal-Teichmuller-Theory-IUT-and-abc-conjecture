import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S2009DicksonActual
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2056Psi5RootsPairsActual

open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open Polynomial

/-- The actual odd 5-division polynomial of the S1667 curve. -/
noncomputable def S2056Psi5 : ℚ[X] :=
  S1667Curve.preΨ 5

/-- `psi_5` has degree 12. -/
theorem S2056Psi5_natDegree : S2056Psi5.natDegree = 12 := by
  unfold S2056Psi5
  rw [WeierstrassCurve.natDegree_preΨ (W := S1667Curve) (n := 5)]
  · norm_num
  · exact_mod_cast (by norm_num : (5 : ℕ) ≠ 0)

/-- `psi_5` is separable (actual S1942 certificate). -/
theorem S2056Psi5_separable : S2056Psi5.Separable := by
  unfold S2056Psi5
  letI : S1667Curve.IsElliptic := S1667Curve_isElliptic
  exact S1942_preΨ_five_separable S1667Curve

/-- The actual root set of `psi_5` in an algebraic closure. -/
abbrev S2056Psi5Roots : Type := S2056Psi5.rootSet (AlgebraicClosure ℚ)

/-- The root set cardinality: degree 12 and separability over the algebraic
closure. -/
theorem S2056Psi5RootsCardRequired :
    Nat.card S2056Psi5Roots = 12 := by
  rw [Nat.card_eq_fintype_card]
  let q : (AlgebraicClosure ℚ)[X] :=
    S2056Psi5.map (algebraMap ℚ (AlgebraicClosure ℚ))
  have hq : q.Splits := by
    simpa using (IsAlgClosed.splits_domain
      (f := RingHom.id (AlgebraicClosure ℚ)) q)
  have hsplit :
      (S2056Psi5.map (algebraMap ℚ (AlgebraicClosure ℚ))).Splits := by
    simpa [q] using hq
  have h := Polynomial.card_rootSet_eq_natDegree
    (p := S2056Psi5) (K := AlgebraicClosure ℚ)
    S2056Psi5_separable hsplit
  rw [h, S2056Psi5_natDegree]

/-- Actual bare bijection between the twelve psi5 roots and the twelve pairs.
This is the cardinality bijection, not yet the Galois-equivariant
x-coordinate bijection. -/
theorem S2056Psi5RootsPairsBijectionRequired :
    Nonempty (S2056Psi5Roots ≃ S2009Pairs) := by
  have hroot : Fintype.card S2056Psi5Roots = 12 := by
    simpa [Nat.card_eq_fintype_card] using S2056Psi5RootsCardRequired
  have hpair : Fintype.card S2009Pairs = 12 := card_pairRep
  exact ⟨Fintype.equivOfCardEq (hroot.trans hpair.symm)⟩

/-- Exact Dedekind factorization target at 29: the mod-29 reduction of psi_5
has irreducible factors of degrees 2 and 10.  The reduction map is part of the
missing certificate, not fabricated here. -/
def S2056Mod29FactorizationRequired : Prop :=
  ∃ (mod29 : ℚ[X] → (ZMod 29)[X]) (g2 g10 : (ZMod 29)[X]),
    Irreducible g2 ∧ Irreducible g10 ∧
      g2.natDegree = 2 ∧ g10.natDegree = 10

end LeanFormal.IUT.XiFPaper.S2056Psi5RootsPairsActual

end
