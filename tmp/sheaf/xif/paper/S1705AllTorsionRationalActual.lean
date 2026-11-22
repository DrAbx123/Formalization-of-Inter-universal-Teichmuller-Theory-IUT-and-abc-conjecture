import tmp.sheaf.xif.paper.S1704TorsionCardActual

/-! # S1705: from geometric torsion cards to AllNTorsionRational 2/3

S1704 proved the geometric cardinalities `Nat.card E[2] = 4` and
`Nat.card E[3] = 9` over the algebraic closure.  This file proves the
cardinality bridge: if the F-rational torsion subtype has the same finite
cardinality as the closure torsion subtype, then every closure torsion point
is a base change of an F-rational point.  The bridge uses only the actual
base-change map and its injectivity; no fake descent map is introduced.

The remaining exact inputs are the F-rational cardinalities:
`Nat.card E_F[2] = 4` and `Nat.card E_F[3] = 9`. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1705AllTorsionRationalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1702AllTorsionRationalActual
open LeanFormal.IUT.XiFPaper.S1704TorsionCardActual
open LeanFormal.IUT.XiFPaper.S1701Torsion23FullActual
open WeierstrassCurve WeierstrassCurve.Affine

local instance : DecidableEq S1687Field := Classical.decEq _
local instance : DecidableEq S1702Closure := Classical.decEq _

abbrev S1705F : Type := S1687Field
abbrev S1705K : Type := S1702Closure
abbrev S1705X := S1667Punctured.baseChange S1705F
abbrev S1705FPoint := S1705X.curve.toAffine.Point
abbrev S1705KPoint := (S1705X.curve.toAffine.baseChange S1705K).Point

noncomputable def S1705Descent : S1705FPoint →+ S1705KPoint :=
  Affine.Point.map (W' := S1705X.curve.toAffine)
    (f := Algebra.ofId S1705F S1705K)

theorem S1705Descent_injective : Function.Injective S1705Descent :=
  Affine.Point.map_injective
    (W' := S1705X.curve.toAffine)
    (f := Algebra.ofId S1705F S1705K)

abbrev S1705FTorsion2 : Type := { Q : S1705FPoint // (2 : ℤ) • Q = 0 }
abbrev S1705KTorsion2 : Type := { P : S1705KPoint // (2 : ℤ) • P = 0 }
abbrev S1705FTorsion3 : Type := { Q : S1705FPoint // (3 : ℤ) • Q = 0 }
abbrev S1705KTorsion3 : Type := { P : S1705KPoint // (3 : ℤ) • P = 0 }

noncomputable def S1705Descent2 : S1705FTorsion2 → S1705KTorsion2 :=
  fun Q => ⟨S1705Descent Q.1, by
    have h := congrArg S1705Descent Q.2
    simpa using h⟩

noncomputable def S1705Descent3 : S1705FTorsion3 → S1705KTorsion3 :=
  fun Q => ⟨S1705Descent Q.1, by
    have h := congrArg S1705Descent Q.2
    simpa using h⟩

theorem S1705Descent2_injective : Function.Injective S1705Descent2 := by
  intro Q R h
  apply Subtype.ext
  exact S1705Descent_injective (congrArg Subtype.val h)

theorem S1705Descent3_injective : Function.Injective S1705Descent3 := by
  intro Q R h
  apply Subtype.ext
  exact S1705Descent_injective (congrArg Subtype.val h)

def S1705TwoTorsionClosureCard : Prop :=
  Nat.card S1705KTorsion2 = 4

def S1705ThreeTorsionClosureCard : Prop :=
  Nat.card S1705KTorsion3 = 9

theorem S1705AllNTorsion2_of_card
    (hcardF : Nat.card S1705FTorsion2 = 4) :
    S1701Torsion2Rational := by
  change S1705X.AllNTorsionRational 2
  have hcardK : Nat.card S1705KTorsion2 = 4 := by
    change Nat.card { P : S1702ClosurePoint // (2 : ℤ) • P = 0 } = 4
    exact S1704TorsionCardActual.twoTorsionCard
  haveI : Finite S1705KTorsion2 :=
    (Nat.card_ne_zero.mp (by rw [hcardK]; norm_num)).2
  intro P hP
  have hrange : Set.range S1705Descent2 = Set.univ := by
    rw [Set.eq_univ_iff_ncard]
    rw [Set.ncard_range_of_injective S1705Descent2_injective]
    exact hcardF.trans hcardK.symm
  let P' : S1705KTorsion2 := ⟨P, hP⟩
  have hmem : P' ∈ Set.range S1705Descent2 := by
    rw [hrange]; exact Set.mem_univ _
  rcases hmem with ⟨Q, hQ⟩
  refine ⟨Q.1, ?_⟩
  change S1705Descent Q.1 = P
  have h := congrArg Subtype.val hQ
  dsimp [S1705Descent2] at h
  exact h

theorem S1705AllNTorsion3_of_card
    (hcardF : Nat.card S1705FTorsion3 = 9) :
    S1701Torsion3Rational := by
  change S1705X.AllNTorsionRational 3
  have hcardK : Nat.card S1705KTorsion3 = 9 := by
    change Nat.card { P : S1702ClosurePoint // (3 : ℤ) • P = 0 } = 9
    exact S1704TorsionCardActual.threeTorsionCard
  haveI : Finite S1705KTorsion3 :=
    (Nat.card_ne_zero.mp (by rw [hcardK]; norm_num)).2
  intro P hP
  have hrange : Set.range S1705Descent3 = Set.univ := by
    rw [Set.eq_univ_iff_ncard]
    rw [Set.ncard_range_of_injective S1705Descent3_injective]
    exact hcardF.trans hcardK.symm
  let P' : S1705KTorsion3 := ⟨P, hP⟩
  have hmem : P' ∈ Set.range S1705Descent3 := by
    rw [hrange]; exact Set.mem_univ _
  rcases hmem with ⟨Q, hQ⟩
  exact ⟨Q.1, congrArg Subtype.val hQ⟩

/-- F-rational 2-torsion cardinality (exact missing). -/
def S1705TwoTorsionFCard : Prop := Nat.card S1705FTorsion2 = 4

/-- F-rational 3-torsion cardinality (exact missing). -/
def S1705ThreeTorsionFCard : Prop := Nat.card S1705FTorsion3 = 9

theorem S1705Torsion23_of_FCards
    (h2 : S1705TwoTorsionFCard) (h3 : S1705ThreeTorsionFCard) :
    PuncturedEllipticCurve.Torsion23Rational
      (S1667Punctured.baseChange S1687Field) :=
  S1701Torsion23_of_parts
    (S1705AllNTorsion2_of_card h2)
    (S1705AllNTorsion3_of_card h3)

#check S1705AllNTorsion2_of_card
#check S1705AllNTorsion3_of_card
#check S1705TwoTorsionFCard
#check S1705ThreeTorsionFCard
#check S1705Torsion23_of_FCards

end LeanFormal.IUT.XiFPaper.S1705AllTorsionRationalActual
end
