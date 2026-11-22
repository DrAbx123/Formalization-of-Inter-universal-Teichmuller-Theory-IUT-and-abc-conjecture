import tmp.sheaf.xif.paper.S1707ThreeTorsionFCardActual

/-!
# S1708: nine distinct F-rational 3-torsion points

S1707 reduced Nat.card E_F[3] = 9 to the lower bound

  9 ≤ Nat.card E_F[3].

This file closes exactly that lower bound by an explicit injection
Fin 9 → E_F[3] built from nine points that S1687 already supplies:

* 0;
* the six points (A(y_i^2), y_i), where y_i enumerates the six roots of
  S1687H in the S1687 splitting field and A = S1687A is the x-coordinate
  polynomial on t = y^2;
* the two rational points P = (25/16, 225/128) and -P.

## Distinctness arguments

* Two root points have equal y-coordinates, and the roots are enumerated
  injectively by Fin 6; hence the six root points are pairwise distinct.
* P ≠ -P: at P the y-coordinate is 225/128, while -P has the
  y-coordinate negY x y = -y on this curve (both a1 = a3 = 0), and
  225/128 ≠ -225/128 in characteristic zero.
* A root point and ±P have different x-coordinates: a root point has
  x = A(y^2) with F(A(y^2)) = 0 for the residual cubic F = S1687F, while
  the x-coordinate of ±P is 25/16, and F(25/16) = 151875/16 ≠ 0.
* 0 is different from every affine point by Affine.Point.some_ne_zero.

The card comparison is the requested one: Fintype.card_le_of_injective
gives 9 ≤ Nat.card E_F[3]; the opposite inequality is the S1705 descent
injection E_F[3] ↪ E_K[3] together with S1704's geometric count
Nat.card E_K[3] = 9.  The proof is complete and uses only the standard
classical foundational principles.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1708NinePointInjectionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1702AllTorsionRationalActual
open LeanFormal.IUT.XiFPaper.S1704TorsionCardActual
open LeanFormal.IUT.XiFPaper.S1705AllTorsionRationalActual
open LeanFormal.IUT.XiFPaper.S1706FCardActual
open LeanFormal.IUT.XiFPaper.S1707ThreeTorsionFCardActual
open Polynomial WeierstrassCurve WeierstrassCurve.Affine

local instance : DecidableEq S1687Field := Classical.decEq _
local instance : DecidableEq S1702Closure := Classical.decEq _

/-! ## 1. Enumeration of the six roots of S1687H -/

/-- An explicit enumeration of the six roots of the S1687 defining polynomial
by Fin 6.  Existence follows from the actual cardinality
Nat.card (S1687H.rootSet S1687Field) = 6 proved in S1687. -/
noncomputable def S1708RootEquiv : Fin 6 ≃ S1687H.rootSet S1687Field :=
  (Fintype.equivFinOfCardEq
    (by rw [← Nat.card_eq_fintype_card]; exact S1687SixRootsDistinct)).symm

/-- The i-th actual root of S1687H in the S1687 splitting field. -/
noncomputable def S1708Root (i : Fin 6) : S1687Field :=
  (S1708RootEquiv i).1

theorem S1708Root_mem (i : Fin 6) :
    S1708Root i ∈ S1687H.rootSet S1687Field :=
  (S1708RootEquiv i).2

/-- Each enumerated value is a genuine root of the defining polynomial. -/
theorem S1708Root_root (i : Fin 6) : aeval (S1708Root i) S1687H = 0 := by
  have h := S1708Root_mem i
  rw [Polynomial.mem_rootSet_of_ne S1687H_ne_zero] at h
  exact h

/-- The root enumeration is injective, hence the six root points have
pairwise distinct y-coordinates. -/
theorem S1708Root_injective : Function.Injective S1708Root := by
  intro i j h
  apply S1708RootEquiv.injective
  exact Subtype.ext h

/-! ## 2. The residual cubic at 25/16 and the coordinates of ±P -/

/-- The residual cubic does not vanish at the x-coordinate 25/16 of the
rational 3-torsion points. -/
theorem S1708F_eval_25_16 : S1687F.eval (25/16 : ℚ) = 151875/16 := by
  unfold S1687F
  norm_num

/-- Evaluation of the residual cubic at the base-changed rational point. -/
theorem S1708_aeval_F_25_16 :
    aeval (algebraMap ℚ S1687Field (25/16)) S1687F =
      algebraMap ℚ S1687Field (151875/16) := by
  rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, S1708F_eval_25_16]

/-- On this curve negY x y = -y because a1 = a3 = 0. -/
theorem S1708_negY (x y : S1687Field) : S1687AffineF.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY, S1687AffineF, S1687CurveF, S1667Curve,
    WeierstrassCurve.baseChange, WeierstrassCurve.map, WeierstrassCurve.toAffine]

/-- P ≠ -P: the two points have opposite nonzero y-coordinates. -/
theorem S1708RationalP_ne_neg : S1687RationalP ≠ -S1687RationalP := by
  intro h
  have hy := (Affine.Point.some.inj h).2
  rw [S1708_negY] at hy
  norm_num at hy

/-! ## 3. Distinctness of the six root points and ±P -/

/-- The root-point map is injective on the six enumerated roots. -/
theorem S1708RootPoint_injective {i j : Fin 6}
    (h : S1687RootPoint (S1708Root i) (S1708Root_root i) =
      S1687RootPoint (S1708Root j) (S1708Root_root j)) : i = j := by
  have hy := (Affine.Point.some.inj h).2
  exact S1708Root_injective hy

/-- A root point is not P: its x-coordinate is a root of F, while the
x-coordinate of P is 25/16 and F(25/16) ≠ 0. -/
theorem S1708RootPoint_ne_ratP (i : Fin 6) :
    S1687RootPoint (S1708Root i) (S1708Root_root i) ≠ S1687RationalP := by
  intro h
  have hx := (Affine.Point.some.inj h).1
  have hF := S1687Root_alpha_f (S1708Root i) (S1708Root_root i)
  rw [hx] at hF
  rw [S1708_aeval_F_25_16] at hF
  have hq : (151875/16 : ℚ) = 0 :=
    (algebraMap ℚ S1687Field).injective (by simpa using hF)
  norm_num at hq

/-- A root point is not -P: negation preserves the x-coordinate, so the
same residual-cubic argument applies. -/
theorem S1708RootPoint_ne_negRatP (i : Fin 6) :
    S1687RootPoint (S1708Root i) (S1708Root_root i) ≠ -S1687RationalP := by
  intro h
  have h' : -S1687RootPoint (S1708Root i) (S1708Root_root i) = S1687RationalP := by
    rw [h, neg_neg]
  have hx := (Affine.Point.some.inj h').1
  have hF := S1687Root_alpha_f (S1708Root i) (S1708Root_root i)
  rw [hx] at hF
  rw [S1708_aeval_F_25_16] at hF
  have hq : (151875/16 : ℚ) = 0 :=
    (algebraMap ℚ S1687Field).injective (by simpa using hF)
  norm_num at hq

/-- Every affine point is nonzero, in particular a root point. -/
theorem S1708RootPoint_ne_zero (i : Fin 6) :
    S1687RootPoint (S1708Root i) (S1708Root_root i) ≠ 0 :=
  Affine.Point.some_ne_zero (S1687Root_nonsingular (S1708Root i) (S1708Root_root i))

/-- The rational point P is nonzero. -/
theorem S1708RationalP_ne_zero : S1687RationalP ≠ 0 :=
  Affine.Point.some_ne_zero S1687RationalP_nonsingular

/-- The rational point -P is nonzero. -/
theorem S1708NegRationalP_ne_zero : -S1687RationalP ≠ 0 := by
  intro h
  exact S1708RationalP_ne_zero (neg_eq_zero.mp h)

/-! ## 4. The nine points as an explicit injective family -/

/-- The requested carrier: F-rational points killed by 3. -/
abbrev S1708F3 : Type := {Q : S1687AffineF.Point // (3 : ℤ) • Q = 0}

/-- The S1705 F-torsion type is definitionally the requested carrier. -/
theorem S1708F3_eq : S1708F3 = S1705FTorsion3 := rfl

/-- The zero point, as an F-rational 3-torsion point. -/
def S1708Zero : S1708F3 := ⟨(0 : S1687AffineF.Point), zsmul_zero 3⟩

/-- The root point attached to the k-th enumerated root. -/
def S1708RootPt (k : Fin 6) : S1708F3 :=
  ⟨S1687RootPoint (S1708Root k) (S1708Root_root k), S1687RootPoint_three _ _⟩

/-- The rational point P = (25/16, 225/128). -/
def S1708P : S1708F3 := ⟨S1687RationalP, S1687RationalP_three⟩

theorem S1708NegP_three :
    (3 : ℤ) • (-S1687RationalP : S1687AffineF.Point) = 0 := by
  rw [zsmul_neg, S1687RationalP_three, neg_zero]

/-- The rational point -P. -/
def S1708NegP : S1708F3 :=
  ⟨(-S1687RationalP : S1687AffineF.Point), S1708NegP_three⟩

/-- The index block decomposition underlying the nine-point family:
one zero point, six root points, then P and -P. -/
def S1708Split : Fin 9 ≃ (Fin 1 ⊕ (Fin 6 ⊕ (Fin 1 ⊕ Fin 1))) :=
  (finSumFinEquiv (m := 1) (n := 8)).symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin 1))
      ((finSumFinEquiv (m := 6) (n := 2)).symm.trans
        (Equiv.sumCongr (Equiv.refl (Fin 6))
          (finSumFinEquiv (m := 1) (n := 1)).symm)))

/-- The auxiliary block-wise family on the decomposition. -/
def S1708Aux : (Fin 1 ⊕ (Fin 6 ⊕ (Fin 1 ⊕ Fin 1))) → S1708F3
  | Sum.inl _ => S1708Zero
  | Sum.inr (Sum.inl k) => S1708RootPt k
  | Sum.inr (Sum.inr (Sum.inl _)) => S1708P
  | Sum.inr (Sum.inr (Sum.inr _)) => S1708NegP

theorem S1708RootPt_injective : Function.Injective S1708RootPt := by
  intro i j h
  exact S1708RootPoint_injective (congrArg Subtype.val h)

theorem S1708P_ne_negP : S1708P ≠ S1708NegP := by
  intro h
  exact S1708RationalP_ne_neg (congrArg Subtype.val h)

theorem S1708Zero_ne_rootPt (k : Fin 6) : S1708Zero ≠ S1708RootPt k := by
  intro h
  exact S1708RootPoint_ne_zero k (congrArg Subtype.val h).symm

theorem S1708Zero_ne_P : S1708Zero ≠ S1708P := by
  intro h
  exact S1708RationalP_ne_zero (congrArg Subtype.val h).symm

theorem S1708Zero_ne_negP : S1708Zero ≠ S1708NegP := by
  intro h
  exact S1708NegRationalP_ne_zero (congrArg Subtype.val h).symm

theorem S1708RootPt_ne_P (k : Fin 6) : S1708RootPt k ≠ S1708P := by
  intro h
  exact S1708RootPoint_ne_ratP k (congrArg Subtype.val h)

theorem S1708RootPt_ne_negP (k : Fin 6) : S1708RootPt k ≠ S1708NegP := by
  intro h
  exact S1708RootPoint_ne_negRatP k (congrArg Subtype.val h)

/-- The auxiliary block-wise family is injective. -/
theorem S1708Aux_injective : Function.Injective S1708Aux := by
  rintro (a | (b | (c | d))) (e | (f | (g | h1))) h
  · have : a = e := Subsingleton.elim a e
    subst this
    rfl
  · exact (S1708Zero_ne_rootPt f (by simpa [S1708Aux] using h)).elim
  · exact (S1708Zero_ne_P (by simpa [S1708Aux] using h)).elim
  · exact (S1708Zero_ne_negP (by simpa [S1708Aux] using h)).elim
  · exact (S1708Zero_ne_rootPt b (by simpa [S1708Aux] using h.symm)).elim
  · exact congrArg Sum.inr (congrArg Sum.inl (S1708RootPt_injective (by
      simpa [S1708Aux] using h)))
  · exact (S1708RootPt_ne_P b (by simpa [S1708Aux] using h)).elim
  · exact (S1708RootPt_ne_negP b (by simpa [S1708Aux] using h)).elim
  · exact (S1708Zero_ne_P (by simpa [S1708Aux] using h.symm)).elim
  · exact (S1708RootPt_ne_P f (by simpa [S1708Aux] using h.symm)).elim
  · have : c = g := Subsingleton.elim c g
    subst this
    rfl
  · exact (S1708P_ne_negP (by simpa [S1708Aux] using h)).elim
  · exact (S1708Zero_ne_negP (by simpa [S1708Aux] using h.symm)).elim
  · exact (S1708RootPt_ne_negP f (by simpa [S1708Aux] using h.symm)).elim
  · exact (S1708P_ne_negP (by simpa [S1708Aux] using h.symm)).elim
  · have : d = h1 := Subsingleton.elim d h1
    subst this
    rfl

/-- The nine explicit F-rational 3-torsion points, indexed by Fin 9:
index 0 is 0, indices 1-6 are the six root points, and indices 7, 8
are P and -P. -/
noncomputable def S1708NinePoints : Fin 9 → S1708F3 :=
  fun i => S1708Aux (S1708Split i)

/-- The nine-point family is injective. -/
theorem S1708NinePoints_injective : Function.Injective S1708NinePoints := by
  intro i j h
  exact S1708Split.injective (S1708Aux_injective h)

/-- Index 0 is the zero point. -/
theorem S1708NinePoints_zero : S1708NinePoints 0 = S1708Zero := rfl

/-- Index k + 1 is the k-th root point. -/
theorem S1708NinePoints_root (k : Fin 6) :
    S1708NinePoints ⟨k.val + 1, by omega⟩ = S1708RootPt k := by
  fin_cases k <;> rfl

/-- Index 7 is P. -/
theorem S1708NinePoints_seven : S1708NinePoints 7 = S1708P := rfl

/-- Index 8 is -P. -/
theorem S1708NinePoints_eight : S1708NinePoints 8 = S1708NegP := rfl

/-! ## 5. The cardinality comparison -/

/-- Transport the nine-point family to the S1705 F-torsion type along the
definitional identification of the two carriers. -/
noncomputable def S1708ToS1705 : S1708F3 ≃ S1705FTorsion3 :=
  Equiv.cast S1708F3_eq

/-- The nine-point family, regarded as a map into the S1705 F-torsion type. -/
noncomputable def S1708NinePointsF : Fin 9 → S1705FTorsion3 :=
  S1708ToS1705 ∘ S1708NinePoints

theorem S1708NinePointsF_injective : Function.Injective S1708NinePointsF :=
  S1708ToS1705.injective.comp S1708NinePoints_injective

/-- The closure cardinality Nat.card E_K[3] = 9 from S1704. -/
theorem S1708KTorsion3_card : Nat.card S1705KTorsion3 = 9 := by
  change Nat.card { P : S1702ClosurePoint // (3 : ℤ) • P = 0 } = 9
  exact S1704TorsionCardActual.threeTorsionCard

/-- The requested lower bound: the nine explicit points give at least nine
F-rational 3-torsion points. -/
theorem S1708NinePointLowerBound : S1707NinePointLowerBound := by
  change 9 ≤ Nat.card S1705FTorsion3
  haveI : Finite S1705KTorsion3 :=
    (Nat.card_ne_zero.mp (by rw [S1708KTorsion3_card]; norm_num)).2
  haveI : Finite S1705FTorsion3 :=
    Finite.of_injective S1705Descent3 S1705Descent3_injective
  haveI : Fintype S1705FTorsion3 := Fintype.ofFinite _
  have h := Fintype.card_le_of_injective S1708NinePointsF S1708NinePointsF_injective
  simpa using h

/-- The opposite bound, by the S1705 descent injection and the S1704 closure
cardinality. -/
theorem S1708ThreeTorsionFCard_le : Nat.card S1705FTorsion3 ≤ 9 := by
  haveI : Finite S1705KTorsion3 :=
    (Nat.card_ne_zero.mp (by rw [S1708KTorsion3_card]; norm_num)).2
  simpa [S1708KTorsion3_card] using
    Nat.card_le_card_of_injective S1705Descent3 S1705Descent3_injective

/-- The exact F-rational 3-torsion cardinality, closing the S1707 input. -/
theorem S1708ThreeTorsionFCard : S1705ThreeTorsionFCard :=
  le_antisymm S1708ThreeTorsionFCard_le
    (show 9 ≤ Nat.card S1705FTorsion3 from S1708NinePointLowerBound)

/-- The S1707 named missing input is now actual. -/
theorem S1708ThreeTorsionFCardMissing : S1707ThreeTorsionFCardMissing :=
  S1708ThreeTorsionFCard

/-- The S1707 conditional consumer, now discharged by the actual
F-rational 3-torsion cardinality. -/
theorem S1708Torsion23Rational :
    PuncturedEllipticCurve.Torsion23Rational (S1667Punctured.baseChange S1687Field) :=
  S1707Torsion23_of_threeCard S1708ThreeTorsionFCard

/-! ## 6. Axiom footprint -/

#check S1708NinePoints
#check S1708NinePoints_injective
#check S1708NinePointLowerBound
#check S1708ThreeTorsionFCard
#check S1708Torsion23Rational

#print axioms S1708NinePoints_injective
#print axioms S1708NinePointLowerBound
#print axioms S1708ThreeTorsionFCard
#print axioms S1708Torsion23Rational

end LeanFormal.IUT.XiFPaper.S1708NinePointInjectionActual
end
