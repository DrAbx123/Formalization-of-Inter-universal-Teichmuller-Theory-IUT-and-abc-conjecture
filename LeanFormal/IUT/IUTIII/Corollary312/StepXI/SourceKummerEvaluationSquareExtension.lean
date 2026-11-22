import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The reduced Remark-3.10.2 square: extension from three free legs

This module reduces the row `G1-SRC` of the Card-SHE residual table
(`logs/coordination/outsider-survey-transport-20261016.md`, section 17.3):
the inhabitability of the reduced commuting square
`Theorem311Source.SourceKummerEvaluationSquare` (Remark 3.10.2) is factored
through the four *free* data:

* the upper (vertically coric) evaluation arrow;
* the left and the right Kummer arrows;
* the lower unit portion (Card EV at the lower pair of strips).

The fourth leg -- the lower horizontal -- is then forced at the strip level by
the paper's own construction instruction: "each of these lower horizontal
arrows may be constructed by conjugating the corresponding upper horizontal
arrow by the relevant Kummer isomorphisms" (IUT III, Remark 3.10.2).  The
forced formula is `lowerHorizontal.stripIso = leftKummer ; (upperHorizontal ;
rightKummer^{-1})`, recovered from any square as the readback theorem
`lowerHorizontal_stripIso_eq`.

## What is and is NOT claimed

* Claimed: the inhabitability characterization
  `sourceKummerEvaluationSquare_nonempty_iff`; the readback of the forced
  lower strip representative from the recorded commutation; and the gate-only
  satisfiability witness `sourceKummerEvaluationSquare_self`.
* NOT claimed: any source-level construction of the evaluation or Kummer
  arrows (rows S2-KU / S2-EV remain the explicit condition), and NOT the
  Theta-times-mu-LGP compatibility for an *independently constructed* lower
  horizontal (Card SQ: that equality, for a lower horizontal supplied by the
  Corollary 4.10, (ii), evaluation isomorphism, is paper content, not proved
  here).  The reduced square compares composites of isomorphism
  representatives; it does not identify the two arithmetic holomorphic
  structures (SHE trap T4 of the DSH-F report).
* The two Card-IPL G1 negative results are not re-proved (cited boundary).

## Consumer

`Theorem311Source.SourceKummerEvaluationSquare.sheSupply` and
`sheLinkSquare` (`SourceSHETransportObligations.lean`) consume exactly an
inhabitant of this square; by the characterization below, the SHE conditional
assembly is discharged by the three free legs plus one lower unit portion, and
by nothing else at this reduced interface.
-/

namespace LeanFormal.IUT

universe uv upi umon uG

noncomputable section

variable {V : Type uv}

namespace FPrimeStripEquiv

/-- Left cancellation in the representative groupoid: the inverse of a
representative, followed by the representative itself, cancels on the left of
any subsequent leg.  Companion of `trans_symm` / `symm_trans`
(`SourceFTimesMuPrimeStripPolyIsomorphism.lean`) in the associativity shape
used by the conjugation formula of Remark 3.10.2. -/
theorem symm_trans_cancel {A B C : FPrimeStrip.{umon, uv, upi} V}
    (e : FPrimeStripEquiv B A) (f : FPrimeStripEquiv A C) :
    FPrimeStripEquiv.trans (FPrimeStripEquiv.symm e)
      (FPrimeStripEquiv.trans e f) = f := by
  rw [← Theorem311Source.OriginalInput.FPrimeStripEquiv.trans_assoc,
    Theorem311Source.OriginalInput.FPrimeStripEquiv.symm_trans e,
    Theorem311Source.OriginalInput.FPrimeStripEquiv.trans_refl_left]

end FPrimeStripEquiv

namespace Theorem311Source
namespace SourceKummerEvaluationSquare

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {upperLeft upperRight lowerLeft lowerRight : FPrimeStrip.{umon, uv, upi} V}

/-- Extension of three free legs to a full reduced square: the lower
horizontal is constructed by conjugating the upper horizontal by the two
Kummer representatives (the construction direction of Remark 3.10.2); its
unit portion is the supplied lower unit portion. -/
def ofThreeLegs
    (upperHorizontal : SourceEvaluationArrow G upperLeft upperRight)
    (leftKummer : SourceKummerArrow G lowerLeft upperLeft)
    (rightKummer : SourceKummerArrow G lowerRight upperRight)
    (lowerUnitPortion : SourceEvaluationUnitPortion G lowerLeft lowerRight) :
    SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight where
  upperHorizontal := upperHorizontal
  lowerHorizontal :=
    { stripIso := leftKummer.stripIso.trans
        (upperHorizontal.stripIso.trans rightKummer.stripIso.symm)
      unitPortion := lowerUnitPortion }
  leftKummer := leftKummer
  rightKummer := rightKummer
  commutes := FPrimeStripEquiv.symm_trans_cancel leftKummer.stripIso
    (upperHorizontal.stripIso.trans rightKummer.stripIso.symm)

@[simp] theorem ofThreeLegs_upperHorizontal
    (upperHorizontal : SourceEvaluationArrow G upperLeft upperRight)
    (leftKummer : SourceKummerArrow G lowerLeft upperLeft)
    (rightKummer : SourceKummerArrow G lowerRight upperRight)
    (lowerUnitPortion : SourceEvaluationUnitPortion G lowerLeft lowerRight) :
    (ofThreeLegs upperHorizontal leftKummer rightKummer lowerUnitPortion).upperHorizontal =
      upperHorizontal := rfl

@[simp] theorem ofThreeLegs_leftKummer
    (upperHorizontal : SourceEvaluationArrow G upperLeft upperRight)
    (leftKummer : SourceKummerArrow G lowerLeft upperLeft)
    (rightKummer : SourceKummerArrow G lowerRight upperRight)
    (lowerUnitPortion : SourceEvaluationUnitPortion G lowerLeft lowerRight) :
    (ofThreeLegs upperHorizontal leftKummer rightKummer lowerUnitPortion).leftKummer =
      leftKummer := rfl

@[simp] theorem ofThreeLegs_rightKummer
    (upperHorizontal : SourceEvaluationArrow G upperLeft upperRight)
    (leftKummer : SourceKummerArrow G lowerLeft upperLeft)
    (rightKummer : SourceKummerArrow G lowerRight upperRight)
    (lowerUnitPortion : SourceEvaluationUnitPortion G lowerLeft lowerRight) :
    (ofThreeLegs upperHorizontal leftKummer rightKummer lowerUnitPortion).rightKummer =
      rightKummer := rfl

/-- Inhabitability characterization (the reduction of `G1-SRC`): a reduced
square exists exactly when the upper evaluation arrow, the two Kummer arrows
and the lower unit portion exist.  The remaining source obligations are
therefore exactly the arrow bodies (rows S2-KU / S2-EV) plus one Card-EV unit
portion instance at the lower pair; the square itself adds no independent
source content at this reduced interface. -/
theorem sourceKummerEvaluationSquare_nonempty_iff :
    Nonempty (SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight) ↔
      Nonempty (SourceEvaluationArrow G upperLeft upperRight) ∧
        Nonempty (SourceKummerArrow G lowerLeft upperLeft) ∧
        Nonempty (SourceKummerArrow G lowerRight upperRight) ∧
        Nonempty (SourceEvaluationUnitPortion G lowerLeft lowerRight) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨⟨S.upperHorizontal⟩, ⟨S.leftKummer⟩, ⟨S.rightKummer⟩,
      ⟨S.lowerHorizontal.unitPortion⟩⟩
  · rintro ⟨⟨upperHorizontal⟩, ⟨leftKummer⟩, ⟨rightKummer⟩, ⟨lowerUnitPortion⟩⟩
    exact ⟨ofThreeLegs upperHorizontal leftKummer rightKummer lowerUnitPortion⟩

/-- Readback of the forced lower strip representative from the recorded
commutation: in any square, the lower horizontal's strip-level representative
is the conjugation of the upper horizontal by the two Kummer representatives.
This is the conjugation formula of Remark 3.10.2, recovered from the square. -/
theorem lowerHorizontal_stripIso_eq
    (S : SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight) :
    S.lowerHorizontal.stripIso =
      S.leftKummer.stripIso.trans
        (S.upperHorizontal.stripIso.trans S.rightKummer.stripIso.symm) := by
  calc S.lowerHorizontal.stripIso
      = FPrimeStripEquiv.trans (FPrimeStripEquiv.refl lowerLeft)
          S.lowerHorizontal.stripIso :=
        (OriginalInput.FPrimeStripEquiv.trans_refl_left
          S.lowerHorizontal.stripIso).symm
    _ = FPrimeStripEquiv.trans
          (FPrimeStripEquiv.trans S.leftKummer.stripIso
            (FPrimeStripEquiv.symm S.leftKummer.stripIso))
          S.lowerHorizontal.stripIso := by
        rw [FPrimeStripEquiv.trans_symm S.leftKummer.stripIso]
    _ = FPrimeStripEquiv.trans S.leftKummer.stripIso
          (FPrimeStripEquiv.trans (FPrimeStripEquiv.symm S.leftKummer.stripIso)
            S.lowerHorizontal.stripIso) :=
        OriginalInput.FPrimeStripEquiv.trans_assoc S.leftKummer.stripIso
          (FPrimeStripEquiv.symm S.leftKummer.stripIso)
          S.lowerHorizontal.stripIso
    _ = FPrimeStripEquiv.trans S.leftKummer.stripIso
          (FPrimeStripEquiv.trans S.upperHorizontal.stripIso
            (FPrimeStripEquiv.symm S.rightKummer.stripIso)) := by
        rw [S.commutes]

/-- Gate-only satisfiability witness for the extended record: the reduced
square is inhabited at the degenerate (identity-strip, trivial-action)
instance.  As for `sourceKummerArrow_self` / `sourceEvaluationArrow_self`,
this witnesses satisfiability of the frozen records only; it is not a source
construction of the paper's arrows. -/
theorem sourceKummerEvaluationSquare_self
    (S : FPrimeStrip.{umon, uv, upi} V) :
    Nonempty (SourceKummerEvaluationSquare G S S S S) := by
  obtain ⟨upper⟩ := sourceEvaluationArrow_self (G := G) S
  obtain ⟨leftK⟩ := sourceKummerArrow_self (G := G) S
  obtain ⟨rightK⟩ := sourceKummerArrow_self (G := G) S
  exact ⟨ofThreeLegs upper leftK rightK
    { sourceAction := fun _ => 1
      targetAction := fun _ => 1
      unitLayer := fun v => MulEquiv.refl (TimesMuQuotient ((S.Mon v)ˣ))
      unitLayer_equivariant := fun _ _ _ => rfl }⟩

end SourceKummerEvaluationSquare
end Theorem311Source

end

namespace Audit

/-- The reduced Remark-3.10.2 square extends from three free legs; this is
the inhabitability reduction of the `G1-SRC` residual (row 8 of the Card-SHE
residual table). -/
def sourceKummerEvaluationSquareExtension : Obligation :=
  { id := "IUT-III.source-kummer-evaluation-square-extension"
    source :=
      "IUT III, Remark 3.10.2 (conjugation); Remark 3.11.1, (iii); " ++
        "Corollary 3.12, proof, Step (xi-b)"
    status := VerificationStatus.interface
    note :=
      "Extension of the reduced Remark-3.10.2 square from three free legs " ++
        "(upper evaluation arrow, left and right Kummer arrows) plus one " ++
        "lower unit portion; the lower horizontal is forced at the strip " ++
        "level by the paper's conjugation instruction, with the readback " ++
        "theorem lowerHorizontal_stripIso_eq and the inhabitability " ++
        "characterization sourceKummerEvaluationSquare_nonempty_iff. NOT " ++
        "constructed: the source-level bodies of the arrows (rows S2-KU / " ++
        "S2-EV). NOT proved: the Theta-x-mu-LGP compatibility for an " ++
        "independently constructed lower horizontal (Card SQ). The two " ++
        "Card-IPL G1 negative results are not re-proved."
    dependsOn :=
      [ "IUT-III.source-kummer-evaluation-arrows",
        "IUT-III.source-SHE-obligations",
        "IUT-I-II.prime-strip-core" ] }

end Audit

end LeanFormal.IUT
