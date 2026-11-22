import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Shape cards for Tate's algorithm and the Ogg-Saito formula at the prime `2`

This file records shape-only statements used by the two-adic analysis of the
abc-Frey family.  Every field is a slot for a later, separately verified
construction; no numerical value, fibre type, or conductor exponent is
endorsed here.

Source: coordination card set `estimates rec6`
(`logs/coordination/outsider-survey-estimates-20261016.md`, Section 3.3).

Literature freeze for this card set:

* Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*,
  Chapter IV: Section 9 "Tate's Algorithm to Compute the Special Fiber",
  Section 10 "The Conductor of an Elliptic Curve", Section 11 "Ogg's
  Formula".  The publisher table of contents places Ogg's formula in IV.11
  (the planning note's "IV.10" refers to the conductor section); the corpus
  file `papers/motizuki_corpus/text/Explicit estimates in IUTeich.txt`
  cites `[Silv2], Chapter IV, Section 10, Theorem 10.2, (a)`, `Example
  10.5` and `[Silv2], Chapter IV, Section 11, Ogg's Formula 11.1`.
* Saito, "Conductor, discriminant, and the Noether formula of arithmetic
  surfaces", Duke Mathematical Journal 57(1) (1988), 151-173,
  DOI 10.1215/s0012-7094-88-05706-7.

The slots below are not claimed to be fillable by existing work: the
two-adic conductor gap of `FreyConductorTwoAdic` remains open.
-/

namespace LeanFormal.IUT.ABCBridge.Geometry.TateOggSaitoTwoAdicCards

/-- Shape slot: the Kodaira type of the special fibre at the prime under
consideration (good reduction included). -/
inductive KodairaFiberTypeShape where
  | good
  | iN (n : ℕ)
  | iNStar (n : ℕ)
  | ii
  | iii
  | iv
  | ivStar
  | iiiStar
  | iiStar
deriving DecidableEq, Repr

/-- Shape card: the branch datum of Tate's algorithm at the prime `2`.
All fields are slots; no branch value is endorsed. -/
structure TateTwoAdicBranchData (E : WeierstrassCurve ℚ_[2]) where
  /-- Slot: the valuation of `c₄` of the considered model. -/
  c4Valuation : ℤ
  /-- Slot: the valuation of `c₆` of the considered model. -/
  c6Valuation : ℤ
  /-- Slot: the valuation of the discriminant of the considered model. -/
  discriminantValuation : ℤ
  /-- Slot: the resulting Kodaira type. -/
  fiberType : KodairaFiberTypeShape
  /-- Slot: the branch-table relation producing `fiberType`. -/
  branchRelation : Prop

/-- Shape card: the Tate / Ogg-Saito data behind the conductor exponent at
the prime `2`.  All fields are slots; no value is endorsed. -/
structure TateOggSaitoTwoAdicData (E : WeierstrassCurve ℚ_[2]) where
  /-- Slot: `ord_2` of the minimal discriminant. -/
  v₂Δmin : ℕ
  /-- Slot: the number of geometric components of the special fibre. -/
  m₂ : ℕ
  /-- Slot: the wild correction term (Saito 1988). -/
  swan₂ : ℕ

/-- Shape card: the Ogg-Saito relation for the conductor exponent at the
prime `2`, with all numerical entries as slots. -/
def conductorExponentTwoAdicFormula (E : WeierstrassCurve ℚ_[2])
    (d : TateOggSaitoTwoAdicData E) (f₂ : ℕ) : Prop :=
  f₂ = d.v₂Δmin + 1 - d.m₂ + d.swan₂

end LeanFormal.IUT.ABCBridge.Geometry.TateOggSaitoTwoAdicCards
