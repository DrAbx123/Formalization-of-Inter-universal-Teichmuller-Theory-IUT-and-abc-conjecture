import tmp.sheaf.xif.paper.S3135LogShellValueGroupActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceUnitRegionHaarDataActual

/-!
# Card (1): expansion of the log-shell value-group faithfulness, and its refutation at the concrete model

**task-17 (B).**  Card (1) asks for the value-group half of the actual log-shell
(IUT II, Example 1.8, (ix), iut2.txt:2402-2409: `I(G) ⊆ O^×μ(G)` is `p^{-1}` times
the image of the `G`-invariants of `O^×(G)`; cf. [AbsTopIII], Proposition 5.8, (ii);
Remark 3.9.4): the realization of the positive reals in the value monoid should be
degree-faithful.

## What is proved here

1. The set `S3135FaithfulExponents` of real exponents at which the actual realization
   is degree-faithful is an **additive submonoid** of `ℝ`: it contains `0` and is
   closed under addition (the monoid-homomorphism law plus additivity of the
   log-degree).  Consequently every natural multiple of the `q`-parameter log is
   faithful — a structural form of the cyclic case proved in task-11.
2. The exact missing datum is recorded as the structure
   `S3135ValueGroupSplitting` (a faithful value-group action); card (1) is exactly
   its nonemptiness.

## Refutation at the concrete value-layer model

The only concrete actual model of `SourceImageRealization`/
`SourceUnitRegionHaarData` in the tree (`SourceUnitRegionHaarDataActual.lean`) has
`q = 1` and the nonpositive value monoid; a group can only map trivially into a
monoid of nonpositive degrees, so its positive-real action is the trivial
homomorphism and `logDegreeAt (posRealAction (ofAdd x)) = 0` for every `x`.
This is proved here: **full and pointwise faithfulness are refuted on that concrete
model** (card (1) is therefore *not* a consequence of the source-realization /
Haar-data fields; it is the genuinely missing nontrivial value-group embedding of
IUT II, Example 1.8, (ix)).  The paper carrier's nontrivial realization is not
constructed in the tree, so card (1) remains the named exact missing.
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3135F4ActualHullResidualActual
open LeanFormal.IUT.XiFPaper.S3135ActualF4LogShellDegreeActual
open LeanFormal.IUT.XiFPaper.S3135LogShellValueGroupActual

namespace LeanFormal.IUT.XiFPaper.S3135LogShellFaithfulnessExpansionActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v)

/-! ## 1. The faithful-exponent set is an additive submonoid -/

/-- The real exponents at which the actual value-group realization is
degree-faithful. -/
def S3135FaithfulExponents : Set ℝ :=
  {x | I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd x)) = x}

/-- The exponent `0` is faithful (the realization sends `1` to `1`). -/
theorem s3135_faithful_zero : (0 : ℝ) ∈ S3135FaithfulExponents I v R := by
  show I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd (0 : ℝ))) = 0
  have hof : Multiplicative.ofAdd (0 : ℝ) = 1 := rfl
  rw [hof, map_one, I.logDegreeAt_one]

/-- The faithful exponents are closed under addition. -/
theorem s3135_faithful_add {x y : ℝ} (hx : x ∈ S3135FaithfulExponents I v R)
    (hy : y ∈ S3135FaithfulExponents I v R) :
    x + y ∈ S3135FaithfulExponents I v R := by
  show I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd (x + y))) = x + y
  have hof : Multiplicative.ofAdd (x + y) =
      Multiplicative.ofAdd x * Multiplicative.ofAdd y := rfl
  rw [hof, map_mul, I.logDegreeAt_mul]
  have hx' : I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd x)) = x := hx
  have hy' : I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd y)) = y := hy
  rw [hx', hy']

/-- The `q`-parameter log is a faithful exponent (the actual `degree_of_q` field). -/
theorem s3135_faithful_log_q :
    Real.log ((I.theaterAt 0 0).thetaPacket.q) ∈ S3135FaithfulExponents I v R :=
  R.degree_of_q

/-- Every natural multiple of the `q`-parameter log is a faithful exponent, as a
member of the additive submonoid of faithful exponents (structural form of the
task-11 cyclic-subgroup theorem). -/
theorem s3135_faithful_nsmul_log_q (k : ℕ) :
    k * Real.log ((I.theaterAt 0 0).thetaPacket.q) ∈ S3135FaithfulExponents I v R := by
  induction k with
  | zero => simpa using s3135_faithful_zero I v R
  | succ k ih =>
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have h1 : ((k : ℝ) + 1) * Real.log ((I.theaterAt 0 0).thetaPacket.q) =
        k * Real.log ((I.theaterAt 0 0).thetaPacket.q) +
          Real.log ((I.theaterAt 0 0).thetaPacket.q) := by ring
    rw [h1]
    exact s3135_faithful_add I v R ih (s3135_faithful_log_q I v R)

/-! ## 2. The exact missing datum -/

/-- **The exact missing datum of card (1)**: a faithful value-group action of the
positive reals in the actual value monoid — the value-group half of the log-shell
construction (IUT II, Example 1.8, (ix), iut2.txt:2402-2409; [AbsTopIII],
Proposition 5.8, (ii); Remark 3.9.4).  The actual source realization only records the
`q`-case (`SourceImageRealization.degree_of_q`); this structure is the precise
additional datum. -/
structure S3135ValueGroupSplitting (R : I.SourceImageRealization v) : Prop where
  /-- Degree faithfulness at every real log-shell exponent. -/
  faithful : ∀ x : ℝ,
    I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd x)) = x

/-- Card (1) is exactly the nonemptiness of the faithful value-group splitting. -/
theorem s3135_valueGroupSplitting_iff_faithfulness :
    S3135ValueGroupDegreeFaithfulness I v R ↔
      Nonempty (S3135ValueGroupSplitting (I := I) (v := v) R) := by
  constructor
  · intro h
    exact ⟨{ faithful := h }⟩
  · rintro ⟨h⟩
    exact h.faithful

/-! ## 3. Refutation at the concrete value-layer model -/

variable {l' : PrimeGeFive}
variable (S : SourceDefinition31Data.{ua} l')

/-- The concrete model's positive-real action is trivial, so its degree at every
exponent is `0`. -/
theorem sourceHaarActual_logDegree_posRealAction (x : ℝ) :
    (sourceHaarActualOriginalInput (l := l') S).logDegreeAt 0 0 ()
        ((sourceHaarActualImageRealization (l := l') S).posRealAction
          (Multiplicative.ofAdd x)) = 0 := by
  have hpos : (sourceHaarActualImageRealization (l := l') S).posRealAction
      (Multiplicative.ofAdd x) = 1 := rfl
  rw [hpos, (sourceHaarActualOriginalInput (l := l') S).logDegreeAt_one]

/-- **Full value-group faithfulness is refuted on the concrete actual model**: at
`x = 1` the left side is `0` but the right side is `1`.  Hence card (1) is not a
consequence of the source-realization datum: it is the missing nontrivial value-group
embedding (IUT II, Example 1.8, (ix)). -/
theorem sourceHaarActual_valueGroupFaithfulness_false :
    ¬ S3135ValueGroupDegreeFaithfulness (sourceHaarActualOriginalInput (l := l') S) ()
      (sourceHaarActualImageRealization (l := l') S) := by
  intro h
  have h1 := h 1
  rw [sourceHaarActual_logDegree_posRealAction (l' := l') S 1] at h1
  norm_num at h1

/-- `(1, 1, 2)` is an ABC triple. -/
theorem abcTriple_one_one_two : IsABCTriple 1 1 2 :=
  ⟨Nat.one_pos, Nat.one_pos, by norm_num, Nat.coprime_one_left 1⟩

/-- **Pointwise log-shell faithfulness is refuted on the concrete actual model**:
at the triple `(1,1,2)` the height exponent is strictly positive but the realized
log-degree is `0`. -/
theorem sourceHaarActual_pointFaithfulness_false :
    ¬ S3135PointLogShellFaithfulness (sourceHaarActualOriginalInput (l := l') S) ()
      (sourceHaarActualImageRealization (l := l') S) := by
  intro h
  have habc : IsABCTriple 1 1 2 := abcTriple_one_one_two
  have h1 := h 1 1 2 habc
  have hpos : (sourceHaarActualImageRealization (l := l') S).posRealAction
      (Multiplicative.ofAdd (Height.logHeight₁ (abcRationalPoint 1 2) /
        sourceVolumeIndexCard (l := l'))) = 1 := rfl
  rw [hpos, (sourceHaarActualOriginalInput (l := l') S).logDegreeAt_one] at h1
  have hlog2 : Height.logHeight₁ (abcRationalPoint 1 2) = Real.log 2 :=
    abcRationalPoint_logHeight₁ habc
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcard : (0 : ℝ) < sourceVolumeIndexCard (l := l') :=
    sourceVolumeIndexCard_pos (l := l')
  have hquot : 0 < Height.logHeight₁ (abcRationalPoint 1 2) /
      sourceVolumeIndexCard (l := l') := by
    rw [hlog2]
    exact div_pos hlog2pos hcard
  linarith

#check S3135FaithfulExponents
#check s3135_faithful_add
#check s3135_faithful_nsmul_log_q
#check S3135ValueGroupSplitting
#check sourceHaarActual_valueGroupFaithfulness_false
#check sourceHaarActual_pointFaithfulness_false

end LeanFormal.IUT.XiFPaper.S3135LogShellFaithfulnessExpansionActual
end
