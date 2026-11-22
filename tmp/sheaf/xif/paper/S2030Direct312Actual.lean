import tmp.sheaf.xif.paper.S1940PaperLStarDeterminantActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.xif.paper.OrigXiFPaperSignedHullActual
import tmp.sheaf.xif.paper.NativeBadFintypeForTActual

/-!
# S2030: the direct paper Corollary 3.12 inequality without S1880PaperO,
# and the Fintype audit of the bad-place source set

Layer: **O** (original-text Theta-link / IUT III Corollary 3.12, Step (xi-f)).

## 1. What is proved on the paper datum

S1944 proves

  s1944_paper312_inequality :
    -|log q| <= OrigXiFSignedThetaHullLogVolume (S1944D T)

by `s1880_xiF_inequality_abs (S1944D T)`, whose module
`S1880OriginalXiFActual` also carries the paper object `S1880PaperO`.  This file
gives a **direct** proof of the same inequality at the same datum without
importing that module:

* S1938's general numerical criterion
  `s1938_neg_abs_log_q_le_neg_average_of_average_le_one` states that for every
  actual determinant `P` with procession average at most one,

    -|log q| <= -average P;

* S1940 proves
  `s1940PaperLStarDeterminant_processionNormalized`:
  the paper l* source determinant has procession average `a0`;

* S1915 proves `s1915_a0_le_one : a0 <= 1`;

* S1944D's signed hull log-volume is `-a0` by the structure field
  `hull_logVolume_eq_procession` and `OrigXiFSignedThetaHullLogVolume_eq_neg_average`.

Hence the paper inequality is the numerical chain

  -|log q| <= -a0,

with no Haar readout, no S1880 comparison, and no `S1880PaperO` on the proof
path.

**Import note.**  S1938's module imports S1905, which imports
`S1880OriginalXiFActual`; importing S1938 would therefore put S1880PaperO back
into the transitive import cone, although S1938's general criterion itself does
not use it.  To keep the S1880 module out of this package's cone, the criterion
is restated here under the name
`s2030_neg_abs_log_q_le_neg_average_of_average_le_one` with exactly S1938's
statement and exactly S1938's three-line proof (S1487's magnitude bound
`log 5 <= |log q|` plus `1 < log 5`).  A consumer that already imports S1938 can
use `s1938_neg_abs_log_q_le_neg_average_of_average_le_one` interchangeably; the
two statements are identical.

## 2. The `[Fintype (Bad (nativePlaceSelection T))]` audit

The bare source record

  structure SourcePlaceSelection (A : InitialThetaArithmeticData l) where
    V_mod_bad : Set (NumberField.FinitePlace A.Fmod)
    V_mod_bad_odd_residue_characteristic : ...
    V_mod_bad_nonempty : V_mod_bad.Nonempty

(LeanFormal/IUT/IUTI/InitialTheta/SourcePlaceSelection.lean:31-37) contains
**no finiteness field**, whereas

  Bad P = {p : NumberField.FinitePlace A.Fmod // p ∈ P.V_mod_bad}

(SourcePlacePartitionReduction.lean:188-189).  On the bare record the finiteness
of `Bad P` is therefore an extra hypothesis, not a consequence of the three
listed fields.  Section 2 records this exactly:

* `s2030_bad_fintype_of_finite` : `P.V_mod_bad.Finite -> Nonempty (Fintype (Bad P))`;
* `SourcePlaceSelectionFinite` : the corrected source selection carrying
  `V_mod_bad_finite : V_mod_bad.Finite`, with a `Fintype (Bad P)` instance;
* `SourceNativeInitialThetaDataFinite` : the corrected paper datum carrying the
  same finiteness field.

For the *full* source datum the hypothesis is not missing: Clause B
(`multiplicative_over_bad`) plus
`Definition31BadReductionFiniteness.exists_finite_goodReduction_off` and the
local disjointness theorem prove `T.tuple.source.V_mod_bad.Finite`
(`NativeBadFintypeForTActual.nativeBadSetFinite`, imported here).  Consequently
the `[Fintype]` parameter of S1944 is redundant: section 3 defines the paper
datum `s2030D T h` from an explicit finite-set proof `h` and proves 3.12 with
**no `[Fintype]` binder**.  The unconditional form uses
`h := nativeBadSetFinite T`; the corrected-source form uses
`h := T.V_mod_bad_finite` on `SourceNativeInitialThetaDataFinite`.

## 3. What is not claimed

No `sorry`, `admit`, `axiom`, `True`/`PUnit` slot, arbitrary datum, or fake
measure is used.  The only local instances are the standard irreducibility of
`X^2 + 1` over `Q` and primality of 5, needed to read the actual completion q
exactly as in S1487/S1880/S1938/S1944.  The theorems below are about the same
actual S1902 theta hull and the same actual S1940 paper l* determinant as S1944;
the datum `s2030D T h` has those exact fields.  The honest boundary is that
`SourcePlaceSelection` alone still does not carry the finite-set condition; the
file supplies the corrected record and shows that the paper datum already
satisfies it.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S2030Direct312Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.OrigXiF
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.S1940PaperLStarDeterminantActual
open LeanFormal.IUT.XiFPaperThetaHull
open scoped BigOperators

universe u

variable {l : PrimeGeFive}

/-- The concrete Gaussian field Q(i) is an AdjoinRoot, so its Field instance
needs the irreducibility fact; this is the same local instance used by
S1487/S1880/S1938/S1944 when reading the actual completion q. -/
local instance s2030GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2030FivePrime : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ## 1. The general numerical criterion (S1938, restated) -/

/-- `1 < log 5`, the numerical input of the criterion. -/
theorem s2030_one_lt_log_five : (1 : ℝ) < Real.log 5 := by
  have h : Real.log (Real.exp 1) < Real.log 5 :=
    Real.log_lt_log (Real.exp_pos 1)
      (lt_trans Real.exp_one_lt_three (by norm_num))
  rwa [Real.log_exp] at h

/-- `|log q| = localLogMagnitude S1487Cand` for the actual completion q. -/
theorem s2030_abs_log_q_eq_magnitude :
    |Real.log ‖S1487Cand.q‖| = localLogMagnitude S1487Cand :=
  abs_localSignedLog S1487Cand

/-- `log 5 <= |log q|` for the actual completion q (S1487). -/
theorem s2030_log_five_le_abs_log_q :
    Real.log 5 ≤ |Real.log ‖S1487Cand.q‖| := by
  rw [s2030_abs_log_q_eq_magnitude]
  exact S1487Cand_magnitude_ge_log_five

/-- **The general 3.12 criterion**, exactly S1938's
`s1938_neg_abs_log_q_le_neg_average_of_average_le_one`: every actual
determinant whose procession average is at most one satisfies
`-|log q| <= -average`. -/
theorem s2030_neg_abs_log_q_le_neg_average_of_average_le_one
    (P : SignedHullLogActual (SignedLabel l.value))
    (hP : s1904ProcessionAverage P ≤ 1) :
    -|Real.log ‖S1487Cand.q‖| ≤ -s1904ProcessionAverage P := by
  have hq := s2030_log_five_le_abs_log_q
  have h1 := s2030_one_lt_log_five
  linarith

/-- The criterion in the paper's `localLogMagnitude` form. -/
theorem s2030_neg_magnitude_le_neg_average_of_average_le_one
    (P : SignedHullLogActual (SignedLabel l.value))
    (hP : s1904ProcessionAverage P ≤ 1) :
    -localLogMagnitude S1487Cand ≤ -s1904ProcessionAverage P := by
  rw [← s2030_abs_log_q_eq_magnitude]
  exact s2030_neg_abs_log_q_le_neg_average_of_average_le_one P hP

/-! ## 2. Finiteness of the bad-place set: audit and corrected records -/

/-- **The exact additional hypothesis on a bare source selection.**  If the
source selection's bad moduli set is finite, then `Bad P` has a `Fintype`.
This is the only missing field of `SourcePlaceSelection` relevant to the
`[Fintype (Bad ...)]` parameter. -/
theorem s2030_bad_fintype_of_finite
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A) (h : P.V_mod_bad.Finite) :
    Nonempty (Fintype (Bad P)) := by
  haveI : Finite (Bad P) := h.to_subtype
  exact ⟨Fintype.ofFinite _⟩

/-- The corrected source selection: the three fields of `SourcePlaceSelection`
together with the finite-set condition that the original record omits. -/
structure SourcePlaceSelectionFinite {l : PrimeGeFive}
    (A : InitialThetaArithmeticData.{u} l) extends SourcePlaceSelection A where
  V_mod_bad_finite : V_mod_bad.Finite

namespace SourcePlaceSelectionFinite

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
variable (P : SourcePlaceSelectionFinite A)

/-- The corrected selection's bad moduli set is finite. -/
theorem finite : P.toSourcePlaceSelection.V_mod_bad.Finite :=
  P.V_mod_bad_finite

/-- The finite-set condition gives the `Fintype` on the bad places. -/
noncomputable instance instFintypeBad :
    Fintype (Bad P.toSourcePlaceSelection) := by
  haveI : Finite (Bad P.toSourcePlaceSelection) := P.V_mod_bad_finite.to_subtype
  exact Fintype.ofFinite _

end SourcePlaceSelectionFinite

/-- The corrected paper datum: the full native source datum together with the
finite-set condition on its bad moduli places. -/
structure SourceNativeInitialThetaDataFinite (l : PrimeGeFive) where
  toSourceNativeInitialThetaData : SourceNativeInitialThetaData.{0} l
  V_mod_bad_finite : toSourceNativeInitialThetaData.tuple.source.V_mod_bad.Finite

namespace SourceNativeInitialThetaDataFinite

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaDataFinite l)

/-- The corrected native datum's bad-place `Fintype`, derived from the carried
finiteness proof (no `[Fintype]` hypothesis). -/
noncomputable instance instFintypeBad :
    Fintype (Bad (nativePlaceSelection T.toSourceNativeInitialThetaData)) := by
  have h : (nativePlaceSelection T.toSourceNativeInitialThetaData).V_mod_bad.Finite := by
    simpa only [nativePlaceSelection] using T.V_mod_bad_finite
  haveI : Finite (Bad (nativePlaceSelection T.toSourceNativeInitialThetaData)) :=
    h.to_subtype
  exact Fintype.ofFinite _

end SourceNativeInitialThetaDataFinite

/-- The fully unconditional finiteness theorem for the paper source datum:
`nativeBadSetFinite` uses Clause B and the actual finite bad-reduction support.
It is stated here to make the audit self-contained. -/
theorem s2030_native_bad_set_finite
    (T : SourceNativeInitialThetaData.{0} l) :
    T.tuple.source.V_mod_bad.Finite :=
  LeanFormal.IUT.N8Closure.NativeBadFintypeForTActual.nativeBadSetFinite T

/-- The `Fintype` on the bad places of an arbitrary paper source datum, with no
`[Fintype]` hypothesis. -/
@[reducible] noncomputable def s2030FintypeOfFinite
    (T : SourceNativeInitialThetaData.{0} l)
    (h : T.tuple.source.V_mod_bad.Finite) :
    Fintype (Bad (nativePlaceSelection T)) := by
  have h' : (nativePlaceSelection T).V_mod_bad.Finite := by
    simpa only [nativePlaceSelection] using h
  haveI : Finite (Bad (nativePlaceSelection T)) := h'.to_subtype
  exact Fintype.ofFinite _

/-! ## 3. The paper datum and the direct 3.12 -/

section WithFinite
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual paper signed-hull datum at the S1902 theta hull and the S1940
paper l* determinant.  This is definitionally the S1944D datum. -/
noncomputable def s2030DOf :
    OrigXiFPaperSignedHullData (S1902Carrier T) l where
  thetaHull := s1902ActualThetaHull T
  determinant := s1940PaperLStarDeterminant T
  hull_logVolume_eq_procession := s1940_s1904_bridge T

/-- The theta hull of the paper datum is the actual S1902 theta hull. -/
theorem s2030DOf_thetaHull :
    (s2030DOf T).thetaHull = s1902ActualThetaHull T := rfl

/-- The determinant-side average of the paper datum is the actual S1915 readout
`a0` (S1940). -/
theorem s2030DOf_average_eq_a0 :
    s1904ProcessionAverage (s2030DOf T).determinant = s1915A0 T := by
  change (s1940PaperLStarDeterminant T).processionNormalizedLogVolume = s1915A0 T
  exact s1940PaperLStarDeterminant_processionNormalized T

/-- The determinant-side average is at most one (S1915). -/
theorem s2030DOf_average_le_one :
    s1904ProcessionAverage (s2030DOf T).determinant ≤ 1 := by
  rw [s2030DOf_average_eq_a0]
  exact s1915_a0_le_one T

/-- The signed hull log-volume of the paper datum is `-a0`. -/
theorem s2030DOf_signed_eq_neg_a0 :
    OrigXiFSignedThetaHullLogVolume (s2030DOf T) = -s1915A0 T := by
  rw [OrigXiFSignedThetaHullLogVolume_eq_neg_average]
  change -((s1940PaperLStarDeterminant T).processionNormalizedLogVolume) = -s1915A0 T
  rw [s1940PaperLStarDeterminant_processionNormalized]

end WithFinite

/-- The paper datum with the bad-place `Fintype` constructed from an explicit
finite-set proof `h`.  This is the same datum as S1944D; the instance is a
local let, so the *statement* of the public theorems below has no
`[Fintype]` binder. -/
noncomputable def s2030D
    (T : SourceNativeInitialThetaData.{0} l)
    (h : T.tuple.source.V_mod_bad.Finite) :
    OrigXiFPaperSignedHullData (S1902Carrier T) l :=
  letI : Fintype (Bad (nativePlaceSelection T)) := s2030FintypeOfFinite T h
  s2030DOf T

/-- The determinant average of `s2030D` is at most one.  This is the
determinant-side normalization needed by the general criterion. -/
theorem s2030D_average_le_one
    (T : SourceNativeInitialThetaData.{0} l)
    (h : T.tuple.source.V_mod_bad.Finite) :
    s1904ProcessionAverage (s2030D T h).determinant ≤ 1 := by
  letI : Fintype (Bad (nativePlaceSelection T)) := s2030FintypeOfFinite T h
  change s1904ProcessionAverage (s2030DOf T).determinant ≤ 1
  exact s2030DOf_average_le_one T

/-- **The direct paper Corollary 3.12 inequality**, with the `Fintype` on the bad
places derived from an explicit finite-set proof.  No S1880 comparison occurs. -/
theorem s2030_paper312_inequality_of_finite
    (T : SourceNativeInitialThetaData.{0} l)
    (h : T.tuple.source.V_mod_bad.Finite) :
    -|Real.log ‖S1487Cand.q‖| ≤
      OrigXiFSignedThetaHullLogVolume (s2030D T h) := by
  have hle := s2030D_average_le_one T h
  rw [OrigXiFSignedThetaHullLogVolume_eq_neg_average]
  exact s2030_neg_abs_log_q_le_neg_average_of_average_le_one
    ((s2030D T h).determinant) hle

/-- The same inequality in the paper's `localLogMagnitude` form. -/
theorem s2030_paper312_inequality_magnitude_of_finite
    (T : SourceNativeInitialThetaData.{0} l)
    (h : T.tuple.source.V_mod_bad.Finite) :
    -localLogMagnitude S1487Cand ≤
      OrigXiFSignedThetaHullLogVolume (s2030D T h) := by
  have hmain := s2030_paper312_inequality_of_finite T h
  rw [← s2030_abs_log_q_eq_magnitude]
  exact hmain

/-- The strict form: `-|log q| < -|log Theta|`. -/
theorem s2030_paper312_strict_of_finite
    (T : SourceNativeInitialThetaData.{0} l)
    (h : T.tuple.source.V_mod_bad.Finite) :
    -|Real.log ‖S1487Cand.q‖| <
      OrigXiFSignedThetaHullLogVolume (s2030D T h) := by
  have hle : (s2030D T h).determinant.procession.average ≤ 1 := by
    change s1904ProcessionAverage (s2030D T h).determinant ≤ 1
    exact s2030D_average_le_one T h
  rw [OrigXiFSignedThetaHullLogVolume_eq_neg_average]
  have h1 : (1 : ℝ) < Real.log 5 := s2030_one_lt_log_five
  have h2 : Real.log 5 ≤ |Real.log ‖S1487Cand.q‖| := s2030_log_five_le_abs_log_q
  linarith

/-! ## 4. The unconditional forms (no `[Fintype]` hypothesis) -/

/-- **The unconditional direct paper 3.12**, with the bad-place `Fintype`
constructed from `s2030_native_bad_set_finite`.  This is the same statement as
S1944's `s1944_paper312_inequality`, but its proof uses S1938's numerical
criterion, S1940's average = `a0`, S1915's `a0 <= 1`, and the S1944D signed
value = `-a0`; it does not use S1880 or `S1880PaperO`. -/
theorem s2030_paper312_inequality
    (T : SourceNativeInitialThetaData.{0} l) :
    -|Real.log ‖S1487Cand.q‖| ≤
      OrigXiFSignedThetaHullLogVolume (s2030D T (s2030_native_bad_set_finite T)) :=
  s2030_paper312_inequality_of_finite T (s2030_native_bad_set_finite T)

/-- The unconditional `localLogMagnitude` form. -/
theorem s2030_paper312_inequality_magnitude
    (T : SourceNativeInitialThetaData.{0} l) :
    -localLogMagnitude S1487Cand ≤
      OrigXiFSignedThetaHullLogVolume (s2030D T (s2030_native_bad_set_finite T)) :=
  s2030_paper312_inequality_magnitude_of_finite T (s2030_native_bad_set_finite T)

/-- The unconditional strict form. -/
theorem s2030_paper312_strict
    (T : SourceNativeInitialThetaData.{0} l) :
    -|Real.log ‖S1487Cand.q‖| <
      OrigXiFSignedThetaHullLogVolume (s2030D T (s2030_native_bad_set_finite T)) :=
  s2030_paper312_strict_of_finite T (s2030_native_bad_set_finite T)

/-- **The correct-source form**: on `SourceNativeInitialThetaDataFinite`, where
the bad-set finiteness is a field of the corrected source record, 3.12 holds
with no `[Fintype]` hypothesis. -/
theorem s2030_paper312_inequality_of_sourceFinite
    (T : SourceNativeInitialThetaDataFinite l) :
    -|Real.log ‖S1487Cand.q‖| ≤
      OrigXiFSignedThetaHullLogVolume
        (s2030D T.toSourceNativeInitialThetaData T.V_mod_bad_finite) :=
  s2030_paper312_inequality_of_finite T.toSourceNativeInitialThetaData
    T.V_mod_bad_finite

/-- The correct-source `localLogMagnitude` form. -/
theorem s2030_paper312_inequality_magnitude_of_sourceFinite
    (T : SourceNativeInitialThetaDataFinite l) :
    -localLogMagnitude S1487Cand ≤
      OrigXiFSignedThetaHullLogVolume
        (s2030D T.toSourceNativeInitialThetaData T.V_mod_bad_finite) :=
  s2030_paper312_inequality_magnitude_of_finite T.toSourceNativeInitialThetaData
    T.V_mod_bad_finite

/-- The full paper package at the unconditional datum: the determinant-side
normalization and 3.12 both hold. -/
theorem s2030_paper312_package
    (T : SourceNativeInitialThetaData.{0} l) :
    s1904ProcessionAverage
        (s2030D T (s2030_native_bad_set_finite T)).determinant ≤ 1 ∧
      -|Real.log ‖S1487Cand.q‖| ≤
        OrigXiFSignedThetaHullLogVolume
          (s2030D T (s2030_native_bad_set_finite T)) :=
  ⟨s2030D_average_le_one T (s2030_native_bad_set_finite T),
    s2030_paper312_inequality T⟩

/-! ## 5. Axiom probes -/

#print axioms s2030_one_lt_log_five
#print axioms s2030_abs_log_q_eq_magnitude
#print axioms s2030_log_five_le_abs_log_q
#print axioms s2030_neg_abs_log_q_le_neg_average_of_average_le_one
#print axioms s2030_neg_magnitude_le_neg_average_of_average_le_one
#print axioms s2030_bad_fintype_of_finite
#print axioms SourcePlaceSelectionFinite.instFintypeBad
#print axioms SourceNativeInitialThetaDataFinite.instFintypeBad
#print axioms s2030_native_bad_set_finite
#print axioms s2030DOf
#print axioms s2030DOf_average_eq_a0
#print axioms s2030DOf_signed_eq_neg_a0
#print axioms s2030D
#print axioms s2030D_average_le_one
#print axioms s2030_paper312_inequality_of_finite
#print axioms s2030_paper312_inequality
#print axioms s2030_paper312_inequality_magnitude
#print axioms s2030_paper312_strict
#print axioms s2030_paper312_inequality_of_sourceFinite
#print axioms s2030_paper312_package

end LeanFormal.IUT.XiFPaper.S2030Direct312Actual
