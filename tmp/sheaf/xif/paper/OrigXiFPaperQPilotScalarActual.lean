import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! # OrigXiF: actual paper q-pilot scalar from the L-carrier C3 q

This file is in the original Theta-link layer (**O**), not the normalized
model (N), the native target (T), or the SourceDefinition31Data contract (S).
It constructs the paper q-pilot signed log-volume directly from the actual
`SourcePilotRegionDataL` q element

  C3.q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place

and compares it with the scalar field of `PaperQPilotObject`.

## What is actual here

* `OrigXiFPaperQPilotLogVolume C3 = -|Real.log ||C3.q.q|||` is the paper
  signed q-pilot log-volume built from the actual L-carrier C3.  The scalar is
  not a fixed constant and is not the value `q = 1/5`: it is a function of the
  actual completion q, and the file proves
  `OrigXiFPaperQPilotLogVolume C3₁ = OrigXiFPaperQPilotLogVolume C3₂ ↔
   ||C3₁.q.q|| = ||C3₂.q.q||`.
* `actualSourcePilotRegionDataL` supplies the actual C3 unconditionally from
  S1391's concrete root/Kummer/tensor block; the scalar at that C3 is
  `Real.log ||(concreteQCandidate I place).q||`.

## Exact first field

`PaperQPilotObject.qPilotLogVolume_eq` is the field

  O.qPilotLogVolume = sourceQPilotSignedLog I.initial,

where `sourceQPilotSignedLog I.initial` is the negative sum of the bad-place
q-parameter absolute logs of the SourceDefinition31Data contract.  The actual
L-carrier C3 carries one completion q, not that bad-place family.  Therefore
the compatibility statement

  O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3

is proved to be **exactly equivalent** to the scalar identification

  sourceQPilotSignedLog I.initial = OrigXiFPaperQPilotLogVolume C3,

i.e. to

  -sum_b |log q_b| = -|log ||C3.q.q|||.

That equality is recorded as `OrigXiFPaperQPilotScalarExactFirstField`.  It is
a named `Prop`; this file constructs no inhabitant for it, because the actual
L-carrier q and the contract bad-place family are not related by the available
source data.  The conditional theorem
`OrigXiFPaperQPilotObject_qPilotLogVolume_eq_neg_abs` shows that once the
exact first field is supplied, the object scalar is precisely the actual
`-|log q|`.  No True/PUnit/empty-type/axiom/sorry is used to fill the gap.

No inhabitant of `PaperQPilotObject` is asserted.  No normalized or native
qVFam scalar is introduced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual

universe upi umon ui uG uL uC

variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}

/-! ## 1. The actual paper q-pilot scalar from C3.q.q -/

/-- The paper q-pilot signed log-volume `-|log q|` of the actual L-carrier C3,
computed from the actual completion element `C3.q.q`. -/
noncomputable def OrigXiFPaperQPilotLogVolume
    (C3 : SourcePilotRegionDataL (I := I)) : Real :=
  -|Real.log ‖C3.q.q‖|

/-- The scalar is definitionally the paper form `-|log q|`. -/
theorem OrigXiFPaperQPilotLogVolume_eq_neg_abs_log_q
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFPaperQPilotLogVolume C3 = -|Real.log ‖C3.q.q‖| := rfl

/-- Because the actual q-candidate is contracting, `-|log q|` is the signed
completion log `log ||q||`. -/
theorem OrigXiFPaperQPilotLogVolume_eq_log_norm
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFPaperQPilotLogVolume C3 = Real.log ‖C3.q.q‖ := by
  unfold OrigXiFPaperQPilotLogVolume
  have hneg : Real.log ‖C3.q.q‖ < 0 :=
    ArithmeticQPilotLogVolume.localSignedLog_neg C3.q
  rw [abs_of_neg hneg, neg_neg]

/-- The actual paper q-pilot scalar is strictly negative. -/
theorem OrigXiFPaperQPilotLogVolume_neg
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFPaperQPilotLogVolume C3 < 0 := by
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm]
  exact ArithmeticQPilotLogVolume.localSignedLog_neg C3.q

/-- The actual paper q-pilot scalar is nonzero. -/
theorem OrigXiFPaperQPilotLogVolume_ne_zero
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFPaperQPilotLogVolume C3 ≠ 0 :=
  ne_of_lt (OrigXiFPaperQPilotLogVolume_neg (I := I) C3)

/-- The scalar exponentiates back to the actual completion norm. -/
theorem OrigXiFPaperQPilotLogVolume_exp
    (C3 : SourcePilotRegionDataL (I := I)) :
    Real.exp (OrigXiFPaperQPilotLogVolume C3) = ‖C3.q.q‖ := by
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm,
    Real.exp_log (ArithmeticQPilotLogVolume.qNorm_pos C3.q)]

/-- The scalar is not a fixed constant: equality of two actual paper scalars is
equivalent to equality of the two actual completion norms. -/
theorem OrigXiFPaperQPilotLogVolume_eq_iff_norm_eq
    (C3₁ C3₂ : SourcePilotRegionDataL (I := I)) :
    OrigXiFPaperQPilotLogVolume C3₁ = OrigXiFPaperQPilotLogVolume C3₂ ↔
      ‖C3₁.q.q‖ = ‖C3₂.q.q‖ := by
  constructor
  · intro h
    have hlog : Real.log ‖C3₁.q.q‖ = Real.log ‖C3₂.q.q‖ := by
      simpa [OrigXiFPaperQPilotLogVolume_eq_log_norm] using h
    have hexp := congrArg Real.exp hlog
    simpa [Real.exp_log (ArithmeticQPilotLogVolume.qNorm_pos C3₁.q),
      Real.exp_log (ArithmeticQPilotLogVolume.qNorm_pos C3₂.q)] using hexp
  · intro h
    rw [OrigXiFPaperQPilotLogVolume_eq_log_norm,
      OrigXiFPaperQPilotLogVolume_eq_log_norm, h]

/-! ## 2. The actual L-carrier C3 instance -/

/-- The actual L-carrier C3 has the concrete q candidate as its q field. -/
theorem OrigXiFActualC3_q
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    (actualSourcePilotRegionDataL (I := I) place).q =
      concreteQCandidate (I := I) place := rfl

/-- The actual L-carrier C3 has the concrete q candidate as its completion
q element. -/
theorem OrigXiFActualQPilotLogVolume_eq_log_concreteQCandidate
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    OrigXiFPaperQPilotLogVolume
        (actualSourcePilotRegionDataL (I := I) place) =
      Real.log ‖(concreteQCandidate (I := I) place).q‖ := by
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm, OrigXiFActualC3_q]
  rfl

/-- The actual L-carrier scalar is `-|log q|` for the concrete q. -/
theorem OrigXiFActualQPilotLogVolume_eq_neg_abs_log_q
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    OrigXiFPaperQPilotLogVolume
        (actualSourcePilotRegionDataL (I := I) place) =
      -|Real.log ‖(concreteQCandidate (I := I) place).q‖| :=
  OrigXiFPaperQPilotLogVolume_eq_neg_abs_log_q (I := I)
    (actualSourcePilotRegionDataL (I := I) place)

/-- The actual L-carrier scalar is strictly negative. -/
theorem OrigXiFActualQPilotLogVolume_neg
    {p : Nat} [Fact p.Prime]
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p) :
    OrigXiFPaperQPilotLogVolume
        (actualSourcePilotRegionDataL (I := I) place) < 0 :=
  OrigXiFPaperQPilotLogVolume_neg (I := I)
    (actualSourcePilotRegionDataL (I := I) place)

/-! ## 3. Compatibility with `PaperQPilotObject.qPilotLogVolume_eq` -/

/-- Scalar compatibility with the paper q-pilot object: the object scalar is
the actual L-carrier q-pilot scalar. -/
def OrigXiFPaperQPilotScalarCompatibility
    (O : PaperQPilotObject (Label := Label) (Choice := Choice)
      I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I)) : Prop :=
  O.qPilotLogVolume = OrigXiFPaperQPilotLogVolume C3

/-- The exact first scalar field of the compatibility with
`PaperQPilotObject.qPilotLogVolume_eq`: the contract bad-place q-log sum is the
actual L-carrier q-pilot scalar. -/
def OrigXiFPaperQPilotScalarExactFirstField
    (C3 : SourcePilotRegionDataL (I := I)) : Prop :=
  sourceQPilotSignedLog I.initial = OrigXiFPaperQPilotLogVolume C3

/-- Compatibility with the object's `qPilotLogVolume_eq` is exactly the
recorded scalar identification. -/
theorem OrigXiFPaperQPilotScalarCompatibility_iff_exactFirstField
    (O : PaperQPilotObject (Label := Label) (Choice := Choice)
      I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFPaperQPilotScalarCompatibility O C3 ↔
      OrigXiFPaperQPilotScalarExactFirstField (I := I) C3 := by
  unfold OrigXiFPaperQPilotScalarCompatibility
    OrigXiFPaperQPilotScalarExactFirstField
  rw [O.qPilotLogVolume_eq]

/-- The exact first field in the signed form
`-sum_b |log q_b| = log ||C3.q.q||`. -/
theorem OrigXiFPaperQPilotScalarExactFirstField_iff_signed
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFPaperQPilotScalarExactFirstField (I := I) C3 ↔
      -sourceBadQAbsLog I.initial = Real.log ‖C3.q.q‖ := by
  unfold OrigXiFPaperQPilotScalarExactFirstField sourceQPilotSignedLog
  rw [OrigXiFPaperQPilotLogVolume_eq_log_norm]

/-- The exact first field in the paper `-|log|` form. -/
theorem OrigXiFPaperQPilotScalarExactFirstField_iff_neg_abs
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFPaperQPilotScalarExactFirstField (I := I) C3 ↔
      -sourceBadQAbsLog I.initial = -|Real.log ‖C3.q.q‖| := by
  unfold OrigXiFPaperQPilotScalarExactFirstField sourceQPilotSignedLog
    OrigXiFPaperQPilotLogVolume
  rfl

/-- The exact first field fully unfolded as the equality of the bad-place
absolute-log sum with the actual completion q-pilot scalar. -/
theorem OrigXiFPaperQPilotScalarExactFirstField_iff_sum
    (C3 : SourcePilotRegionDataL (I := I)) :
    OrigXiFPaperQPilotScalarExactFirstField (I := I) C3 ↔
      (letI := I.initial.bad_finite;
       -(∑ b : I.initial.badPlaces,
           |Real.log (I.initial.reduction.qParameter b)|) =
         -|Real.log ‖C3.q.q‖|) := by
  rw [OrigXiFPaperQPilotScalarExactFirstField_iff_neg_abs]
  unfold sourceBadQAbsLog
  rfl

/-- Conditional compatibility: supplying the exact first field makes the
object scalar the actual paper q-pilot scalar. -/
theorem OrigXiFPaperQPilotScalarCompatibility_of_exactFirstField
    (O : PaperQPilotObject (Label := Label) (Choice := Choice)
      I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I))
    (h : OrigXiFPaperQPilotScalarExactFirstField (I := I) C3) :
    OrigXiFPaperQPilotScalarCompatibility O C3 :=
  (OrigXiFPaperQPilotScalarCompatibility_iff_exactFirstField
    (I := I) O C3).mpr h

/-- Conditional scalar compatibility with the object field: under the exact
first field, `O.qPilotLogVolume` is precisely the actual `-|log q|`. -/
theorem OrigXiFPaperQPilotObject_qPilotLogVolume_eq_neg_abs
    (O : PaperQPilotObject (Label := Label) (Choice := Choice)
      I G envStrip)
    (C3 : SourcePilotRegionDataL (I := I))
    (h : OrigXiFPaperQPilotScalarExactFirstField (I := I) C3) :
    O.qPilotLogVolume = -|Real.log ‖C3.q.q‖| := by
  rw [OrigXiFPaperQPilotScalarCompatibility_of_exactFirstField
      (I := I) O C3 h,
    OrigXiFPaperQPilotLogVolume_eq_neg_abs_log_q]

/-! ## 4. Axiom checks -/

#print axioms OrigXiFPaperQPilotLogVolume
#print axioms OrigXiFPaperQPilotLogVolume_eq_log_norm
#print axioms OrigXiFPaperQPilotLogVolume_eq_iff_norm_eq
#print axioms OrigXiFActualQPilotLogVolume_eq_log_concreteQCandidate
#print axioms OrigXiFPaperQPilotScalarCompatibility_iff_exactFirstField
#print axioms OrigXiFPaperQPilotScalarExactFirstField_iff_sum

end LeanFormal.IUT.XiFPaper.OrigXiFPaperQPilotScalarActual

end
