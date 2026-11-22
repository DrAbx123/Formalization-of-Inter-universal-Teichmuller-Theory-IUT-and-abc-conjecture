import tmp.sheaf.xif.paper.S1630HDDOutputImageActual
import tmp.sheaf.xif.paper.S1644OutputDependentPointActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-! # S1669: output dependence from the actual Theorem 3.11 output

S1630 reduced the paper HDD image to `S1630OutputDependentIntegralPoint`:
a map from `Theorem311Output I` to the dependent local-field product, with
integral nonzero coordinates at every place and two outputs whose points
differ.  S1644 showed that singleton sources cannot supply it.  This file
examines the remaining actual source of output variation: the output record
itself.

## Findings

1. The raw output type is **not** a subsingleton.  The constructor
   `theorem311Output I` is a particular value, but `part_iii` contains a
   horizontal LGP link whose label functions can be shifted by one; this gives
   a second value `s1669AltOutput`.  So at least two raw output values exist.
   The second value is however **not** compatible with the actual SHE output
   record (`s1669AltOutput_not_SHEOutputActual`).

2. The second value differs only in `part_iii` label data.  It has the same
   `part_i`, `part_ii`, `source` and `quotient` as the actual constructor.
   Moreover every output whose three parts agree with the actual constructor is
   equal to it (`s1669HonestOutput_subsingleton`), and every actual
   `SHEOutputActual` record has exactly the constructor output
   (`s1669SHEOutputActual_output_unique`).  Thus all actual output values are
   one value; the only differences are modifications of `part_iii` (and
   potentially `part_i`) outside the SHE compatibility fields, not tied to
   the paper HDD data.

3. The actual output-dependent data that can reach the local-field product are
   constant: `source`, `quotient`, `part_ii`, the profile image
   `quotientImage I o.quotient` and the SHE reading map are all
   output-independent.  The q-pilot/theta data live in `Input`, not in
   `Theorem311Output`; no output field carries a local-field value.

4. Consequently the actual output type supplies no genuine output-to-local-field
   map.  The only actual output-to-local-field map used by the imported
   S1417/S1402 chain is the constant unit-section reading.

5. Nevertheless the formal condition in S1630 is too weak: the `part_iii`
   label does give an output-dependent natural number, and casting it to the
   completion gives an integral nonzero output-dependent point family
   (`s1669JunkPoint`).  This is a **junk** family, not the paper HDD image; we
   prove it exists to show that `S1630OutputDependentIntegralPoint` by itself
   is fake-inhabitable and does not capture genuineness.

6. The exact first missing object at the current interface is a
   *nondegenerate* output-dependent integral point family: output dependence
   plus exclusion of the constant reading and of the formal label
   construction.  This is recorded as
   `S1669NondegenerateOutputDependentPoint`; no inhabitant is asserted.  The
   available actual output data cannot supply it, and the junk construction is
   proved not to satisfy it.  This predicate is one minimal strengthening
   that excludes the two known degenerate fills; a full source-provenance
   predicate is not available in the current types, so the actual paper
   q-pilot/theta output-to-section map remains the real missing datum.

No unit reading image, free lattice or fake point is used as the paper object.
The junk point is used only as a counterexample to the strength of the S1630
condition, never as the paper image. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1669HDDOutputDependenceActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1417HDDImageFamilyActual
open LeanFormal.IUT.XiFPaper.S1513HDDOutputBindingActual
open LeanFormal.IUT.XiFPaper.S1551HDDImageGeneratorActual
open LeanFormal.IUT.XiFPaper.S1630HDDOutputImageActual
open LeanFormal.IUT.XiFPaper.S1644OutputDependentPointActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}
variable {s : Finset (NumberField.FinitePlace ℚ)}

/-! ## 1. The output type has at least two values -/

/-- A second value of the output type: shift the two label functions of the
horizontal LGP link in part (iii) by one, keeping the underlying maps and the
commuting square. -/
noncomputable def s1669AltPartIII : PartIII I :=
  { (theorem311Output I).part_iii with
    timesMuLink :=
      { (theorem311Output I).part_iii.timesMuLink with
        upper_label := fun c =>
          (theorem311Output I).part_iii.timesMuLink.upper_label c + 1
        lower_label := fun c =>
          (theorem311Output I).part_iii.timesMuLink.lower_label c + 1
        labels_agree := by
          intro c
          rw [(theorem311Output I).part_iii.timesMuLink.labels_agree c] } }

/-- The second output value. -/
noncomputable def s1669AltOutput : Theorem311Output I :=
  { theorem311Output I with part_iii := s1669AltPartIII (I := I) }

/-- The second output is genuinely different from the actual constructor. -/
theorem s1669AltOutput_ne : s1669AltOutput (I := I) ≠ theorem311Output I := by
  intro h
  have h3 : (s1669AltOutput (I := I)).part_iii = (theorem311Output I).part_iii := by
    rw [h]
  have hlink : (s1669AltOutput (I := I)).part_iii.timesMuLink =
      (theorem311Output I).part_iii.timesMuLink := by
    rw [h3]
  have hlab := congrArg (fun L : HorizontalLGPLink Choice Choice => L.upper_label)
    hlink
  have hval := congrFun hlab I.core.base
  change (theorem311Output I).part_iii.timesMuLink.upper_label I.core.base + 1 =
    (theorem311Output I).part_iii.timesMuLink.upper_label I.core.base at hval
  omega

/-- Therefore the actual output type is not a subsingleton. -/
theorem s1669Output_not_subsingleton : ¬ Subsingleton (Theorem311Output I) := by
  intro h
  exact s1669AltOutput_ne (I := I) (Subsingleton.elim _ _)

/-- The second output has the same part (i) as the actual constructor. -/
@[simp] theorem s1669AltOutput_part_i :
    (s1669AltOutput (I := I)).part_i = (theorem311Output I).part_i := rfl

/-- The second output has the same part (ii) as the actual constructor. -/
@[simp] theorem s1669AltOutput_part_ii :
    (s1669AltOutput (I := I)).part_ii = (theorem311Output I).part_ii := rfl

/-- The second output has the same source as the actual constructor. -/
@[simp] theorem s1669AltOutput_source :
    (s1669AltOutput (I := I)).source = (theorem311Output I).source := rfl

/-- The second output has the same quotient as the actual constructor. -/
@[simp] theorem s1669AltOutput_quotient :
    (s1669AltOutput (I := I)).quotient = (theorem311Output I).quotient := rfl

/-- The only difference between the second output and the actual constructor is
the part (iii) label data. -/
theorem s1669AltOutput_part_iii_ne :
    (s1669AltOutput (I := I)).part_iii ≠ (theorem311Output I).part_iii := by
  intro h
  have h' : s1669AltPartIII (I := I) = (theorem311Output I).part_iii := h
  apply s1669AltOutput_ne (I := I)
  rw [s1669AltOutput]
  rw [h']

/-- Outputs whose three parts agree with the actual constructor are all equal:
all remaining fields are determined by the two source/quotient equalities and
by proof irrelevance. -/
def s1669HonestOutput (I : Input Label Choice) : Type _ :=
  { o : Theorem311Output I //
      o.part_i = (theorem311Output I).part_i ∧
      o.part_ii = (theorem311Output I).part_ii ∧
      o.part_iii = (theorem311Output I).part_iii }

/-- The honest part of the output type is a subsingleton. -/
theorem s1669HonestOutput_subsingleton :
    Subsingleton (s1669HonestOutput I) := by
  constructor
  rintro ⟨o, ho⟩ ⟨o', ho'⟩
  obtain ⟨hi, hii, hiii⟩ := ho
  obtain ⟨hi', hii', hiii'⟩ := ho'
  apply Subtype.ext
  cases o
  cases o'
  simp_all
  exact ⟨hi.trans hi'.symm, hii.trans hii'.symm, hiii.trans hiii'.symm⟩

/-- A direct uniqueness corollary: an output whose three parts agree with the
actual constructor is exactly the actual constructor. -/
theorem s1669HonestOutput_eq (o : Theorem311Output I)
    (hi : o.part_i = (theorem311Output I).part_i)
    (hii : o.part_ii = (theorem311Output I).part_ii)
    (hiii : o.part_iii = (theorem311Output I).part_iii) :
    o = theorem311Output I := by
  exact congrArg Subtype.val
    (@Subsingleton.elim (s1669HonestOutput I)
      (s1669HonestOutput_subsingleton (I := I))
      ⟨o, hi, hii, hiii⟩
      ⟨theorem311Output I, rfl, rfl, rfl⟩)

/-- Any function of the actual output data is constant on the honest output
locus: the only freedom left in the formal output type is outside the three
actual parts (in the junk label modifications of part (iii)). -/
theorem s1669HonestOutput_function_constant {α : Type*}
    (f : Theorem311Output I → α) (o o' : Theorem311Output I)
    (ho : o.part_i = (theorem311Output I).part_i ∧
      o.part_ii = (theorem311Output I).part_ii ∧
      o.part_iii = (theorem311Output I).part_iii)
    (ho' : o'.part_i = (theorem311Output I).part_i ∧
      o'.part_ii = (theorem311Output I).part_ii ∧
      o'.part_iii = (theorem311Output I).part_iii) :
    f o = f o' := by
  rw [s1669HonestOutput_eq o ho.1 ho.2.1 ho.2.2,
    s1669HonestOutput_eq o' ho'.1 ho'.2.1 ho'.2.2]

/-! ## 1.1 Actual SHE output records have a unique output -/

/-- Every actual SHE output record has the output value produced by the actual
constructor.  This is the precise sense in which the actual output is unique:
`SHEOutputActual` pins all three parts, and the honest locus is a subsingleton. -/
theorem s1669SHEOutputActual_output_unique (S : SHEOutputActual I) :
    S.output = theorem311Output I :=
  s1669HonestOutput_eq S.output S.part_i_eq S.part_ii_eq S.part_iii_eq

/-- Two actual SHE output records have the same output. -/
theorem s1669SHEOutputActual_output_subsingleton
    (S T : SHEOutputActual I) : S.output = T.output :=
  (s1669SHEOutputActual_output_unique S).trans
    (s1669SHEOutputActual_output_unique T).symm

/-- The formal second output is not compatible with the actual SHE output
record: its part (iii) is not the actual part (iii). -/
theorem s1669AltOutput_not_SHEOutputActual :
    ¬ ∃ S : SHEOutputActual I, S.output = s1669AltOutput (I := I) := by
  rintro ⟨S, hS⟩
  have h : (s1669AltOutput (I := I)).part_iii =
      (theorem311Output I).part_iii := by
    rw [← hS, S.part_iii_eq, theorem311Output_part_iii]
  exact s1669AltOutput_part_iii_ne h

/-! ## 2. The actual output data are constant -/

/-- The output source is forced. -/
theorem s1669Source_independent (o o' : Theorem311Output I) :
    o.source = o'.source :=
  o.source_eq.trans o'.source_eq.symm

/-- The output quotient is forced. -/
theorem s1669Quotient_independent (o o' : Theorem311Output I) :
    o.quotient = o'.quotient := by
  rw [o.quotient_eq, o'.quotient_eq, s1669Source_independent o o']

/-- Part (ii) is a subsingleton: its two data fields are forced by the
corresponding equalities, and all other fields are propositions. -/
theorem s1669PartII_subsingleton : Subsingleton (PartII I) := by
  constructor
  intro x y
  cases x with
  | mk v hv s d li na ar =>
    cases y with
    | mk v' hv' s' d' li' na' ar' =>
      simp only [hv, hv', d, d'] at *

/-- Part (ii) is output-independent. -/
theorem s1669PartII_independent (o o' : Theorem311Output I) :
    o.part_ii = o'.part_ii := by
  haveI := s1669PartII_subsingleton (I := I)
  exact Subsingleton.elim o.part_ii o'.part_ii

/-- The actual output-dependent profile image is constant because it only sees
the forced quotient. -/
theorem s1669ProfileImage_independent (o o' : Theorem311Output I) :
    outputProfileImage I o = outputProfileImage I o' := by
  unfold outputProfileImage
  rw [s1669Quotient_independent o o']

/-- The SHE reading map is constant in the output by definition. -/
theorem s1669SHEReadingMap_independent
    (o o' : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (actualSHEOutput I).readingMap v o = (actualSHEOutput I).readingMap v o' :=
  rfl

/-- The actual output reading point is constant in the output. -/
theorem s1669ReadingPoint_independent (o o' : Theorem311Output I) :
    outputReadingPoint I s o = outputReadingPoint I s o' :=
  outputReadingPoint_output_independent I s o o'

/-- The actual reading image is output-independent. -/
theorem s1669ReadingImage_independent (o o' : Theorem311Output I) :
    outputReadingImage I s o = outputReadingImage I s o' :=
  outputReadingImage_output_independent I s o o'

/-- The actual reading image is not output-dependent. -/
theorem s1669ReadingImage_not_output_dependent :
    ¬ ∃ o o' : Theorem311Output I,
      outputReadingImage I s o ≠ outputReadingImage I s o' := by
  rintro ⟨o, o', hne⟩
  exact hne (s1669ReadingImage_independent o o')

/-- The actual S1417 reading image is a constant family. -/
theorem s1669OutputReadingImage_constant :
    outputReadingImage I s =
      (fun _ => outputReadingImage I s (theorem311Output I)) :=
  outputReadingImage_constant I s

/-- The actual S1402 source built from the SHE unit reading image is
output-independent. -/
theorem s1669UnitSource_independent
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (o o' : Theorem311Output I) :
    (s1551UnitImageSource (I := I) det).image o =
      (s1551UnitImageSource (I := I) det).image o' :=
  s1551UnitImage_output_independent (I := I) det o o'

/-- The actual unit-reading S1402 source is not output-dependent. -/
theorem s1669UnitSource_not_output_dependent
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    ¬ ∃ o o' : Theorem311Output I,
      (s1551UnitImageSource (I := I) det).image o ≠
        (s1551UnitImageSource (I := I) det).image o' :=
  s1551UnitImage_not_output_dependent (I := I) det

/-- S1644: no S1630 output-dependent point family can have the actual
unit-reading S1402 source. -/
theorem s1669UnitSource_no_S1630
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    ¬ ∃ P : S1630OutputDependentIntegralPoint (I := I) (s := s),
      P.toSource = s1551UnitImageSource (I := I) det :=
  no_outputDependentPoint_of_unitImageSource (I := I) (s := s) det

/-! ## 3. The junk label construction shows that S1630 is fake-inhabitable -/

/-- The natural number attached to an output by the part (iii) LGP label,
shifted by two so that it is never the reading value one. -/
def s1669JunkN (o : Theorem311Output I) : Nat :=
  o.part_iii.timesMuLink.upper_label I.core.base + 2

/-- The junk output-dependent point: cast the LGP label to the completion at
every place.  It is integral and nonzero, but it is not the paper HDD image. -/
noncomputable def s1669JunkPoint : Theorem311Output I → S1513DependentPoint s :=
  fun o v => (s1669JunkN (I := I) o : Completion v.1)

/-- Natural numbers are integral in every completion. -/
theorem s1669NatCast_mem_completionIntegers
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) (n : Nat) :
    (n : Completion v.1) ∈ (CompletionIntegers v.1 : Set (Completion v.1)) := by
  induction n with
  | zero => exact zero_mem _
  | succ n ih =>
      have h : ((n + 1 : Nat) : Completion v.1) = (n : Completion v.1) + 1 := by
        push_cast
        ring
      rw [h]
      exact add_mem ih (one_mem _)

/-- Every coordinate of the junk point is integral. -/
theorem s1669JunkPoint_integral (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    s1669JunkPoint (I := I) (s := s) o v ∈
      (CompletionIntegers v.1 : Set (Completion v.1)) :=
  s1669NatCast_mem_completionIntegers (s := s) v (s1669JunkN (I := I) o)

/-- Every coordinate of the junk point is nonzero. -/
theorem s1669JunkPoint_ne_zero (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    s1669JunkPoint (I := I) (s := s) o v ≠ 0 := by
  dsimp [s1669JunkPoint]
  exact Nat.cast_ne_zero.mpr (by unfold s1669JunkN; omega)

/-- Every coordinate of the junk point is different from the reading value
one. -/
theorem s1669JunkPoint_ne_one (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    s1669JunkPoint (I := I) (s := s) o v ≠ 1 := by
  dsimp [s1669JunkPoint]
  exact Nat.cast_ne_one.mpr (by unfold s1669JunkN; omega)

/-- The junk point is not the actual unit-section reading point. -/
theorem s1669JunkPoint_ne_reading (hne : s.Nonempty) :
    s1669JunkPoint (I := I) (s := s) ≠
      (fun o => outputReadingPoint I s o) := by
  obtain ⟨v0, hv0⟩ := hne
  let v : {v : NumberField.FinitePlace ℚ // v ∈ s} := ⟨v0, hv0⟩
  intro h
  have h0 : s1669JunkPoint (I := I) (s := s) (theorem311Output I) =
      outputReadingPoint I s (theorem311Output I) :=
    congrFun h (theorem311Output I)
  have h1 := congrFun h0 v
  rw [outputReadingPoint_eq_one] at h1
  exact s1669JunkPoint_ne_one (I := I) (s := s) (theorem311Output I) v h1

/-- Pointwise version: the junk value is never the reading value one. -/
theorem s1669JunkPoint_ne_reading_apply (o : Theorem311Output I)
    (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) :
    s1669JunkPoint (I := I) (s := s) o v ≠
      outputReadingPoint I s o v := by
  rw [outputReadingPoint_eq_one]
  exact s1669JunkPoint_ne_one (I := I) (s := s) o v

/-- The junk point is not in the actual S1417 reading image, hence it is not
supplied by the actual S1402 unit-reading source. -/
theorem s1669JunkPoint_not_mem_outputReadingImage (hne : s.Nonempty)
    (o : Theorem311Output I) :
    s1669JunkPoint (I := I) (s := s) o ∉ outputReadingImage I s o := by
  obtain ⟨v0, hv0⟩ := hne
  let v : {v : NumberField.FinitePlace ℚ // v ∈ s} := ⟨v0, hv0⟩
  intro h
  have h' : s1669JunkPoint (I := I) (s := s) o = outputReadingPoint I s o := by
    simpa [outputReadingImage] using h
  exact s1669JunkPoint_ne_reading_apply (I := I) (s := s) o v (congrFun h' v)

/-- The junk point is output-dependent: the second output shifts the label by
one, and at any place the two natural numbers differ. -/
theorem s1669JunkPoint_output_dependent (hne : s.Nonempty) :
    ∃ o o' : Theorem311Output I,
      s1669JunkPoint (I := I) (s := s) o ≠
        s1669JunkPoint (I := I) (s := s) o' := by
  obtain ⟨v0, hv0⟩ := hne
  let v : {v : NumberField.FinitePlace ℚ // v ∈ s} := ⟨v0, hv0⟩
  refine ⟨theorem311Output I, s1669AltOutput (I := I), ?_⟩
  intro h
  have h0 := congrFun h v
  have hnat : s1669JunkN (I := I) (theorem311Output I) =
      s1669JunkN (I := I) (s1669AltOutput (I := I)) := by
    dsimp [s1669JunkPoint] at h0
    exact Nat.cast_injective h0
  dsimp [s1669JunkN, s1669AltOutput, s1669AltPartIII] at hnat
  omega

/-- The junk point family packs into S1630 once any det bookkeeping is
supplied.  This is the fake inhabitant; it is not the paper HDD image. -/
noncomputable def s1669JunkS1630
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (hne : s.Nonempty) :
    S1630OutputDependentIntegralPoint (I := I) (s := s) where
  point := s1669JunkPoint (I := I) (s := s)
  point_ne_zero := s1669JunkPoint_ne_zero
  integral := s1669JunkPoint_integral
  output_dependent := s1669JunkPoint_output_dependent hne
  detData := det

/-- **Red flag.** For any det bookkeeping and any nonempty place set, the S1630
output-dependent integral point family is inhabited.  The inhabitant is the
junk label construction, not the paper HDD image.  Hence S1630 by itself is
fake-inhabitable and cannot be the exact first missing statement without a
genuineness condition. -/
theorem s1669S1630_fake_inhabited_of_det
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s)))
    (hne : s.Nonempty) :
    Nonempty (S1630OutputDependentIntegralPoint (I := I) (s := s)) :=
  ⟨s1669JunkS1630 (I := I) (s := s) det hne⟩

/-! ## 4. The nondegenerate first missing object -/

/-- A nondegenerate output-dependent integral point family.  Beyond the S1630
conditions it excludes the two known degenerate fills: the constant
unit-section reading and the formal part (iii) label construction.  This is a
minimal nondegeneracy predicate, not a complete source-provenance predicate;
no inhabitant is asserted. -/
structure S1669NondegenerateOutputDependentPoint
    (I : Input Label Choice) (s : Finset (NumberField.FinitePlace ℚ)) where
  point : Theorem311Output I → S1513DependentPoint s
  point_ne_zero : ∀ (o) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    point o v ≠ 0
  integral : ∀ (o) (v : {v : NumberField.FinitePlace ℚ // v ∈ s}),
    point o v ∈ (CompletionIntegers v.1 : Set (Completion v.1))
  output_dependent : ∃ o o' : Theorem311Output I, point o ≠ point o'
  /-- Not the constant unit-section reading image. -/
  not_reading : point ≠ fun o => outputReadingPoint I s o
  /-- Not the formal part (iii) label construction. -/
  not_junk : point ≠ s1669JunkPoint (I := I) (s := s)

namespace S1669NondegenerateOutputDependentPoint

variable (P : S1669NondegenerateOutputDependentPoint I s)

/-- The nondegenerate point family supplies the S1630 structure (with the
given det bookkeeping). -/
noncomputable def toS1630
    (det : DetTensorPowerLogVolumeBookkeeping (Set (S1513DependentPoint s))) :
    S1630OutputDependentIntegralPoint (I := I) (s := s) where
  point := P.point
  point_ne_zero := P.point_ne_zero
  integral := P.integral
  output_dependent := P.output_dependent
  detData := det

/-- The junk point does not satisfy the nondegeneracy condition. -/
theorem not_junk_of_eq_junk
    (h : P.point = s1669JunkPoint (I := I) (s := s)) : False :=
  P.not_junk h

/-- The reading point does not satisfy the nondegeneracy condition because it
is output-independent. -/
theorem not_eq_reading_of_output_independent
    (h : P.point = fun o => outputReadingPoint I s o) : False :=
  P.not_reading h

end S1669NondegenerateOutputDependentPoint

/-- The exact first missing object at the current interface: a nondegenerate
output-dependent integral point family.  No inhabitant is asserted; the actual
paper q-pilot/theta output-to-section map is still not formalized. -/
abbrev S1669FirstMissing (I : Input Label Choice)
    (s : Finset (NumberField.FinitePlace ℚ)) :=
  S1669NondegenerateOutputDependentPoint I s

/-- The nondegenerate first missing object is strictly stronger than S1630:
the junk S1630 inhabitant is not nondegenerate. -/
theorem s1669Junk_not_nondegenerate (hne : s.Nonempty) :
    ¬ ∃ P : S1669NondegenerateOutputDependentPoint I s,
      P.point = s1669JunkPoint (I := I) (s := s) := by
  rintro ⟨P, hP⟩
  exact P.not_junk hP

/-- The exact first missing object has no inhabitant from the actual reading
map. -/
theorem s1669Reading_not_nondegenerate :
    ¬ ∃ P : S1669NondegenerateOutputDependentPoint I s,
      P.point = fun o => outputReadingPoint I s o := by
  rintro ⟨P, hP⟩
  exact P.not_reading hP

/-- Summary of the actual output-side obstruction. -/
theorem s1669ActualOutput_data_constant :
    (∀ o o' : Theorem311Output I, o.source = o'.source) ∧
    (∀ o o' : Theorem311Output I, o.quotient = o'.quotient) ∧
    (∀ o o' : Theorem311Output I, o.part_ii = o'.part_ii) ∧
    (∀ o o' : Theorem311Output I,
      outputProfileImage I o = outputProfileImage I o') ∧
    (∀ o o' : Theorem311Output I,
      outputReadingPoint I s o = outputReadingPoint I s o') :=
  ⟨s1669Source_independent,
   s1669Quotient_independent,
   s1669PartII_independent,
   s1669ProfileImage_independent,
   s1669ReadingPoint_independent⟩

/-! ## 5. Checks and axiom audit -/

#check s1669AltOutput
#check s1669AltOutput_ne
#check s1669Output_not_subsingleton
#check s1669AltOutput_part_iii_ne
#check s1669SHEOutputActual_output_unique
#check s1669SHEOutputActual_output_subsingleton
#check s1669AltOutput_not_SHEOutputActual
#check s1669HonestOutput_subsingleton
#check s1669HonestOutput_eq
#check s1669HonestOutput_function_constant
#check s1669Source_independent
#check s1669Quotient_independent
#check s1669PartII_independent
#check s1669ProfileImage_independent
#check s1669SHEReadingMap_independent
#check s1669OutputReadingImage_constant
#check s1669ReadingImage_not_output_dependent
#check s1669UnitSource_independent
#check s1669UnitSource_not_output_dependent
#check s1669UnitSource_no_S1630
#check s1669JunkPoint
#check s1669JunkPoint_integral
#check s1669JunkPoint_ne_zero
#check s1669JunkPoint_ne_reading
#check s1669JunkPoint_ne_reading_apply
#check s1669JunkPoint_not_mem_outputReadingImage
#check s1669JunkPoint_output_dependent
#check s1669JunkS1630
#check s1669S1630_fake_inhabited_of_det
#check S1669NondegenerateOutputDependentPoint
#check S1669FirstMissing
#check S1669NondegenerateOutputDependentPoint.toS1630
#check s1669Junk_not_nondegenerate
#check s1669Reading_not_nondegenerate
#check s1669ActualOutput_data_constant

#print axioms s1669AltOutput_ne
#print axioms s1669HonestOutput_subsingleton
#print axioms s1669SHEOutputActual_output_unique
#print axioms s1669SHEOutputActual_output_subsingleton
#print axioms s1669AltOutput_not_SHEOutputActual
#print axioms s1669HonestOutput_eq
#print axioms s1669HonestOutput_function_constant
#print axioms s1669PartII_subsingleton
#print axioms s1669JunkPoint_output_dependent
#print axioms s1669S1630_fake_inhabited_of_det
#print axioms s1669Junk_not_nondegenerate
#print axioms s1669ActualOutput_data_constant

end LeanFormal.IUT.XiFPaper.S1669HDDOutputDependenceActual

end
