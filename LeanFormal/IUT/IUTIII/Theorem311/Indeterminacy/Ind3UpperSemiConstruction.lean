/-
  Ind3 upper-semi construction on the constructed finite output.

  Frozen target: `Ind3.lean` (`IUT-III.Ind3`), whose note reads
  "Construct and prove upper-semi compatibility, not just state it."

  `UpperSemi.lean` and `Ind3Reduction.lean` supply the one-sided dominance
  kernel and the log-Kummer clause contract, and `ConcreteFiniteModel.lean`
  supplies the stated correspondence `possibleImageUpperSemi` for the
  Q(i)-at-5 output.  This module constructs the stage family for the
  constructed output and proves the upper-semi law:

  * `outputImageFamily l c` is the vertical stage family, one possible image
    per stage `n`, taken from the output values after the `n`-th (Ind3) lift;
  * its upper law is proved (`outputImageFamily_upper`), together with the
    sharp criterion `outputImageFamily_le_iff` and the strict one-sidedness
    witness `outputImageFamily_not_le_of_lt` (no reverse dominance);
  * `constructedOutputUpperSemi l c` is the resulting
    `UpperSemiCorrespondence`; its images are the output's possible images at
    the lifted stages, and at the base choice it agrees with the stated
    correspondence `possibleImageUpperSemi l`;
  * a nonzero lift is visible: the constructed family equals the stated one
    at stage `n` exactly when the choice sits at level zero.

  The construction of the actual analytic log-shell/Kummer carriers of the
  paper remains open (the card recorded in `Ind3Reduction.lean` and the
  reduction report).
-/

import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind3Reduction
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

namespace LeanFormal.IUT

open ConcreteFiniteTheorem311

noncomputable section

universe u v

namespace Ind3UpperSemi

/-- The vertical stage family of the constructed output: stage `n` is the
possible image of the output after the `n`-th (Ind3) lift of the choice. -/
def outputImageFamily (l : PrimeGeFive) (c : ProcessionChoice l) :
    Nat -> PossibleImage Real :=
  fun n => ⟨possibleImage l (ProcessionChoice.ind3Lift n c)⟩

theorem outputImageFamily_carrier (l : PrimeGeFive) (c : ProcessionChoice l)
    (n : Nat) :
    (outputImageFamily l c n).carrier = possibleImage l (ProcessionChoice.ind3Lift n c) :=
  rfl

theorem outputImageFamily_mem_iff (l : PrimeGeFive) (c : ProcessionChoice l)
    (n : Nat) (z : Real) :
    z ∈ outputImageFamily l c n ↔
      z = normalizedLogVolume l (ProcessionChoice.ind3Lift n c) := by
  change z ∈ possibleImage l (ProcessionChoice.ind3Lift n c) ↔
    z = normalizedLogVolume l (ProcessionChoice.ind3Lift n c)
  simp [possibleImage]

/-- Value form of the stage family: stage `n` carries exactly the value
`thetaLogVolume l + (level + n)`. -/
theorem outputImageFamily_value (l : PrimeGeFive) (c : ProcessionChoice l)
    (n : Nat) (z : Real) :
    z ∈ outputImageFamily l c n ↔
      z = thetaLogVolume l + ((c.upperSemiLevel + n : Nat) : Real) := by
  rw [outputImageFamily_mem_iff]
  simp only [normalizedLogVolume, ProcessionChoice.ind3_upperSemiLevel]

/-- The value comparison between two stages of the lifted output. -/
theorem normalizedLogVolume_ind3_le_of_le (l : PrimeGeFive)
    (c : ProcessionChoice l) {m n : Nat} (hmn : m ≤ n) :
    normalizedLogVolume l (ProcessionChoice.ind3Lift m c) ≤
      normalizedLogVolume l (ProcessionChoice.ind3Lift n c) := by
  simp only [normalizedLogVolume, ProcessionChoice.ind3_upperSemiLevel]
  have hcast : ((c.upperSemiLevel + m : Nat) : Real) ≤
      ((c.upperSemiLevel + n : Nat) : Real) := by
    exact_mod_cast Nat.add_le_add_left hmn c.upperSemiLevel
  linarith

/-- The constructed stage family satisfies the upper-semi law. -/
theorem outputImageFamily_upper (l : PrimeGeFive) (c : ProcessionChoice l) :
    IsUpperSemi (outputImageFamily l c) := by
  intro m n hmn z hz
  rw [outputImageFamily_mem_iff] at hz
  refine ⟨normalizedLogVolume l (ProcessionChoice.ind3Lift n c),
    by rw [outputImageFamily_mem_iff], ?_⟩
  rw [hz]
  exact normalizedLogVolume_ind3_le_of_le l c hmn

/-- Sharp stage criterion: the stage-`m` image is dominated by the stage-`n`
image exactly when `m ≤ n`. -/
theorem outputImageFamily_le_iff (l : PrimeGeFive) (c : ProcessionChoice l)
    (m n : Nat) :
    outputImageFamily l c m ≤ outputImageFamily l c n ↔ m ≤ n := by
  constructor
  · intro h
    have hz : normalizedLogVolume l (ProcessionChoice.ind3Lift m c) ∈
        outputImageFamily l c m := by rw [outputImageFamily_mem_iff]
    obtain ⟨w, hw, hmw⟩ := h _ hz
    rw [outputImageFamily_mem_iff] at hw
    subst hw
    simp only [normalizedLogVolume, ProcessionChoice.ind3_upperSemiLevel] at hmw
    have hcast : ((c.upperSemiLevel + m : Nat) : Real) ≤
        ((c.upperSemiLevel + n : Nat) : Real) := by linarith
    have hnat : c.upperSemiLevel + m ≤ c.upperSemiLevel + n := by
      exact_mod_cast hcast
    exact Nat.add_le_add_iff_left.mp hnat
  · intro hmn z hz
    rw [outputImageFamily_mem_iff] at hz
    refine ⟨normalizedLogVolume l (ProcessionChoice.ind3Lift n c),
      by rw [outputImageFamily_mem_iff], ?_⟩
    rw [hz]
    exact normalizedLogVolume_ind3_le_of_le l c hmn

/-- Strict one-sidedness: a later stage never dominates an earlier one, so no
reverse (lower bound) comparison follows from the upper-semi law. -/
theorem outputImageFamily_not_le_of_lt (l : PrimeGeFive) (c : ProcessionChoice l)
    {m n : Nat} (h : n < m) :
    ¬ (outputImageFamily l c m ≤ outputImageFamily l c n) := by
  intro hle
  exact not_le_of_gt h ((outputImageFamily_le_iff l c m n).mp hle)

/-- Equality of upper-semi correspondences from equality of their images. -/
theorem upperSemiCorrespondence_eq_of_image_eq {α : Type u} {β : Type v}
    [Preorder α] [Preorder β] {C1 C2 : UpperSemiCorrespondence α β}
    (h : C1.image = C2.image) : C1 = C2 := by
  rcases C1 with ⟨i1, u1⟩
  rcases C2 with ⟨i2, u2⟩
  have h' : i1 = i2 := h
  subst h'
  rfl

/-- The upper-semi correspondence constructed from the output values. -/
def constructedOutputUpperSemi (l : PrimeGeFive) (c : ProcessionChoice l) :
    UpperSemiCorrespondence Nat Real :=
  UpperSemiCorrespondence.ofIsUpperSemi (outputImageFamily l c)
    (outputImageFamily_upper l c)

/-- The constructed correspondence is the kernel `ofIsUpperSemi` image of the
stage family. -/
theorem constructedOutputUpperSemi_eq_ofIsUpperSemi (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    constructedOutputUpperSemi l c =
      UpperSemiCorrespondence.ofIsUpperSemi (outputImageFamily l c)
        (outputImageFamily_upper l c) :=
  rfl

/-- The images of the constructed correspondence are the output's possible
images at the lifted stages. -/
theorem constructedOutputUpperSemi_image (l : PrimeGeFive) (c : ProcessionChoice l)
    (n : Nat) :
    (constructedOutputUpperSemi l c).image n =
      possibleImage l (ProcessionChoice.ind3Lift n c) := by
  simp only [constructedOutputUpperSemi,
    UpperSemiCorrespondence.ofIsUpperSemi_image]
  rfl

/-- The images of the constructed correspondence are the procession possible
images of the finite output at the lifted stages. -/
theorem constructedOutputUpperSemi_image_eq_finiteOutput (l : PrimeGeFive)
    (c : ProcessionChoice l) (n : Nat) :
    (constructedOutputUpperSemi l c).image n =
      (finiteOutput l).possibleImage (ProcessionChoice.ind3Lift n c) := by
  rw [constructedOutputUpperSemi_image]
  rfl

/-- The upper-semi law of the constructed correspondence, in the shape used by
the kernel. -/
theorem constructedOutputUpperSemi_upper (l : PrimeGeFive) (c : ProcessionChoice l)
    {m n : Nat} (hmn : m ≤ n) (z : Real)
    (hz : z ∈ (constructedOutputUpperSemi l c).image m) :
    ∃ w, w ∈ (constructedOutputUpperSemi l c).image n ∧ z ≤ w :=
  (constructedOutputUpperSemi l c).upper hmn z hz

/-- At the base choice the constructed correspondence agrees with the stated
family `possibleImageUpperSemi`. -/
theorem constructedOutputUpperSemi_base_image_eq_possibleImageUpperSemi
    (l : PrimeGeFive) (n : Nat) :
    (constructedOutputUpperSemi l ProcessionChoice.base).image n =
      (possibleImageUpperSemi l).image n := by
  rw [constructedOutputUpperSemi_image, possibleImageUpperSemi_image]
  ext z
  simp [possibleImage, normalizedLogVolume, ProcessionChoice.ind3Lift]

/-- At the base choice the constructed correspondence is the stated family. -/
theorem constructedOutputUpperSemi_base_eq (l : PrimeGeFive) :
    constructedOutputUpperSemi l ProcessionChoice.base = possibleImageUpperSemi l := by
  apply upperSemiCorrespondence_eq_of_image_eq
  funext n
  exact constructedOutputUpperSemi_base_image_eq_possibleImageUpperSemi l n

/-- Nonzero lifts are visible: at any fixed stage, the constructed image
agrees with the stated image exactly when the choice sits at level zero. -/
theorem constructedOutputUpperSemi_image_eq_possibleImageUpperSemi_iff
    (l : PrimeGeFive) (c : ProcessionChoice l) (n : Nat) :
    (constructedOutputUpperSemi l c).image n =
        (possibleImageUpperSemi l).image n ↔
      c.upperSemiLevel = 0 := by
  rw [constructedOutputUpperSemi_image, possibleImageUpperSemi_image]
  constructor
  · intro h
    have hmem : thetaLogVolume l + (n : Real) ∈
        possibleImage l (ProcessionChoice.ind3Lift n c) := by
      rw [h]
      exact Set.mem_singleton _
    rw [possibleImage, Set.mem_singleton_iff] at hmem
    have hcast : (n : Real) = ((c.upperSemiLevel + n : Nat) : Real) := by
      simp only [normalizedLogVolume, ProcessionChoice.ind3_upperSemiLevel] at hmem
      linarith
    have hnat : n = c.upperSemiLevel + n := by exact_mod_cast hcast
    omega
  · intro h
    simp [possibleImage, normalizedLogVolume, ProcessionChoice.ind3Lift, h]

end Ind3UpperSemi

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Status record for the constructed (Ind3) upper-semi family on the output. -/
def ind3UpperSemiConstruction : Obligation :=
  { id := "IUT-III.Ind3.upper-semi-construction"
    source := "IUT III, Theorem 3.11, (ii), (Ind3); Proposition 3.5, (ii), (a), (b)"
    status := VerificationStatus.provedKernel
    note :=
      "The vertical stage family of the proved Q(i)-at-5 output is " ++
        "constructed with a proved upper-semi law, a sharp criterion for the " ++
        "one-sided dominance order, and a strict one-sidedness witness. At " ++
        "the base choice the constructed correspondence agrees with the " ++
        "stated family, and at stage n its image agrees with the stated " ++
        "image if and only if the choice sits at level zero. The analytic " ++
        "log-shell and Kummer carriers of the paper remain open." }

end LeanFormal.IUT.Audit
