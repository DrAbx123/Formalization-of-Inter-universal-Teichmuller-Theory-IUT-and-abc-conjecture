/-
  Step (x) consumption wiring for the three indeterminacy kernels.

  Paper anchor: IUT III, Corollary 3.12 proof, Step (x) (Inter-universal
  Teichmuller Theory III, p. 181; raw text lines 10699-10749): the Kummer
  detachment of Theorem 3.11, (ii), (iii) relates the Frobenius-like
  structures in the domain of the Theta-times-mu LGP-link to the
  multiradial representation of Theorem 3.11, (i), (a), (b), (c), at the
  cost of the indeterminacies (Ind1), (Ind2), (Ind3), which "may be
  thought of as data that describes some sort of 'formal quotient'".  The
  procession-normalized mono-analytic log-volumes then furnish an
  associated "coarse space", are invariant with respect to (Ind1) and
  (Ind2), and "have the effect of converting the indeterminacy (Ind3)
  into an inequality [from above]".

  This module wires the three proved kernel records of this project
  (`Ind1QuotientTransport`, `Ind2AlienCopySeparation`,
  `Ind3UpperSemiConstruction`) into that Step-(x) shape for the
  constructed Q(i)-at-5 output:

  * `StepXFormalQuotient.Chain l` bundles the (Ind1) quotient
    compatibility, the (Ind2) alien-copy descent datum, and the (Ind3)
    constructed upper-semi correspondence; `constructedOutputChain`
    inhabits the bundle and `stepXFormalQuotientChain_nonempty` records
    inhabitation.
  * `coarseValue` is the descended log-volume read on a class, and
    `quotientPossibleImage_eq_singleton` identifies the coarse space
    `Profile.quotientPossibleImage` with the singleton of that value.
  * `quotientPossibleImage_ind1Act`, `quotientPossibleImage_ind2Act` and
    `quotientPossibleImage_secondLinkDescent` record the invisibility of
    the (Ind1)/(Ind2) actions and of the descended second link on the
    coarse space; `coarseValue_ind1Act`/`coarseValue_ind2Act` are the
    value-level forms.
  * `quotientPossibleImage_ind3Lift_singleton` and
    `coarseValue_le_of_mem_quotientPossibleImage_ind3Lift` (with the
    strict form for a positive lift) are the Step-(x) (Ind3) law: the
    lifted stage image is the coarse value shifted by the nonnegative
    lift, so every possible value at an (Ind3)-lifted stage dominates
    the coarse value.
  * `core_ind3_level_eq` supplies the kernel form of the equality
    requested in the Card-W CC.2 interface
    (`CarrierConnectorDatum.ind3_level_eq`): on the constructed core the
    (Ind3) lift translates the level exactly, so the core's upper-semi
    `ind3_level` field is sharp on this carrier.
  * `FrobeniusUpperSemiCompatibility` is the named supply for the
    Frobenius-stripping / value-group layer: an endomorphism of the
    procession compatible with the upper-semi level; `coarseValue_mono`
    and `outputImageFamily_dominated` are the induced coarse-value and
    stage-dominance monotonicity lemmas, and
    `ind3Lift_frobeniusCompatibility` is a canonical nonempty instance.

  What this module does NOT do: it does not discharge the source-facing
  (IPL)/(SHE)/(APT) propositions of the Step-XI contract (`ipl`, `she`,
  `apt` in `Corollary312/StepXI/Contract.lean` are free props that are
  instantiated at the call sites), and it does not construct the source
  procession, the source Ism-equivariance, or the log-shell/Kummer
  analytic carriers.  Those remain the pending cards recorded in the stub
  notes; precise interface requests are collected in
  `logs/coordination/finrank-ef-20261016.md`, Entry 17.
-/

import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind1QuotientTransport
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind2AlienCopySeparation
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind3UpperSemiConstruction
import Mathlib.Tactic

namespace LeanFormal.IUT

open MultiradialKernel
open MultiradialKernel.Core
open ConcreteFiniteTheorem311

noncomputable section

namespace StepXFormalQuotient

/-! ## 1. The (Ind2) alien-copy descent datum -/

/-- The (Ind2) alien-copy datum of the constructed output: a genuine
nonzero second-link shift, the shifted alien copy, and the descended-link
facts. -/
structure AlienCopyDescent (l : PrimeGeFive) where
  shift : finiteLabel l
  shift_ne_zero : shift ≠ 0
  link_nontrivial : (Ind2AlienCopy.ind2ShiftedCopy l shift).linkMap ≠ id
  descent_bijective : Function.Bijective
    (Ind2AlienCopy.ind2ShiftedCopy l shift).secondLinkDescent
  descent_preserves_volume :
    ∀ q : GeneratedQuotient (SourceFiniteMultiradial.core l),
      SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l
          ((Ind2AlienCopy.ind2ShiftedCopy l shift).secondLinkDescent q) =
        SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l q

/-- The proved generator of the finite label group supplies the (Ind2)
alien-copy descent datum. -/
def alienCopyDescentOfGenerator (l : PrimeGeFive) : AlienCopyDescent l :=
  { shift := ConcreteSourceEtaleThetaBridge.generator l
    shift_ne_zero := ConcreteSourceEtaleThetaBridge.generator_ne_zero l
    link_nontrivial := Ind2AlienCopy.ind2ShiftedCopy_linkMap_ne_id l
      (ConcreteSourceEtaleThetaBridge.generator l)
      (ConcreteSourceEtaleThetaBridge.generator_ne_zero l)
    descent_bijective :=
      Ind2AlienCopy.ind2ShiftedCopy_secondLinkDescent_bijective l
        (ConcreteSourceEtaleThetaBridge.generator l)
    descent_preserves_volume :=
      Ind2AlienCopy.ind2ShiftedCopy_descent_preserves_volume l
        (ConcreteSourceEtaleThetaBridge.generator l) }

/-! ## 2. The Step-(x) chain bundle -/

/-- The Step-(x) formal quotient chain of the constructed Q(i)-at-5 output
at level `l`: the (Ind1) quotient compatibility, the (Ind2) alien-copy
descent datum, and the (Ind3) constructed upper-semi correspondence in
one consumer-facing record. -/
structure Chain (l : PrimeGeFive) where
  quotientCompatibility : ConstructedOutputQuotientCompatibility l
  alienCopy : AlienCopyDescent l
  upperSemi : UpperSemiCorrespondence Nat Real
  upperSemi_base_eq : upperSemi = possibleImageUpperSemi l

/-- The constructed output supplies the whole Step-(x) chain; every field
instantiates a proved kernel record. -/
def constructedOutputChain (l : PrimeGeFive) : Chain l where
  quotientCompatibility := sourceOutputQuotientCompatibility l
  alienCopy := alienCopyDescentOfGenerator l
  upperSemi := Ind3UpperSemi.constructedOutputUpperSemi l ProcessionChoice.base
  upperSemi_base_eq := Ind3UpperSemi.constructedOutputUpperSemi_base_eq l

theorem stepXFormalQuotientChain_nonempty (l : PrimeGeFive) :
    Nonempty (Chain l) :=
  ⟨constructedOutputChain l ⟩

@[simp] theorem constructedOutputChain_quotientCompatibility
    (l : PrimeGeFive) :
    (constructedOutputChain l).quotientCompatibility =
      sourceOutputQuotientCompatibility l :=
  rfl

@[simp] theorem constructedOutputChain_alienCopy_shift
    (l : PrimeGeFive) :
    (constructedOutputChain l).alienCopy.shift =
      ConcreteSourceEtaleThetaBridge.generator l :=
  rfl

@[simp] theorem constructedOutputChain_upperSemi (l : PrimeGeFive) :
    (constructedOutputChain l).upperSemi =
      Ind3UpperSemi.constructedOutputUpperSemi l ProcessionChoice.base :=
  rfl

/-! ## 3. The coarse space of the formal quotient -/

/-- The Step-(x) coarse value: the descended normalized log-volume of the
constructed output, read on the indeterminacy class of a choice. -/
def coarseValue (l : PrimeGeFive) (c : ProcessionChoice l) : Real :=
  SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l
    (generatedQuotientMap (SourceFiniteMultiradial.core l) c)

/-- The coarse value of a class is the normalized log-volume of any
representative (the (Ind1)/(Ind2)-invariant normalization). -/
@[simp] theorem coarseValue_mk (l : PrimeGeFive) (c : ProcessionChoice l) :
    SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l
        (generatedQuotientMap (SourceFiniteMultiradial.core l) c) =
      normalizedLogVolume l c :=
  SourceFiniteMultiradial.normalizedLogVolumeOnQuotient_mk l c

@[simp] theorem coarseValue_eq_normalizedLogVolume (l : PrimeGeFive)
    (c : ProcessionChoice l) :
    coarseValue l c = normalizedLogVolume l c :=
  SourceFiniteMultiradial.normalizedLogVolumeOnQuotient_mk l c

/-- The Step-(x) coarse space: the quotient possible image of a class is
the singleton of the descended log-volume, so a class carries a definite
coarse value. -/
theorem quotientPossibleImage_eq_singleton (l : PrimeGeFive)
    (q : GeneratedQuotient (SourceFiniteMultiradial.core l)) :
    (SourceFiniteMultiradial.profile l).quotientPossibleImage q =
      {SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l q} := by
  refine Quotient.inductionOn q ?_
  intro c
  change (SourceFiniteMultiradial.profile l).quotientPossibleImage
      (generatedQuotientMap (SourceFiniteMultiradial.core l) c) =
    {SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l
      (generatedQuotientMap (SourceFiniteMultiradial.core l) c)}
  have hval : SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l
      (generatedQuotientMap (SourceFiniteMultiradial.core l) c) =
        normalizedLogVolume l c :=
    SourceFiniteMultiradial.normalizedLogVolumeOnQuotient_mk l c
  rw [Profile.quotientPossibleImage_mk,
    SourceFiniteMultiradial.profile_possibleImage, possibleImage, hval]

/-- (Ind1) is invisible at value level: the coarse value is invariant
under the procession-label action. -/
@[simp] theorem coarseValue_ind1Act (l : PrimeGeFive) (g : finiteLabel l)
    (c : ProcessionChoice l) :
    coarseValue l (ProcessionChoice.ind1Act g c) = coarseValue l c := by
  simp only [coarseValue_eq_normalizedLogVolume, normalizedLogVolume_ind1]

/-- (Ind2) is invisible at value level: the coarse value is invariant
under the tensor-label action. -/
@[simp] theorem coarseValue_ind2Act (l : PrimeGeFive) (g : finiteLabel l)
    (c : ProcessionChoice l) :
    coarseValue l (ProcessionChoice.ind2Act g c) = coarseValue l c := by
  simp only [coarseValue_eq_normalizedLogVolume, normalizedLogVolume_ind2]

/-- The coarse value grows with the (Ind3) lift (one-sidedness at value
level). -/
theorem coarseValue_ind3_le (l : PrimeGeFive) (c : ProcessionChoice l)
    (n : Nat) :
    coarseValue l c ≤ coarseValue l (ProcessionChoice.ind3Lift n c) := by
  simpa only [coarseValue_eq_normalizedLogVolume] using
    normalizedLogVolume_ind3 l n c

/-- (Ind1) is invisible on the coarse space: acting by a label does not
change the quotient possible image of a class. -/
theorem quotientPossibleImage_ind1Act (l : PrimeGeFive) (g : finiteLabel l)
    (c : ProcessionChoice l) :
    (SourceFiniteMultiradial.profile l).quotientPossibleImage
        (generatedQuotientMap (SourceFiniteMultiradial.core l)
          (ProcessionChoice.ind1Act g c)) =
      (SourceFiniteMultiradial.profile l).quotientPossibleImage
        (generatedQuotientMap (SourceFiniteMultiradial.core l) c) := by
  rw [←SourceFiniteMultiradial.core_ind1 l g c,
    generatedQuotientMap_ind1]

/-- (Ind2) is invisible on the coarse space. -/
theorem quotientPossibleImage_ind2Act (l : PrimeGeFive) (g : finiteLabel l)
    (c : ProcessionChoice l) :
    (SourceFiniteMultiradial.profile l).quotientPossibleImage
        (generatedQuotientMap (SourceFiniteMultiradial.core l)
          (ProcessionChoice.ind2Act g c)) =
      (SourceFiniteMultiradial.profile l).quotientPossibleImage
        (generatedQuotientMap (SourceFiniteMultiradial.core l) c) := by
  rw [←SourceFiniteMultiradial.core_ind2 l g c,
    generatedQuotientMap_ind2]

/-- The descended second link preserves the coarse space: the alien copy
carries the same quotient possible image (the sole possible values at the
two links are the respective coarse values, and these agree). -/
theorem quotientPossibleImage_secondLinkDescent (l : PrimeGeFive)
    (shift : finiteLabel l)
    (q : GeneratedQuotient (SourceFiniteMultiradial.core l)) :
    (SourceFiniteMultiradial.profile l).quotientPossibleImage
        ((Ind2AlienCopy.ind2ShiftedCopy l shift).secondLinkDescent q) =
      (SourceFiniteMultiradial.profile l).quotientPossibleImage q := by
  rw [quotientPossibleImage_eq_singleton l
      ((Ind2AlienCopy.ind2ShiftedCopy l shift).secondLinkDescent q),
    quotientPossibleImage_eq_singleton l q,
    Ind2AlienCopy.ind2ShiftedCopy_descent_preserves_volume l shift]

/-! ## 4. The (Ind3) law on the coarse space -/

/-- The (Ind3) stage law on the coarse space: the quotient possible image
of an (Ind3)-lifted class is the singleton of the coarse value shifted by
the nonnegative lift. -/
theorem quotientPossibleImage_ind3Lift_singleton (l : PrimeGeFive)
    (c : ProcessionChoice l) (n : Nat) :
    (SourceFiniteMultiradial.profile l).quotientPossibleImage
        (generatedQuotientMap (SourceFiniteMultiradial.core l)
          (ProcessionChoice.ind3Lift n c)) =
      {coarseValue l c + (n : Real)} := by
  have hval : SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l
      (generatedQuotientMap (SourceFiniteMultiradial.core l)
        (ProcessionChoice.ind3Lift n c)) =
      coarseValue l c + (n : Real) := by
    rw [coarseValue_mk l (ProcessionChoice.ind3Lift n c),
      coarseValue_eq_normalizedLogVolume]
    simp only [normalizedLogVolume, ProcessionChoice.ind3_upperSemiLevel,
      Nat.cast_add]
    ring
  calc (SourceFiniteMultiradial.profile l).quotientPossibleImage
        (generatedQuotientMap (SourceFiniteMultiradial.core l)
          (ProcessionChoice.ind3Lift n c))
      = {SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l
          (generatedQuotientMap (SourceFiniteMultiradial.core l)
            (ProcessionChoice.ind3Lift n c))} :=
        quotientPossibleImage_eq_singleton l _
    _ = {coarseValue l c + (n : Real)} := by
        rw [hval]

/-- Step (x), (Ind3) as a one-sided inequality: every possible value at an
(Ind3)-lifted stage dominates the coarse value. -/
theorem coarseValue_le_of_mem_quotientPossibleImage_ind3Lift
    (l : PrimeGeFive) (c : ProcessionChoice l) (n : Nat) (z : Real)
    (hz : z ∈ (SourceFiniteMultiradial.profile l).quotientPossibleImage
      (generatedQuotientMap (SourceFiniteMultiradial.core l)
        (ProcessionChoice.ind3Lift n c))) :
    coarseValue l c ≤ z := by
  rw [quotientPossibleImage_ind3Lift_singleton l c n,
    Set.mem_singleton_iff] at hz
  rw [hz]
  have hn : (0 : Real) ≤ (n : Real) := by
    exact_mod_cast Nat.zero_le n
  linarith

/-- Strict form for a positive lift: a nonzero (Ind3) lift is visible on
the coarse space. -/
theorem coarseValue_lt_of_mem_quotientPossibleImage_ind3Lift
    (l : PrimeGeFive) (c : ProcessionChoice l) {n : Nat} (hn : 0 < n)
    (z : Real)
    (hz : z ∈ (SourceFiniteMultiradial.profile l).quotientPossibleImage
      (generatedQuotientMap (SourceFiniteMultiradial.core l)
        (ProcessionChoice.ind3Lift n c))) :
    coarseValue l c < z := by
  rw [quotientPossibleImage_ind3Lift_singleton l c n,
    Set.mem_singleton_iff] at hz
  rw [hz]
  have hn' : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  linarith

/-! ## 5. Kernel form of the CC.2 level equality -/

/-- Kernel-form witness of the equality requested in the Card-W CC.2
interface (`CarrierConnectorDatum.ind3_level_eq`): on the constructed
Q(i)-at-5 core the (Ind3) lift translates the level exactly, so the
core's upper-semi `ind3_level` field is sharp on this carrier.  The
source-level carrier (units/processions of Card-W) is not built in this
module. -/
theorem core_ind3_level_eq (l : PrimeGeFive) (n : Nat)
    (c : ProcessionChoice l) :
    (SourceFiniteMultiradial.core l).level
        ((SourceFiniteMultiradial.core l).ind3 n c) =
      (SourceFiniteMultiradial.core l).level c + n := by
  simp only [SourceFiniteMultiradial.core_ind3,
    SourceFiniteMultiradial.core_level,
    ProcessionChoice.ind3_upperSemiLevel]

/-! ## 6. Frobenius action on the upper-semi discrimination -/

/-- Named interface for the Frobenius-stripping / value-group layer: an
endomorphism of the constructed procession whose action does not lower
the upper-semi level.  Every compatibility lemma below is proved from
this single field, so the interface can be inhabited wherever a
Frobenius action on the core is available. -/
structure FrobeniusUpperSemiCompatibility (l : PrimeGeFive)
    (frobenius : ProcessionChoice l → ProcessionChoice l) where
  level_monotone : ∀ c : ProcessionChoice l,
    c.upperSemiLevel ≤ (frobenius c).upperSemiLevel

namespace FrobeniusUpperSemiCompatibility

variable {l : PrimeGeFive} {frob : ProcessionChoice l → ProcessionChoice l}

/-- The interface's level law, as a named accessor: a compatible
Frobenius action does not lower the upper-semi level. -/
theorem upperSemiLevel_le (D : FrobeniusUpperSemiCompatibility l frob)
    (c : ProcessionChoice l) :
    c.upperSemiLevel ≤ (frob c).upperSemiLevel := by
  obtain ⟨hlev⟩ := D
  exact hlev c

/-- Monotonicity of the coarse value under a compatible Frobenius
action: the value-level form requested for the (Ind3)/upper-semi side. -/
theorem coarseValue_mono (D : FrobeniusUpperSemiCompatibility l frob)
    (c : ProcessionChoice l) :
    coarseValue l c ≤ coarseValue l (frob c) := by
  obtain ⟨hlev⟩ := D
  simp only [coarseValue_eq_normalizedLogVolume, normalizedLogVolume]
  have h : (c.upperSemiLevel : Real) ≤ ((frob c).upperSemiLevel : Real) := by
    exact_mod_cast hlev c
  linarith

/-- Stage-level form (monotonicity on the upper-semi discrimination):
every possible value in the stage-`m` family of `c` is dominated by a
possible value in the stage-`n` family of `frob c` whenever `m ≤ n`. -/
theorem outputImageFamily_dominated (D : FrobeniusUpperSemiCompatibility l frob)
    (c : ProcessionChoice l) {m n : Nat}
    (hmn : m ≤ n) (z : Real)
    (hz : z ∈ Ind3UpperSemi.outputImageFamily l c m) :
    ∃ w, w ∈ Ind3UpperSemi.outputImageFamily l (frob c) n
      ∧ z ≤ w := by
  obtain ⟨hlev⟩ := D
  rw [Ind3UpperSemi.outputImageFamily_mem_iff] at hz
  refine ⟨normalizedLogVolume l (ProcessionChoice.ind3Lift n (frob c)),
    by rw [Ind3UpperSemi.outputImageFamily_mem_iff], ?_⟩
  rw [hz]
  simp only [normalizedLogVolume, ProcessionChoice.ind3_upperSemiLevel,
    Nat.cast_add]
  have h : (c.upperSemiLevel : Real) ≤ ((frob c).upperSemiLevel : Real) := by
    exact_mod_cast hlev c
  have hmn' : (m : Real) ≤ (n : Real) := by exact_mod_cast hmn
  linarith

/-- Coarse-space form: every possible value on the quotient class of a
Frobenius image dominates the coarse value of the original choice (the
shape consumed on the (Ind3)/upper-semi side). -/
theorem coarseValue_le_of_mem_quotientPossibleImage_frobenius
    (D : FrobeniusUpperSemiCompatibility l frob)
    (c : ProcessionChoice l) (z : Real)
    (hz : z ∈ (SourceFiniteMultiradial.profile l).quotientPossibleImage
      (generatedQuotientMap (SourceFiniteMultiradial.core l) (frob c))) :
    coarseValue l c ≤ z := by
  obtain ⟨hlev⟩ := D
  rw [quotientPossibleImage_eq_singleton l, Set.mem_singleton_iff] at hz
  rw [hz]
  change coarseValue l c ≤ coarseValue l (frob c)
  simp only [coarseValue_eq_normalizedLogVolume, normalizedLogVolume]
  have h : (c.upperSemiLevel : Real) ≤ ((frob c).upperSemiLevel : Real) := by
    exact_mod_cast hlev c
  linarith

/-- The identity action is compatible (the degree-one case of a
Frobenius-type action). -/
theorem id : FrobeniusUpperSemiCompatibility l (fun c : ProcessionChoice l => c) :=
  ⟨fun _ => le_refl _⟩

/-- Composition of compatible actions is compatible (multiplicativity of the
Frobenius degree): the composite does not lower the level either. -/
theorem comp {frob₁ frob₂ : ProcessionChoice l → ProcessionChoice l}
    (D₁ : FrobeniusUpperSemiCompatibility l frob₁)
    (D₂ : FrobeniusUpperSemiCompatibility l frob₂) :
    FrobeniusUpperSemiCompatibility l (fun c => frob₁ (frob₂ c)) :=
  ⟨fun c => (upperSemiLevel_le D₂ c).trans
    (upperSemiLevel_le D₁ (frob₂ c))⟩

end FrobeniusUpperSemiCompatibility

/-- The (Ind3) lift is a canonical compatible Frobenius action on the
constructed core, giving the value-group layer a nonempty instance of
the interface. -/
theorem ind3Lift_frobeniusCompatibility (l : PrimeGeFive) (k : Nat) :
    FrobeniusUpperSemiCompatibility l (ProcessionChoice.ind3Lift k) :=
  ⟨fun c => by
    rw [ProcessionChoice.ind3_upperSemiLevel]
    exact Nat.le_add_right c.upperSemiLevel k⟩

end StepXFormalQuotient

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Status record for the Step-(x) consumption wiring of the three
indeterminacy kernels. -/
def stepXFormalQuotientConsumption : Obligation :=
  { id := "IUT-III.StepX.formal-quotient-consumption"
    source :=
      "IUT III, Corollary 3.12 proof, Step (x); p. 181 " ++
        "(formal quotient, coarse space, (Ind3) as inequality)"
    status := VerificationStatus.provedKernel
    note :=
      "The three proved kernel records (quotient transport of the " ++
        "constructed output, alien-copy separation, constructed " ++
        "upper-semi family) are bundled into one Step-(x) chain and " ++
        "glued to the profile coarse space: the quotient possible image " ++
        "of a class is the singleton of the descended log-volume; the " ++
        "(Ind1)/(Ind2) actions and the descended second link are " ++
        "invisible on it; the (Ind3) lifts shift the coarse value by " ++
        "the nonnegative stage, so every possible value at a lifted " ++
        "stage dominates the coarse value (strictly for a positive " ++
        "lift). The source-facing (IPL)/(SHE)/(APT) propositions, the " ++
        "source procession with its Ism action, and the log-shell/Kummer " ++
        "analytic carriers remain open; the north-wall contract slots " ++
        "are not discharged by this module. The kernel level of the " ++
        "constructed core satisfies the exact (Ind3) translation " ++
        "`level (ind3 n c) = level c + n` (`core_ind3_level_eq`), the " ++
        "kernel form of the Card-W CC.2 interface request; the " ++
        "source-level carrier of that request remains open. The named " ++
        "Frobenius/upper-semi compatibility interface " ++
        "(`FrobeniusUpperSemiCompatibility`) supplies the value-group " ++
        "(Frobenius-stripping) layer with level monotonicity, coarse-" ++
        "value monotonicity and stage dominance, with the (Ind3) lift " ++
        "as a canonical nonempty instance."
    dependsOn :=
      [ "IUT-III.Ind1.quotient-transport",
        "IUT-III.Ind2.concrete-alien-copy-separation",
        "IUT-III.Ind3.upper-semi-construction" ] }

end LeanFormal.IUT.Audit
