/-
  Ind1 quotient transport for the constructed finite output.

  Frozen target: `Ind1.lean` (`IUT-III.Ind1`), whose note reads
  "Prove the first quotient compatibility from the constructed output."

  This module supplies the generic action-form absorption and the Q(i)-at-5
  instance layer of the (Ind1) reduction:

  * On any multiradial kernel the formal quotient absorbs the (Ind1) and
    (Ind2) actions (`generatedQuotientMap_ind1`, `generatedQuotientMap_ind2`),
    complementing the single-step form already proved in `Ind1Reduction.lean`.
  * On the proved Q(i)-at-5 carrier the vertical level is a complete
    invariant of the indeterminacy class (`quotientClass_eq_iff_level_eq`);
    consequently the constructed output's normalized log-volume descends to
    the quotient (`normalizedLogVolumeOnQuotient`), is the unique such
    descent (`normalizedLogVolumeOnQuotient_unique`), and is injective
    (`normalizedLogVolumeOnQuotient_injective`).
  * The consumer shape `ConstructedOutputQuotientCompatibility` freezes the
    output-side quotient compatibility and is instantiated for
    `SourceFiniteTheorem311.output l`.

  The source-side statement (an arbitrary procession of D-prime-strips with
  its actual log-volume) is not constructed here; that card is carried by
  `Ind1Reduction.lean` and the reduction report. No statement below keeps
  two distinct indeterminacy classes identified: the descended volume is
  proved injective.
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

namespace LeanFormal.IUT

open MultiradialKernel
open MultiradialKernel.Core
open ConcreteFiniteTheorem311

noncomputable section

universe u v

/-! ## Generic absorption of the Ind1/Ind2 actions by the formal quotient -/

namespace MultiradialKernel.Core

variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- The formal quotient absorbs the (Ind1) action: acting by `g` does not
change the indeterminacy class. -/
theorem generatedQuotientMap_ind1 (core : Core Label Choice) (g : Label) (a : Choice) :
    generatedQuotientMap core (core.ind1 g a) = generatedQuotientMap core a :=
  (generatedQuotientMap_eq_of_generated core (.ind1 ⟨g, rfl⟩)).symm

/-- The formal quotient absorbs the (Ind2) action. -/
theorem generatedQuotientMap_ind2 (core : Core Label Choice) (g : Label) (a : Choice) :
    generatedQuotientMap core (core.ind2 g a) = generatedQuotientMap core a :=
  (generatedQuotientMap_eq_of_generated core (.ind2 ⟨g, rfl⟩)).symm

end MultiradialKernel.Core

namespace SourceFiniteMultiradial

/-- On the Q(i)-at-5 carrier the vertical level is a complete invariant of the
indeterminacy class: two choices have the same formal quotient class if and
only if they sit at the same upper-semi level. -/
theorem quotientClass_eq_iff_level_eq (l : PrimeGeFive) {a b : ProcessionChoice l} :
    generatedQuotientMap (core l) a = generatedQuotientMap (core l) b <->
      a.upperSemiLevel = b.upperSemiLevel := by
  constructor
  · intro h
    have hlevel := generatedQuotientMap_level_eq (core l) h
    simpa using hlevel
  · intro h
    exact sameLevel_quotient_eq h

/-- The normalized log-volume of the constructed finite output, descended to
the indeterminacy quotient of the multiradial kernel. -/
def normalizedLogVolumeOnQuotient (l : PrimeGeFive) :
    GeneratedQuotient (core l) -> Real :=
  fun q => Quotient.liftOn' q (fun c : ProcessionChoice l => normalizedLogVolume l c)
    (fun _ _ h => (profile l).logVolume_respects_generated h)

/-- The descended volume has the output value on every representative. -/
theorem normalizedLogVolumeOnQuotient_mk (l : PrimeGeFive) (c : ProcessionChoice l) :
    normalizedLogVolumeOnQuotient l (Quotient.mk'' c) = normalizedLogVolume l c :=
  rfl

/-- Uniqueness: any function on the indeterminacy quotient whose values on
representatives are the output volumes equals the descended volume. -/
theorem normalizedLogVolumeOnQuotient_unique (l : PrimeGeFive)
    (f : GeneratedQuotient (core l) -> Real)
    (hmk : forall c : ProcessionChoice l,
      f (Quotient.mk'' c) = normalizedLogVolume l c) :
    f = normalizedLogVolumeOnQuotient l := by
  funext q
  refine Quotient.inductionOn q ?_
  intro c
  rw [hmk c, normalizedLogVolumeOnQuotient_mk]

/-- Injectivity: the descended volume separates indeterminacy classes, so the
class is recovered from the value. -/
theorem normalizedLogVolumeOnQuotient_injective (l : PrimeGeFive) :
    Function.Injective (normalizedLogVolumeOnQuotient l) := by
  intro q1 q2 h
  revert h
  refine Quotient.inductionOn q1 ?_
  intro a h
  revert h
  refine Quotient.inductionOn q2 ?_
  intro b h
  have hreal : (a.upperSemiLevel : Real) = (b.upperSemiLevel : Real) := by
    have hc : normalizedLogVolume l a = normalizedLogVolume l b := h
    simp only [normalizedLogVolume] at hc
    linarith
  have hlevel : a.upperSemiLevel = b.upperSemiLevel := by exact_mod_cast hreal
  exact (quotientClass_eq_iff_level_eq l).mpr hlevel

end SourceFiniteMultiradial

/-- Consumer-facing frozen shape of the (Ind1) quotient compatibility of the
constructed output: the procession log-volume descends to the indeterminacy
quotient, uniquely and injectively, the (Ind1)/(Ind2) steps are invisible on
it, and the quotient class of a choice is determined exactly by its vertical
level. -/
structure ConstructedOutputQuotientCompatibility (l : PrimeGeFive) where
  output : SourceFiniteTheorem311.Output l
  descendedVolume : GeneratedQuotient (SourceFiniteMultiradial.core l) -> Real
  descendedVolume_mk : forall c : ProcessionChoice l,
    descendedVolume (Quotient.mk'' c) = output.procession.logVolume c
  descendedVolume_unique :
    forall f : GeneratedQuotient (SourceFiniteMultiradial.core l) -> Real,
      (forall c : ProcessionChoice l,
        f (Quotient.mk'' c) = output.procession.logVolume c) ->
      f = descendedVolume
  descendedVolume_injective : Function.Injective descendedVolume
  ind1Step_invariant : forall {a b : ProcessionChoice l},
    Core.Ind1Step (SourceFiniteMultiradial.core l) a b ->
      output.procession.logVolume a = output.procession.logVolume b
  ind2Step_invariant : forall {a b : ProcessionChoice l},
    Core.Ind2Step (SourceFiniteMultiradial.core l) a b ->
      output.procession.logVolume a = output.procession.logVolume b
  class_eq_iff_level_eq : forall {a b : ProcessionChoice l},
    generatedQuotientMap (SourceFiniteMultiradial.core l) a =
        generatedQuotientMap (SourceFiniteMultiradial.core l) b <->
      a.upperSemiLevel = b.upperSemiLevel

/-- The constructed Q(i)-at-5 output supplies the frozen quotient
compatibility shape. -/
noncomputable def sourceOutputQuotientCompatibility (l : PrimeGeFive) :
    ConstructedOutputQuotientCompatibility l where
  output := SourceFiniteTheorem311.output l
  descendedVolume := SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l
  descendedVolume_mk := by
    intro c
    exact SourceFiniteMultiradial.normalizedLogVolumeOnQuotient_mk l c
  descendedVolume_unique := by
    intro f hf
    exact SourceFiniteMultiradial.normalizedLogVolumeOnQuotient_unique l f
      (fun c => hf c)
  descendedVolume_injective :=
    SourceFiniteMultiradial.normalizedLogVolumeOnQuotient_injective l
  ind1Step_invariant := by
    intro a b h
    exact (SourceFiniteMultiradial.profile l).logVolume_respects_ind1Step h
  ind2Step_invariant := by
    intro a b h
    exact (SourceFiniteMultiradial.profile l).logVolume_respects_ind2Step h
  class_eq_iff_level_eq := by
    intro a b
    exact SourceFiniteMultiradial.quotientClass_eq_iff_level_eq l

theorem constructedOutputQuotientCompatibility_nonempty (l : PrimeGeFive) :
    Nonempty (ConstructedOutputQuotientCompatibility l) :=
  ⟨sourceOutputQuotientCompatibility l⟩

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Status record for the (Ind1) quotient transport of the constructed output. -/
def ind1QuotientTransport : Obligation :=
  { id := "IUT-III.Ind1.quotient-transport"
    source := "IUT III, Theorem 3.11, (Ind1); Corollary 3.12 proof, Step (x) formal quotient"
    status := VerificationStatus.provedKernel
    note :=
      "The formal quotient of the multiradial kernel absorbs the (Ind1) and " ++
        "(Ind2) actions; on the proved Q(i)-at-5 constructed output the " ++
        "normalized log-volume descends to the indeterminacy quotient, is the " ++
        "unique such descent, and is injective, so the vertical level is a " ++
        "complete invariant of the class. The arbitrary source procession of " ++
        "D-prime-strips remains pending." }

end LeanFormal.IUT.Audit
