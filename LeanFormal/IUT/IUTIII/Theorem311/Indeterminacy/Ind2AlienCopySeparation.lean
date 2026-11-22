/-
  Ind2 alien-copy separation on the constructed finite output.

  Frozen target: `Ind2.lean` (`IUT-III.Ind2`), whose note reads
  "Prove the second link compatibility without identifying alien copies."

  `Ind2Reduction.lean` proves the general second-link descent through the
  joint (Ind1)/(Ind2) indeterminacy relation on the multiradial skeleton.
  This module supplies the Q(i)-at-5 instance: the alien copy of the
  constructed output is the second-link translate `ind2Act shift` of the same
  finite carrier, its copy correspondence is the identity of the finite label
  group (the two copies share that group and are related by no other datum),
  and no field identifies the copies.

  Proved here:

  * the two compatibility laws of the datum (`linkMap_ind1`, `linkMap_ind2`),
    using the commutation of the two actions and additivity of the `ind2`
    action;
  * genuine non-identification for a nonzero shift: the link moves the base
    choice and therefore is not the identity map
    (`ind2ShiftedCopy_linkMap_base_ne`, `ind2ShiftedCopy_linkMap_ne_id`),
    with the proved generator of the label group as an explicit nonzero
    witness (`ind2ShiftedCopy_linkMap_nontrivial`);
  * the descended second link is bijective on indeterminacy classes, with the
    explicit two-sided inverse given by the `-shift` copy
    (`ind2ShiftedCopy_secondLinkDescent_injective`, `..._surjective`);
  * the descended link preserves the descended normalized log-volume of the
    constructed output (`ind2ShiftedCopy_descent_preserves_volume`), and at
    zero shift it degenerates to the diagonal case.

  The Ism-equivariance of the actual source link and the source copies remain
  pending (cards in `Ind2Reduction.lean` and the reduction report).
-/

import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind1QuotientTransport
import LeanFormal.IUT.IUTIII.Theorem311.Indeterminacy.Ind2Reduction
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

namespace LeanFormal.IUT

open MultiradialKernel
open MultiradialKernel.Core
open ConcreteFiniteTheorem311
open SourceFiniteMultiradial

noncomputable section

namespace Ind2AlienCopy

/-- The Q(i)-at-5 alien copy: the second link is the (Ind2) translation by
`shift` between the copy and its alien translate.  The label correspondence is
the identity because both copies share the finite label group; the datum
carries no identification of the two copies. -/
abbrev ind2ShiftedCopy (l : PrimeGeFive) (shift : finiteLabel l) :
    Ind2AlienLink (finiteLabel l) (finiteLabel l)
      (ProcessionChoice l) (ProcessionChoice l) where
  nativeCore := core l
  alienCore := core l
  labelCopyMap := id
  linkMap := fun c => ProcessionChoice.ind2Act shift c
  linkMap_ind1 := by
    intro g a
    change ProcessionChoice.ind2Act shift (ProcessionChoice.ind1Act g a) =
      ProcessionChoice.ind1Act g (ProcessionChoice.ind2Act shift a)
    exact (ProcessionChoice.ind1_ind2_commute g shift a).symm
  linkMap_ind2 := by
    intro g a
    change ProcessionChoice.ind2Act shift (ProcessionChoice.ind2Act g a) =
      ProcessionChoice.ind2Act g (ProcessionChoice.ind2Act shift a)
    rw [← ProcessionChoice.ind2_add shift g a, ← ProcessionChoice.ind2_add g shift a]
    exact congrArg (fun h => ProcessionChoice.ind2Act h a) (add_comm shift g)

@[simp] theorem ind2ShiftedCopy_linkMap_apply (l : PrimeGeFive)
    (shift : finiteLabel l) (c : ProcessionChoice l) :
    (ind2ShiftedCopy l shift).linkMap c = ProcessionChoice.ind2Act shift c :=
  rfl

/-- For every nonzero shift the alien link moves the base choice: the alien
copy is genuinely distinct from the native one. -/
theorem ind2ShiftedCopy_linkMap_base_ne (l : PrimeGeFive) (shift : finiteLabel l)
    (hshift : shift ≠ 0) :
    (ind2ShiftedCopy l shift).linkMap ProcessionChoice.base ≠ ProcessionChoice.base := by
  intro h
  have h' : shift = 0 := by
    simpa using congrArg ProcessionChoice.tensorLabel h
  exact hshift h'

/-- The alien link itself is not the identity map when the shift is nonzero. -/
theorem ind2ShiftedCopy_linkMap_ne_id (l : PrimeGeFive) (shift : finiteLabel l)
    (hshift : shift ≠ 0) :
    (ind2ShiftedCopy l shift).linkMap ≠ id := by
  intro h
  exact ind2ShiftedCopy_linkMap_base_ne l shift hshift
    (congrFun h ProcessionChoice.base)

/-- The alien link is injective; the `-shift` copy inverts it. -/
theorem ind2ShiftedCopy_linkMap_injective (l : PrimeGeFive) (shift : finiteLabel l) :
    Function.Injective (ind2ShiftedCopy l shift).linkMap := by
  intro a b h
  have h' := congrArg (fun c => ProcessionChoice.ind2Act (-shift) c) h
  simpa [ind2ShiftedCopy] using h'

/-- The alien link preserves the vertical level invariant. -/
theorem ind2ShiftedCopy_linkMap_level (l : PrimeGeFive) (shift : finiteLabel l)
    (c : ProcessionChoice l) :
    (core l).level ((ind2ShiftedCopy l shift).linkMap c) = (core l).level c := by
  simp

/-- An explicit nonzero shift exists (the proved generator of the finite label
group), so the alien copy is a genuine translate and not only the diagonal. -/
theorem ind2ShiftedCopy_linkMap_nontrivial (l : PrimeGeFive) :
    ∃ shift : finiteLabel l,
      (ind2ShiftedCopy l shift).linkMap ProcessionChoice.base ≠ ProcessionChoice.base :=
  ⟨ConcreteSourceEtaleThetaBridge.generator l,
    ind2ShiftedCopy_linkMap_base_ne l (ConcreteSourceEtaleThetaBridge.generator l)
      (ConcreteSourceEtaleThetaBridge.generator_ne_zero l)⟩

/-- The descended second link acts on classes by the `shift`-translate of the
representative. -/
theorem ind2ShiftedCopy_secondLinkDescent_apply (l : PrimeGeFive)
    (shift : finiteLabel l) (c : ProcessionChoice l) :
    (ind2ShiftedCopy l shift).secondLinkDescent
        (generatedQuotientMap (core l) c) =
      generatedQuotientMap (core l) (ProcessionChoice.ind2Act shift c) := by
  change (ind2ShiftedCopy l shift).secondLinkDescent (Quotient.mk'' c) =
    Quotient.mk'' (ProcessionChoice.ind2Act shift c)
  rw [(ind2ShiftedCopy l shift).secondLinkDescent_mk]

/-- The `-shift` copy inverts the `shift` descent on indeterminacy classes
(left inverse). -/
theorem ind2ShiftedCopy_secondLinkDescent_inverse_left (l : PrimeGeFive)
    (shift : finiteLabel l) :
    (ind2ShiftedCopy l (-shift)).secondLinkDescent ∘
        (ind2ShiftedCopy l shift).secondLinkDescent = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro c
  rw [Function.comp_apply, (ind2ShiftedCopy l shift).secondLinkDescent_mk,
    (ind2ShiftedCopy l (-shift)).secondLinkDescent_mk]
  simp [ind2ShiftedCopy]

/-- The remaining composite is the identity as well (right inverse). -/
theorem ind2ShiftedCopy_secondLinkDescent_inverse_right (l : PrimeGeFive)
    (shift : finiteLabel l) :
    (ind2ShiftedCopy l shift).secondLinkDescent ∘
        (ind2ShiftedCopy l (-shift)).secondLinkDescent = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro c
  rw [Function.comp_apply, (ind2ShiftedCopy l (-shift)).secondLinkDescent_mk,
    (ind2ShiftedCopy l shift).secondLinkDescent_mk]
  simp [ind2ShiftedCopy]

/-- The descended second link is injective on indeterminacy classes. -/
theorem ind2ShiftedCopy_secondLinkDescent_injective (l : PrimeGeFive)
    (shift : finiteLabel l) :
    Function.Injective (ind2ShiftedCopy l shift).secondLinkDescent := by
  intro q1 q2 h
  calc q1 = ((ind2ShiftedCopy l (-shift)).secondLinkDescent ∘
        (ind2ShiftedCopy l shift).secondLinkDescent) q1 := by
        rw [ind2ShiftedCopy_secondLinkDescent_inverse_left]
        rfl
    _ = ((ind2ShiftedCopy l (-shift)).secondLinkDescent ∘
        (ind2ShiftedCopy l shift).secondLinkDescent) q2 := by
        rw [Function.comp_apply, Function.comp_apply, h]
    _ = q2 := by
        rw [ind2ShiftedCopy_secondLinkDescent_inverse_left]
        rfl

/-- The descended second link is surjective on indeterminacy classes. -/
theorem ind2ShiftedCopy_secondLinkDescent_surjective (l : PrimeGeFive)
    (shift : finiteLabel l) :
    Function.Surjective (ind2ShiftedCopy l shift).secondLinkDescent := by
  intro q
  refine ⟨(ind2ShiftedCopy l (-shift)).secondLinkDescent q, ?_⟩
  have h := congrFun (ind2ShiftedCopy_secondLinkDescent_inverse_right l shift) q
  simpa [Function.comp_apply] using h

/-- The descended second link is bijective on indeterminacy classes: the
alien copy separates classes exactly like the native one. -/
theorem ind2ShiftedCopy_secondLinkDescent_bijective (l : PrimeGeFive)
    (shift : finiteLabel l) :
    Function.Bijective (ind2ShiftedCopy l shift).secondLinkDescent :=
  ⟨ind2ShiftedCopy_secondLinkDescent_injective l shift,
    ind2ShiftedCopy_secondLinkDescent_surjective l shift⟩

/-- The descended second link preserves the descended normalized log-volume of
the constructed output. -/
theorem ind2ShiftedCopy_descent_preserves_volume (l : PrimeGeFive)
    (shift : finiteLabel l) :
    ∀ q : GeneratedQuotient (core l),
      SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l
          ((ind2ShiftedCopy l shift).secondLinkDescent q) =
        SourceFiniteMultiradial.normalizedLogVolumeOnQuotient l q := by
  intro q
  refine Quotient.inductionOn q ?_
  intro c
  rw [(ind2ShiftedCopy l shift).secondLinkDescent_mk,
    SourceFiniteMultiradial.normalizedLogVolumeOnQuotient_mk,
    ind2ShiftedCopy_linkMap_apply]
  exact normalizedLogVolume_ind2 l shift c

/-- At zero shift the descended second link is the identity on indeterminacy
classes. -/
theorem ind2ShiftedCopy_zero_secondLinkDescent_eq_id (l : PrimeGeFive) :
    (ind2ShiftedCopy l 0).secondLinkDescent = id := by
  funext q
  refine Quotient.inductionOn q ?_
  intro c
  rw [(ind2ShiftedCopy l 0).secondLinkDescent_mk]
  simp [ind2ShiftedCopy]

/-- At zero shift the alien link coincides with the diagonal link, so the
concrete alien-copy family contains the generic diagonal as its zero member. -/
theorem ind2ShiftedCopy_zero_linkMap_eq_diagonal (l : PrimeGeFive) :
    (ind2ShiftedCopy l 0).linkMap =
      (Ind2AlienLink.diagonal (SourceFiniteMultiradial.core l)).linkMap := by
  funext c
  simp [Ind2AlienLink.diagonal]

end Ind2AlienCopy

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Status record for the Q(i)-at-5 alien-copy separation. -/
def ind2AlienCopySeparation : Obligation :=
  { id := "IUT-III.Ind2.concrete-alien-copy-separation"
    source := "IUT III, Theorem 3.11, (i) and (iii); Remark 3.11.3 (vii), (x)"
    status := VerificationStatus.provedKernel
    note :=
      "The second-link descent through the joint (Ind1)/(Ind2) indeterminacy " ++
        "relation is instantiated on the proved Q(i)-at-5 constructed output: " ++
        "the alien copy is the Ind2 translate of the finite carrier, its link " ++
        "moves the base choice for every nonzero shift (the proved generator " ++
        "provides one), the descended link is bijective on indeterminacy " ++
        "classes with an explicit two-sided inverse, and it preserves the " ++
        "descended normalized log-volume. The Ism-equivariance of the actual " ++
        "source link remains pending." }

end LeanFormal.IUT.Audit
