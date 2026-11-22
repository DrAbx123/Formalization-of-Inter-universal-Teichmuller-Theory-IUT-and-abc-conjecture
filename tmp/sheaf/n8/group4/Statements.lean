/-
  N8 · group4 · stage 2 — minimal statements from `group4-STAGE1.md` §6.1.

  Source document: tmp/sheaf/n8/group4-STAGE1.md §6.1 (S2-W, "最小" form and
  "尖锐形式").  Both declarations are reproduced from that document and are
  proof-complete here: no placeholder proofs, no fabricated objects.

  Content: the frozen kernel laws do not determine `possibleImage`.
  - `exists_profile_univ_image`: for every `Core` and every base volume there
    is an admissible `Profile` whose possible image is `Set.univ` everywhere
    and whose `logVolume` is constant equal to the base volume.
  - `concrete_profile_image_not_determined`: for the concrete Q(i)-at-5 carrier
    there is an admissible `Profile` with the *same* `logVolume` as the
    constructed `SourceFiniteMultiradial.profile l` but a different image.
-/
import LeanFormal.IUT.IUTIII.Theorem311.SourceFiniteMultiradial
import Mathlib.Tactic

namespace LeanFormal.IUT.MultiradialKernel

universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label]

/-- 冻结的 kernel 律不能确定 possibleImage：对任意 core 与任意基准体积，
存在 admissible Profile，其 possibleImage 处处是 univ、logVolume 恒等于基准值。
即 (Ind1)(Ind2) 的像等号、(Ind3) 的单向支配、非空、体积律全部满足，
而"像"可以是任意全空间。 -/
theorem exists_profile_univ_image
    (core : Core Label Choice) (baseVolume : Real) :
    ∃ Q : Profile core,
      (∀ c : Choice, Q.possibleImage c = Set.univ) ∧
        Q.logVolume = (fun _ : Choice => baseVolume) := by
  refine ⟨{ logVolume := fun _ => baseVolume
            possibleImage := fun _ => Set.univ
            ind1_invariant := fun _ _ => rfl
            ind2_invariant := fun _ _ => rfl
            ind3_upper := fun _ _ => le_rfl
            possibleImage_nonempty := fun _ => Set.univ_nonempty
            possibleImage_ind1 := fun _ _ => rfl
            possibleImage_ind2 := fun _ _ => rfl
            possibleImage_ind3 := fun _ _ _ _ =>
              ⟨_, Set.mem_univ _, le_rfl⟩ }, fun _ => rfl, rfl⟩

end LeanFormal.IUT.MultiradialKernel

namespace LeanFormal.IUT

open ConcreteFiniteTheorem311

/-- 具体 Q(i)-at-5 载体：存在与 Constructed 输出**逐点体积完全相同**、
但像处处不同（univ）的 admissible Profile。 -/
theorem concrete_profile_image_not_determined (l : PrimeGeFive) :
    ∃ Q : MultiradialKernel.Profile (SourceFiniteMultiradial.core l),
      Q.logVolume = (SourceFiniteMultiradial.profile l).logVolume ∧
        Q.possibleImage ≠ (SourceFiniteMultiradial.profile l).possibleImage := by
  refine ⟨{ (SourceFiniteMultiradial.profile l) with
            possibleImage := fun _ => Set.univ
            possibleImage_nonempty := fun _ => Set.univ_nonempty
            possibleImage_ind1 := fun _ _ => rfl
            possibleImage_ind2 := fun _ _ => rfl
            possibleImage_ind3 := fun _ _ _ _ =>
              ⟨_, Set.mem_univ _, le_rfl⟩ }, rfl, ?_⟩
  intro h
  have h0 : (0 : Real) ∈ (SourceFiniteMultiradial.profile l).possibleImage
      (ProcessionChoice.base : ProcessionChoice l) := by
    rw [← h]; exact Set.mem_univ 0
  have h1 : (1 : Real) ∈ (SourceFiniteMultiradial.profile l).possibleImage
      (ProcessionChoice.base : ProcessionChoice l) := by
    rw [← h]; exact Set.mem_univ 1
  rw [SourceFiniteMultiradial.profile_possibleImage, possibleImage,
    normalizedLogVolume] at h0 h1
  simp only [ProcessionChoice.base_upperSemiLevel, Nat.cast_zero,
    Set.mem_singleton_iff] at h0 h1
  linarith

end LeanFormal.IUT
