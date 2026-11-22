import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.S342QVFamilyRootImpossibleActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

/-!
# S1929: literal completion IQ carrier vs. the S1902 root-extension carrier

Layer: **O** (original-text Theta-link / Step (xi-f), carrier comparison).

## The two carriers compared here

S1902 (`S1902ActualThetaHullActual`) constructs the actual Theta hull on the
finite product of the root extensions

  X = S1902Carrier T = (b : Bad (nativePlaceSelection T)) -> rootNormedExtension T b,

where `rootNormedExtension T b = K_b(root_b)` and `root_b^(2l) = qVFamily T b`
in the algebraic closure of the completion `K_b = rootBase T b`.

The *literal completion-valued* carrier would be the corresponding product of
the actual completions themselves:

  LiteralCompletionIQCarrier T = (b : Bad (nativePlaceSelection T)) -> rootBase T b.

This file constructs the actual canonical comparison between these two
carriers:

* `completionToRootExtension T : LiteralCompletionIQCarrier T -> S1902Carrier T`,
  the coordinatewise algebra map `K_b -> K_b(root_b)`; it is injective and
  `Q`-linear;
* `completionIQSubcarrier T`, the actual `Q`-submodule of `S1902Carrier T`
  which is the image of the literal completion carrier.

## What is proved (the exact S342 obstruction)

The S1902 theta image at the positive label `j = 1` is exactly the root family
`b |-> root_b` (the Gaussian exponent is `1^2 = 1`).  If this theta image lay
in the completion subcarrier, then each `root_b` would be an element of the
completion `K_b`; its defining equation would make it a completion `2l`-th
root of the actual `qVFamily` q.  That is impossible by S342
(`twoLthRootData_impossible`).  Consequently:

* `thetaImage_not_mem_completionRange`;
* `completionToRootExtension_not_surjective`;
* `thetaImageSet_not_subset_completionIQSubcarrier`;
* `completionIQSubcarrier_ne_top`;
* the S1902 `IQHullLogVolumeInterface.imageSet` is not contained in the
  completion subcarrier.

Thus the literal completion carrier is a *proper* subcarrier of the actual
S1902 carrier, and the actual Theta image escapes it.

## The realization surface and the first missing datum

`LiteralIQCarrierRealization` records exactly what a completion-valued
realization plus an identification with S1902 would have to supply: an
`IQHullLogVolumeInterface` on the literal completion carrier, a completion
theta image satisfying the paper root equation at `j = 1`, and a map to the
S1902 carrier equal to the canonical embedding and carrying the theta image
to the S1902 theta image.  The file proves this surface has no inhabitant
(two independent ways: the root equation and the theta-image compatibility).

The exact first missing datum is isolated as

  LiteralCompletionRootMissing T =
    for every bad place b, a nonzero completion element r_b with
    r_b ^ (2l) = qVFamily T b.

This is the S342-type gap: it is not missing analysis, it is the impossible
ordinary-completion root of the actual `qVFamily` q.  The equivalence
`completionRootDatum_iff_twoLthRootData` shows that this datum is exactly
S342's ordinary-completion `TwoLthRootData`.  The paper's completion object
would have to use the paper K-side q_v (recorded separately in
`S424QVFamilyPaperQAuditActual.PaperKvQRootData`), not the repo qVFamily.

## Boundary

No completion root, no completion theta value, no identification map, and no
`Nonempty` of the realization surface is asserted.  No `sorry`, axiom, `True`,
`PUnit`, or arbitrary carrier is used.  The file does not claim that the paper
Theta object is impossible: it proves that the literal *ordinary-completion*
realization of the actual repo `qVFamily` is impossible, and that the actual
S1902 root-extension carrier is strictly larger than its completion image.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S342QVFamilyRootImpossibleActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-! ## 1. The actual bad-place index and the positive root label -/

/-- The actual bad-place set of the native source selection is nonempty.  This
is the source field `V_mod_bad_nonempty` transported to `Bad`. -/
theorem bad_nonempty : Nonempty (Bad (N8Closure.nativePlaceSelection T)) := by
  obtain ⟨p, hp⟩ := (N8Closure.nativePlaceSelection T).V_mod_bad_nonempty
  exact ⟨⟨p, hp⟩⟩

/-- The actual signed label `1`, the positive theta label whose Gaussian
exponent is `1`. -/
def oneSignedLabel (l : PrimeGeFive) : SignedLabel l.value where
  val := 1
  property := by
    have hls : (1 : Int) ≤ (lStar l.value : Int) := by
      have h5 : 5 ≤ l.value := l.ge_five
      have hlsn : 1 ≤ lStar l.value := by
        unfold lStar
        omega
      exact_mod_cast hlsn
    exact ⟨by omega, hls⟩

/-- The positive paper theta label `j = 1`, whose theta value is the root
itself (`gaussExponent 1 = 1`). -/
def oneThetaLabel (l : PrimeGeFive) : @ThetaLabel l :=
  ⟨oneSignedLabel l, by
    norm_num [oneSignedLabel]⟩

/-- The S1902 theta image at label `1` is the actual root family. -/
theorem rootExtensionProductThetaImage_oneThetaLabel :
    rootExtensionProductThetaImage T (oneThetaLabel l) =
      (fun b : Bad (N8Closure.nativePlaceSelection T) =>
        (⟨rootNormedElement T b, rootNormedElement_mem T b⟩ :
          rootNormedExtension T b)) := by
  funext b
  apply Subtype.ext
  change (rootNormedElement T b) ^ (gaussExponent (oneSignedLabel l).1) =
    rootNormedElement T b
  have h1 : (oneSignedLabel l).1 = (1 : Int) := rfl
  rw [h1]
  norm_num [gaussExponent]

/-! ## 2. The literal completion carrier and its actual embedding in S1902 -/

/-- The literal completion-valued carrier: the product of the actual
completions `K_b` at the bad places. -/
abbrev LiteralCompletionIQCarrier : Type :=
  (b : Bad (N8Closure.nativePlaceSelection T)) → rootBase T b

/-- The actual canonical map from the completion product into the S1902
root-extension product, coordinatewise `K_b -> K_b(root_b)`. -/
noncomputable def completionToRootExtension :
    LiteralCompletionIQCarrier T → S1902Carrier T :=
  fun x b => algebraMap (rootBase T b) (rootNormedExtension T b) (x b)

/-- The canonical comparison is injective: every completion factor embeds in
its root extension. -/
theorem completionToRootExtension_injective :
    Function.Injective (completionToRootExtension T) := by
  intro x y h
  funext b
  exact (algebraMap (rootBase T b) (rootNormedExtension T b)).injective
    (congrFun h b)

/-- The canonical comparison as an actual `Q`-linear map. -/
noncomputable def completionToRootExtensionLinear :
    LiteralCompletionIQCarrier T →ₗ[ℚ] S1902Carrier T where
  toFun := completionToRootExtension T
  map_add' := by
    intro x y
    funext b
    simp [completionToRootExtension, map_add]
  map_smul' := by
    intro c x
    funext b
    show algebraMap (rootBase T b) (rootNormedExtension T b) (c • x b) =
      c • algebraMap (rootBase T b) (rootNormedExtension T b) (x b)
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1

/-- The actual `Q`-submodule of the S1902 carrier which is the image of the
literal completion carrier. -/
def completionIQSubcarrier : Submodule ℚ (S1902Carrier T) :=
  LinearMap.range (completionToRootExtensionLinear T)

/-- Membership in the completion subcarrier is exactly membership in the range
of the canonical comparison. -/
theorem mem_completionIQSubcarrier_iff (x : S1902Carrier T) :
    x ∈ completionIQSubcarrier T ↔ x ∈ Set.range (completionToRootExtension T) :=
  Iff.rfl

/-! ## 3. The completion-root obstruction (S342) -/

/-- A completion `2l`-th root of the actual `qVFamily` q at one bad place,
spelled with the normalized completion field `rootBase`. -/
def completionRootDatum (b : Bad (N8Closure.nativePlaceSelection T)) : Prop :=
  ∃ r : rootBase T b,
    r ≠ 0 ∧ r ^ (2 * l.value) = (sourceRootQUnit T b : rootBase T b)

/-- A completion root datum gives S342's `TwoLthRootData` at the same bad
place. -/
theorem twoLthRootData_of_completionRootDatum
    {b : Bad (N8Closure.nativePlaceSelection T)}
    (h : completionRootDatum (T := T) b) :
    Nonempty (TwoLthRootData T b) := by
  rcases h with ⟨r, hrne, hrpow⟩
  let u : (sourceRootField T b)ˣ := Units.mk0 r hrne
  have hu : (u : sourceRootField T b) = r := rfl
  refine ⟨{ root := u, root_pow := ?_ }⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  show ((u : sourceRootField T b) : Completion ((nativeBadLift T).lift b)) ^
      (2 * l.value) =
    (qVUnit T b : Completion ((nativeBadLift T).lift b))
  rw [hu]
  exact hrpow

/-- Conversely, S342's `TwoLthRootData` gives a completion root datum in the
normalized completion spelling. -/
theorem completionRootDatum_of_twoLthRootData
    {b : Bad (N8Closure.nativePlaceSelection T)}
    (D : TwoLthRootData T b) :
    completionRootDatum (T := T) b := by
  refine ⟨(D.root : Completion ((nativeBadLift T).lift b)), ?_, ?_⟩
  · exact Units.ne_zero D.root
  · change ((D.root : Completion ((nativeBadLift T).lift b)) : rootBase T b) ^
        (2 * l.value) = (sourceRootQUnit T b : rootBase T b)
    have h := congrArg
      (fun u : (Completion ((nativeBadLift T).lift b))ˣ =>
        (u : Completion ((nativeBadLift T).lift b))) D.root_pow
    simpa [twoLExponent, sourceRootQUnit, qVUnit_apply] using h

/-- The completion root datum is exactly S342's ordinary-completion root data. -/
theorem completionRootDatum_iff_twoLthRootData
    (b : Bad (N8Closure.nativePlaceSelection T)) :
    completionRootDatum (T := T) b ↔ Nonempty (TwoLthRootData T b) :=
  ⟨fun h => twoLthRootData_of_completionRootDatum (T := T) h,
   fun h => h.elim fun D => completionRootDatum_of_twoLthRootData (T := T) D⟩

/-- S342: the actual `qVFamily` has no ordinary-completion `2l`-th root. -/
theorem completionRootDatum_impossible
    (b : Bad (N8Closure.nativePlaceSelection T)) :
    ¬ completionRootDatum (T := T) b :=
  fun h => twoLthRootData_impossible (l := l) T b
    ((completionRootDatum_iff_twoLthRootData (T := T) b).mp h)

/-- The root equation inside the root extension `L_b`, used to transfer a
completion equation from `K_b` to `L_b`. -/
theorem rootNormedElement_L_pow
    (b : Bad (N8Closure.nativePlaceSelection T)) :
    (⟨rootNormedElement T b, rootNormedElement_mem T b⟩ : rootNormedExtension T b) ^
        (2 * l.value) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        (sourceRootQUnit T b : rootBase T b) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, IntermediateField.coe_algebraMap_apply,
    rootNormedElement_pow]
  rfl

/-- If the actual S1902 theta image at label `1` were in the completion image,
then a completion root would exist at every bad place. -/
theorem completionRootDatum_of_mem_range
    (hmem : rootExtensionProductThetaImage T (oneThetaLabel l) ∈
      Set.range (completionToRootExtension T))
    (b : Bad (N8Closure.nativePlaceSelection T)) :
    completionRootDatum (T := T) b := by
  rcases hmem with ⟨x, hx⟩
  have hb : algebraMap (rootBase T b) (rootNormedExtension T b) (x b) =
      (⟨rootNormedElement T b, rootNormedElement_mem T b⟩ :
        rootNormedExtension T b) := by
    have h := congrFun hx b
    rw [rootExtensionProductThetaImage_oneThetaLabel] at h
    simpa [completionToRootExtension] using h
  have hpowL : algebraMap (rootBase T b) (rootNormedExtension T b)
      ((x b) ^ (2 * l.value)) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        (sourceRootQUnit T b : rootBase T b) := by
    rw [map_pow, hb]
    exact rootNormedElement_L_pow (T := T) b
  have hpow : (x b) ^ (2 * l.value) = (sourceRootQUnit T b : rootBase T b) :=
    (algebraMap (rootBase T b) (rootNormedExtension T b)).injective hpowL
  refine ⟨x b, ?_, hpow⟩
  intro hzero
  rw [hzero, zero_pow (Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)] at hpow
  exact Units.ne_zero (sourceRootQUnit T b) hpow.symm

/-- The S1902 theta image at the root label is not in the literal completion
carrier image. -/
theorem thetaImage_not_mem_completionRange :
    rootExtensionProductThetaImage T (oneThetaLabel l) ∉
      Set.range (completionToRootExtension T) := by
  intro hmem
  obtain ⟨b⟩ := bad_nonempty (T := T)
  exact completionRootDatum_impossible (T := T) b
    (completionRootDatum_of_mem_range (T := T) hmem b)

/-- Consequently the canonical comparison is not surjective: the root direction
is genuinely outside the completion image. -/
theorem completionToRootExtension_not_surjective :
    ¬ Function.Surjective (completionToRootExtension T) := by
  intro hsurj
  exact thetaImage_not_mem_completionRange (T := T)
    (hsurj (rootExtensionProductThetaImage T (oneThetaLabel l)))

/-! ## 4. The S1902 image set and IQ interface do not sit on the completion
subcarrier -/

/-- The whole actual S1902 theta image set is not contained in the literal
completion subcarrier. -/
theorem thetaImageSet_not_subset_completionIQSubcarrier :
    ¬ s1902ImageSet T ⊆ (completionIQSubcarrier T : Set (S1902Carrier T)) := by
  intro h
  have hmem : rootExtensionProductThetaImage T (oneThetaLabel l) ∈
      (completionIQSubcarrier T : Set (S1902Carrier T)) :=
    h ⟨oneThetaLabel l, rfl⟩
  exact thetaImage_not_mem_completionRange (T := T) hmem

/-- The literal completion subcarrier is proper: it is not the whole S1902
carrier. -/
theorem completionIQSubcarrier_ne_top :
    completionIQSubcarrier T ≠ ⊤ := by
  intro htop
  apply thetaImageSet_not_subset_completionIQSubcarrier (T := T)
  intro x _
  rw [htop]
  exact Submodule.mem_top

/-- The actual `IQHullLogVolumeInterface` of S1902 has image set
`s1902ImageSet`, which is not contained in the completion subcarrier. -/
theorem s1902IQHullLogVolumeInterface_imageSet_not_subset_completionIQSubcarrier
    [Fintype (Bad (N8Closure.nativePlaceSelection T))] :
    ¬ (s1902IQHullLogVolumeInterface T).imageSet ⊆
      (completionIQSubcarrier T : Set (S1902Carrier T)) := by
  simpa [s1902IQHullLogVolumeInterface, s1902ImageSet] using
    thetaImageSet_not_subset_completionIQSubcarrier (T := T)

/-! ## 5. The literal IQ-carrier realization surface and the first missing
datum -/

/-- The surface a literal completion-valued IQ realization plus an
identification with S1902 would have to inhabit.  It records:

* an `IQHullLogVolumeInterface` on the literal completion carrier, whose image
  set is the completion theta image;
* a completion theta image satisfying the paper root equation at `j = 1`;
* the identification map to the S1902 carrier, equal to the canonical
  completion embedding and carrying the theta image to the S1902 theta image.

The theorem `literalIQCarrierRealization_impossible` proves this surface has no
inhabitant. -/
structure LiteralIQCarrierRealization where
  /-- The IQ hull/log-volume interface on the literal completion carrier. -/
  iq : IQHullLogVolumeInterface (LiteralCompletionIQCarrier T)
  /-- The completion-valued theta image. -/
  thetaImage : @ThetaLabel l → LiteralCompletionIQCarrier T
  /-- The interface's image set is the completion theta image. -/
  iq_imageSet : iq.imageSet = Set.range thetaImage
  /-- The completion theta value at the root label satisfies the paper root
  equation. -/
  thetaImage_root_pow : ∀ b : Bad (N8Closure.nativePlaceSelection T),
    (thetaImage (oneThetaLabel l) b) ^ (2 * l.value) = (qVFamily T b).q
  /-- The identification map into the S1902 carrier. -/
  toRootExtension : LiteralCompletionIQCarrier T → S1902Carrier T
  /-- It is exactly the canonical completion embedding. -/
  toRootExtension_eq : toRootExtension = completionToRootExtension T
  /-- It carries the completion theta image to the actual S1902 theta image. -/
  thetaImage_compat : toRootExtension (thetaImage (oneThetaLabel l)) =
    rootExtensionProductThetaImage T (oneThetaLabel l)

/-- Every realization of the surface yields a completion root at each bad
place. -/
theorem literalIQCarrierRealization_completionRootDatum
    (R : LiteralIQCarrierRealization T)
    (b : Bad (N8Closure.nativePlaceSelection T)) :
    completionRootDatum (T := T) b := by
  refine ⟨R.thetaImage (oneThetaLabel l) b, ?_, ?_⟩
  · intro hzero
    have hpow0 : (0 : rootBase T b) ^ (2 * l.value) = (qVFamily T b).q := by
      simpa [hzero] using R.thetaImage_root_pow b
    rw [zero_pow (Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)] at hpow0
    exact (qVFamily T b).q_ne_zero hpow0.symm
  · show (R.thetaImage (oneThetaLabel l) b) ^ (2 * l.value) =
      (sourceRootQUnit T b : rootBase T b)
    simpa [sourceRootQUnit] using R.thetaImage_root_pow b

/-- The literal completion IQ-carrier realization is impossible: its root
equation is the S342-impossible completion `2l`-th root. -/
theorem literalIQCarrierRealization_impossible :
    ¬ Nonempty (LiteralIQCarrierRealization T) := by
  rintro ⟨R⟩
  obtain ⟨b⟩ := bad_nonempty (T := T)
  exact completionRootDatum_impossible (T := T) b
    (literalIQCarrierRealization_completionRootDatum (T := T) R b)

/-- Independent proof of the same no-go from the theta-image compatibility
field and the canonical-embedding calculation. -/
theorem literalIQCarrierRealization_impossible_via_compat :
    ¬ Nonempty (LiteralIQCarrierRealization T) := by
  rintro ⟨R⟩
  apply thetaImage_not_mem_completionRange (T := T)
  refine ⟨R.thetaImage (oneThetaLabel l), ?_⟩
  rw [← R.toRootExtension_eq]
  exact R.thetaImage_compat

/-- The exact first missing datum: a completion `2l`-th root of the actual
`qVFamily` q at every bad place.  This is the S342-impossible ordinary
completion root, not a missing analytic or Kummer estimate. -/
def LiteralCompletionRootMissing : Prop :=
  ∀ b : Bad (N8Closure.nativePlaceSelection T), completionRootDatum (T := T) b

/-- The first missing datum is impossible for the actual repo `qVFamily`. -/
theorem literalCompletionRootMissing_impossible :
    ¬ LiteralCompletionRootMissing (T := T) := by
  intro h
  obtain ⟨b⟩ := bad_nonempty (T := T)
  exact completionRootDatum_impossible (T := T) b (h b)

/-- Every literal completion realization would supply the first missing
datum.  Combined with `literalCompletionRootMissing_impossible`, this is the
exact obstruction. -/
theorem literalIQCarrierRealization_implies_rootMissing
    (h : Nonempty (LiteralIQCarrierRealization T)) :
    LiteralCompletionRootMissing (T := T) := by
  rcases h with ⟨R⟩
  intro b
  exact literalIQCarrierRealization_completionRootDatum (T := T) R b

/-! ## 6. Axiom probes -/

#print axioms completionRootDatum_iff_twoLthRootData
#print axioms completionRootDatum_impossible
#print axioms thetaImage_not_mem_completionRange
#print axioms completionIQSubcarrier_ne_top
#print axioms literalIQCarrierRealization_impossible
#print axioms literalCompletionRootMissing_impossible

end LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual

end
