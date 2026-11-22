import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2CardReduction

/-!
# ShehddK1K2BoundaryConsumerActual — K1/K2 ray-presentation boundary consumer

STEP 0 prior-art (reuse only; A475 search hit SourceK1K2* tree family):
* Theorem311/SourceK1K2CardReduction.lean (namespace K1K2Realization):
  upUnbounded_univ, raySeparation_univ, logShellRayPresentation_univ_iff,
  negLogVolume_hind3, hclass_negLogVolume_iff, hclass_translation_of_shift,
  k1BoundaryOf_univRayPresentation, k1BoundaryOf_negLogVolumeRayPresentation,
  sourceVerticalRealizationOf_negLogVolumeRayPresentation,
  not_logShellRayPresentation_of_two_singletonImages.

This file packages the proved K1-boundary assembly for the `h = -logVolume` ray
presentation as a consumer: the ray presentation characterization at L = univ, the
(Ind3) monotonicity of -logVolume, and the K1 vertical boundary + source vertical
realization.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddK1K2BoundaryConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.K1K2Realization
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.Theorem311Source.SourceDependencyChain

universe u v

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type v}
variable [AddGroup Label] [Preorder Choice]

/-- **PROVED consumer:** the log-shell ray presentation at `L = univ` is exactly the
possible-image ray form. -/
theorem raypresentation_univ_consumer
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (h : Choice → ℝ) :
    LogShellRayPresentation Q (Set.univ : Set ℝ) h ↔
      ∀ c, Q.possibleImage c = Set.Ici (h c) :=
  logShellRayPresentation_univ_iff P Q h

/-- **PROVED consumer:** `-logVolume` is monotone under the (Ind3) iterate. -/
theorem negLogVolume_hind3_consumer
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (m : Nat) (c : Choice) :
    -(Q.logVolume (P.ind3 m c)) ≤ -(Q.logVolume c) :=
  negLogVolume_hind3 P Q m c

/-- **PROVED consumer:** an unbounded ray presentation with hclass translation yields
BOTH the K1 vertical boundary and the source vertical realization. -/
theorem k1_boundary_of_negLogVolume_ray
    (P : SourceLGPProcession l Label Choice) (Q : SourcePacketRealization P)
    (hray : ∀ c, Q.possibleImage c = Set.Ici (-(Q.logVolume c)))
    (htrans : ∀ (m : Nat) (c c' : Choice), Q.logVolume c = Q.logVolume c' →
      Q.logVolume (P.ind3 m c) = Q.logVolume (P.ind3 m c')) :
    K1VerticalBoundary P Q ∧ SourceVerticalRealization P Q :=
  ⟨k1BoundaryOf_negLogVolumeRayPresentation P Q hray htrans,
    sourceVerticalRealizationOf_negLogVolumeRayPresentation P Q hray htrans⟩

/-- Row record: reused K1/K2 laws vs the consumer interface. -/
def k1k2BoundaryRows : List (String × String × String) :=
  [ ("h = -logVolume ray presentation (hray)", "REUSED DEF", "k1BoundaryOf_negLogVolumeRayPresentation")
  , ("(Ind3) -logVolume monotonicity", "REUSED PROVED", "negLogVolume_hind3")
  , ("hclass translation from volume shift", "REUSED PROVED", "hclass_translation_of_shift / hclass_negLogVolume_iff")
  , ("L = univ ray-presentation characterization", "REUSED PROVED", "logShellRayPresentation_univ_iff (consumer restatement)")
  , ("K1 vertical boundary + source vertical realization", "COMPOSED PROVED", "k1_boundary_of_negLogVolume_ray")
  , ("excluding two-singleton-image presentations", "REUSED PROVED", "not_logShellRayPresentation_of_two_singletonImages") ]

theorem k1k2BoundaryRows_length : k1k2BoundaryRows.length = 6 := rfl

#check raypresentation_univ_consumer
#check negLogVolume_hind3_consumer
#check k1_boundary_of_negLogVolume_ray
#check k1k2BoundaryRows_length

end LeanFormal.IUT.XiFPaper.ShehddK1K2BoundaryConsumerActual
end
