import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity
import tmp.sheaf.xif.paper.ThetaPilotObjectActual

-- Signed hull log-volume directly from the actual source log-degree
--
-- NORMALIZATION CHOICE. We use the card-normalized signed point
--
--   signedPointLogVolume v x = (1 / card(SourceVolumeIndex l)) *
--     I.sourceLocalLogDegree v x.
--
-- For an actual theta-pilot point this equals log(thetaValueAt ...), because
-- sourceLocalLogDegree = card(SourceVolumeIndex l) * log(thetaValueAt ...).
-- The corresponding q-pilot scalar is therefore log(q_v), NOT
-- card * log(q_v). If one instead uses the raw degree, both the hull value and
-- the q-pilot scalar must be multiplied by card(SourceVolumeIndex l).
--
-- The hull is the actual sSup over the actual sourceHolomorphicHull of the
-- signed real point log-volume. No ENNReal.ofReal and no averaging over
-- theta labels are used. WRITE-ONLY; no local lake/lean.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.SignedHullLogFromSourceActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

-- Card-normalized signed point log-volume (real-valued, negative at theta
-- points when the theta value is < 1).
noncomputable def signedPointLogVolume
    (x : I.ThetaPilotPoint v) : Real :=
  (Fintype.card (SourceVolumeIndex l) : Real)⁻¹ *
    I.sourceLocalLogDegree v x

-- The actual signed hull log-volume: sSup over the actual holomorphic hull
-- of the card-normalized signed point log-volume.
noncomputable def signedHullLogVolume : Real :=
  sSup {y : Real | ∃ x : I.ThetaPilotPoint v,
    x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
      y = signedPointLogVolume (I := I) v x}

theorem signedHullLogVolume_eq_sSup :
    signedHullLogVolume (I := I) v R n =
      sSup {y : Real | ∃ x : I.ThetaPilotPoint v,
        x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
          y = signedPointLogVolume (I := I) v x} := rfl

-- The card normalization cancels the sourceLocalLogDegree factor at an
-- actual theta-pilot point, giving exactly log(thetaValueAt ...).
theorem signedPointLogVolume_thetaPilotPoint
    (j : SignedLabel l.value)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    signedPointLogVolume (I := I) v
        (I.sourceThetaPilotPoint v R n j) =
      Real.log (I.thetaValueAt (n.val : Int) 0 j) := by
  unfold signedPointLogVolume
  rw [I.sourceLocalLogDegree_thetaPilotPoint v R n j hdeg]
  have hcard : (Fintype.card (SourceVolumeIndex l) : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (sourceVolumeIndex_card_pos l))
  field_simp [hcard]

-- The base q parameter of the source theta packet.
noncomputable abbrev baseThetaQ : Real :=
  (I.theaterAt 0 0).thetaPacket.q

theorem baseThetaQ_pos : 0 < baseThetaQ (I := I) :=
  (I.theaterAt 0 0).thetaPacket.q_pos

-- At the signed label j = 1, the actual theta value is exactly the base q.
theorem thetaValueAt_one_eq_baseThetaQ :
    I.thetaValueAt (n.val : Int) 0 (oneSignedLabel (l := l)) =
      baseThetaQ (I := I) := by
  unfold thetaValueAt thetaValueAt
  rw [I.linkAt_scale (n.val : Int) 0 0 0 (oneSignedLabel (l := l))]
  change (I.theaterAt 0 0).thetaPacket.scale
      (oneSignedLabel (l := l)) = baseThetaQ (I := I)
  rw [(I.theaterAt 0 0).thetaPacket.scale_eq
    (oneSignedLabel (l := l)), oneSignedLabel_val, gaussExponent_one_toNat]
  simp [realThetaValue]

-- The set of signed log-values of the actual nonzero theta-pilot images.
noncomputable def signedThetaPossibleLogSet : Set Real :=
  {y : Real | ∃ j : SignedLabel l.value, j.1 ≠ 0 ∧
    y = Real.log (I.thetaValueAt (n.val : Int) 0 j)}

-- Every nonzero theta value is q^(j^2) with j^2 >= 1, and log(q) < 0, so its
-- log is at most log(q).
theorem signedThetaPossibleLogSet_upper
    (hlogq : Real.log (baseThetaQ (I := I)) < 0)
    {y : Real} (hy : y ∈ signedThetaPossibleLogSet (I := I) n) :
    y ≤ Real.log (baseThetaQ (I := I)) := by
  rcases hy with ⟨j, hj, rfl⟩
  rw [log_thetaValueAt_eq_gauss (I := I) n j]
  have hj2 : (1 : Int) ≤ gaussExponent j.1 := by
    unfold gaussExponent
    have hjpos : 0 < j.1 * j.1 := by
      exact mul_pos_self.mpr hj
    omega
  have htoNat : (1 : Nat) ≤ (gaussExponent j.1).toNat := by
    have hcast : (1 : Int) ≤ ((gaussExponent j.1).toNat : Int) := by
      rw [Int.toNat_of_nonneg (gaussExponent_nonneg j.1)]
      exact hj2
    exact_mod_cast hcast
  have htoNatR : (1 : Real) ≤ ((gaussExponent j.1).toNat : Real) := by
    exact_mod_cast htoNat
  calc
    ((gaussExponent j.1).toNat : Real) *
        Real.log (baseThetaQ (I := I))
        ≤ 1 * Real.log (baseThetaQ (I := I)) :=
      mul_le_mul_of_nonpos_right htoNatR (le_of_lt hlogq)
    _ = Real.log (baseThetaQ (I := I)) := one_mul _

-- The actual nonzero theta possible logs have supremum exactly log(q_v).
theorem signedThetaPossibleLogSet_sSup
    (hlogq : Real.log (baseThetaQ (I := I)) < 0) :
    sSup (signedThetaPossibleLogSet (I := I) n) =
      Real.log (baseThetaQ (I := I)) := by
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, oneSignedLabel (l := l), oneSignedLabel_ne_zero,
        by rw [thetaValueAt_one_eq_baseThetaQ]⟩
    · intro y hy
      exact signedThetaPossibleLogSet_upper (I := I) n hlogq hy
  · apply le_csSup
    · exact ⟨Real.log (baseThetaQ (I := I)),
        fun y hy => signedThetaPossibleLogSet_upper (I := I) n hlogq hy⟩
    · exact ⟨oneSignedLabel (l := l), oneSignedLabel_ne_zero,
        by rw [thetaValueAt_one_eq_baseThetaQ]⟩

-- Lower bound for the actual holomorphic-hull signed sup: the q-pilot image
-- (j = 1) lies in the actual hull, so log(q_v) is at most the hull sSup.
theorem signedHullLogVolume_ge_baseThetaQLog
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (hbound : BddAbove {y : Real | ∃ x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
        y = signedPointLogVolume (I := I) v x})
    (hlogq : Real.log (baseThetaQ (I := I)) < 0) :
    Real.log (baseThetaQ (I := I)) ≤ signedHullLogVolume (I := I) v R n := by
  apply le_csSup hbound
  refine ⟨I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l)), ?_, ?_⟩
  · exact I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n
      (oneSignedLabel (l := l))
  · rw [signedPointLogVolume_thetaPilotPoint (I := I) v R n
      (oneSignedLabel (l := l)) hdeg, thetaValueAt_one_eq_baseThetaQ]

#check signedPointLogVolume
#check signedHullLogVolume
#check signedPointLogVolume_thetaPilotPoint
#check thetaValueAt_one_eq_baseThetaQ
#check signedThetaPossibleLogSet_upper
#check signedThetaPossibleLogSet_sSup
#check signedHullLogVolume_ge_baseThetaQLog

end LeanFormal.IUT.XiFPaper.SignedHullLogFromSourceActualAdapted

end