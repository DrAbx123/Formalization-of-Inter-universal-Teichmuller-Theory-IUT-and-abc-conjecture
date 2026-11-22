import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity
import tmp.sheaf.xif.paper.ThetaPilotObjectActual

-- Raw signed hull supremum from the actual source log-degree
--
-- This file uses the RAW card-multiplied signed point value
--
--   signedPointLogVolume v x = I.sourceLocalLogDegree v x
--
-- and the sSup over the actual sourceHolomorphicHull. It is real-valued and
-- never goes through ENNReal.ofReal. The theta-pilot point value is exactly
--
--   card(SourceVolumeIndex l) * log(thetaValueAt ...),
--
-- and at j = 1 this is card * log(q_v). The q-pilot scalar on the SAME raw
-- normalization is card * log(q_v), not log(q_v); do not mix the raw and
-- card-normalized versions. No paperLabelHull singleton Haar object is used.
--
-- WRITE-ONLY; no local lake/lean.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.SignedHullSupActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)

-- Raw signed point log-volume (negative at theta points when theta < 1).
noncomputable def signedPointLogVolume
    (x : I.ThetaPilotPoint v) : Real :=
  I.sourceLocalLogDegree v x

-- The actual signed point-log set of the actual holomorphic hull.
noncomputable def signedHullPointLogSet : Set Real :=
  {y : Real | ∃ x : I.ThetaPilotPoint v,
    x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
      y = signedPointLogVolume (I := I) v x}

-- The raw signed hull log-volume: sSup over the actual holomorphic hull.
noncomputable def signedHullLogVolume : Real :=
  sSup (signedHullPointLogSet (I := I) v R n)

theorem signedHullLogVolume_eq :
    signedHullLogVolume (I := I) v R n =
      sSup (signedHullPointLogSet (I := I) v R n) := rfl

-- The exact card-multiplied theta-pilot point formula.
theorem signedThetaPointLogVolume_eq
    (j : SignedLabel l.value)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    signedPointLogVolume (I := I) v
        (I.sourceThetaPilotPoint v R n j) =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j) := by
  unfold signedPointLogVolume
  exact I.sourceLocalLogDegree_thetaPilotPoint v R n j hdeg

-- The base q parameter of the source theta packet.
noncomputable abbrev baseThetaQ : Real :=
  (I.theaterAt 0 0).thetaPacket.q

theorem baseThetaQ_pos : 0 < baseThetaQ (I := I) :=
  (I.theaterAt 0 0).thetaPacket.q_pos

-- At j = 1 the actual theta value is the base q.
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

-- At j = 1 the signed theta point value is exactly card * log(q_v).
theorem signedThetaPointLogVolume_one_eq
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    signedPointLogVolume (I := I) v
        (I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l))) =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (baseThetaQ (I := I)) := by
  rw [signedThetaPointLogVolume_eq (I := I) v R n
    (oneSignedLabel (l := l)) hdeg, thetaValueAt_one_eq_baseThetaQ]

-- Nonzero theta-pilot images: their raw signed log is at most the j = 1 value
-- (all other j^2 are >= 1 and log(q_v) < 0).
theorem signedThetaPointLogVolume_le_one
    (j : SignedLabel l.value) (hj : j.1 ≠ 0)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (hlogq : Real.log (baseThetaQ (I := I)) < 0) :
    signedPointLogVolume (I := I) v
        (I.sourceThetaPilotPoint v R n j) ≤
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (baseThetaQ (I := I)) := by
  rw [signedThetaPointLogVolume_eq (I := I) v R n j hdeg]
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
  have hcard : (0 : Real) ≤ (Fintype.card (SourceVolumeIndex l) : Real) := by
    exact_mod_cast (Nat.zero_le _)
  have hEL :
      ((gaussExponent j.1).toNat : Real) * Real.log (baseThetaQ (I := I)) ≤
        1 * Real.log (baseThetaQ (I := I)) :=
    mul_le_mul_of_nonpos_right htoNatR (le_of_lt hlogq)
  calc
    (Fintype.card (SourceVolumeIndex l) : Real) *
        (((gaussExponent j.1).toNat : Real) * Real.log (baseThetaQ (I := I)))
        ≤ (Fintype.card (SourceVolumeIndex l) : Real) *
          (1 * Real.log (baseThetaQ (I := I))) :=
      mul_le_mul_of_nonneg_left hEL hcard
    _ = (Fintype.card (SourceVolumeIndex l) : Real) *
          Real.log (baseThetaQ (I := I)) := by ring

-- The actual signed hull log-volume is at least the j = 1 value, because the
-- actual theta-pilot point lies in the actual holomorphic hull.
theorem signedHullLogVolume_ge_one
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (hbound : BddAbove (signedHullPointLogSet (I := I) v R n)) :
    (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (baseThetaQ (I := I)) ≤ signedHullLogVolume (I := I) v R n := by
  rw [signedHullLogVolume_eq]
  apply le_csSup hbound
  refine ⟨I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l)), ?_, ?_⟩
  · exact I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n
      (oneSignedLabel (l := l))
  · exact signedThetaPointLogVolume_one_eq (I := I) v R n hdeg

-- The identity point 1 lies in the actual holomorphic hull, with signed value
-- 0. Therefore the full-hull sSup is at least 0; since card * log(q_v) < 0, the
-- full-hull sSup cannot be card * log(q_v). This is an exact obstruction to
-- identifying the full sourceHolomorphicHull sSup with the paper Theta-hull
-- scalar; the nonzero theta-image set is the correct candidate for the latter.
theorem signedHullLogVolume_ge_zero
    (hbound : BddAbove (signedHullPointLogSet (I := I) v R n)) :
    0 ≤ signedHullLogVolume (I := I) v R n := by
  rw [signedHullLogVolume_eq]
  apply le_csSup hbound
  refine ⟨1, (I.sourceHolomorphicHull v R n).one_mem, ?_⟩
  exact I.sourceLocalLogDegree_one v

theorem signedHullLogVolume_ne_one_of_neg
    (hbound : BddAbove (signedHullPointLogSet (I := I) v R n))
    (hcardpos : 0 < (Fintype.card (SourceVolumeIndex l) : Real))
    (hlogq : Real.log (baseThetaQ (I := I)) < 0) :
    signedHullLogVolume (I := I) v R n ≠
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (baseThetaQ (I := I)) := by
  intro h
  have hzero := signedHullLogVolume_ge_zero (I := I) v R n hbound
  rw [h] at hzero
  have hneg :
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (baseThetaQ (I := I)) < 0 :=
    mul_neg_of_pos_of_neg hcardpos hlogq
  exact (not_le_of_gt hneg) hzero

-- Conditional actual equality: if every point of the actual hull has signed
-- value at most the j = 1 value (the exact source upper-bound statement), then
-- the full-hull sSup is exactly card * log(q_v). This is an exact input, not a
-- fabricated identity; the identity-point obstruction above shows that the
-- hypothesis is not automatic for the monoid hull.
theorem signedHullLogVolume_eq_one_of_upper
    (hbound : BddAbove (signedHullPointLogSet (I := I) v R n))
    (hupper : ∀ x : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
        signedPointLogVolume (I := I) v x ≤
          (Fintype.card (SourceVolumeIndex l) : Real) *
            Real.log (baseThetaQ (I := I)))
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    signedHullLogVolume (I := I) v R n =
      (Fintype.card (SourceVolumeIndex l) : Real) *
        Real.log (baseThetaQ (I := I)) := by
  apply le_antisymm
  · rw [signedHullLogVolume_eq]
    apply csSup_le
    · exact ⟨_, I.sourceThetaPilotPoint v R n (oneSignedLabel (l := l)),
        I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v R n
          (oneSignedLabel (l := l)),
        signedThetaPointLogVolume_one_eq (I := I) v R n hdeg⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hupper x hx
  · exact signedHullLogVolume_ge_one (I := I) v R n hdeg hbound

#check signedPointLogVolume
#check signedHullLogVolume
#check signedThetaPointLogVolume_eq
#check signedThetaPointLogVolume_one_eq
#check signedThetaPointLogVolume_le_one
#check signedHullLogVolume_ge_one
#check signedHullLogVolume_ge_zero
#check signedHullLogVolume_ne_one_of_neg
#check signedHullLogVolume_eq_one_of_upper

end LeanFormal.IUT.XiFPaper.SignedHullSupActualAdapted

end