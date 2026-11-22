import tmp.sheaf.xif.paper.S2609SignedGapPartsActual
import tmp.sheaf.xif.paper.S2610SignedGap2ConditionalActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2605SignedSourceVolumeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2611SignedGap2SourceActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {v : V}

/-- The three genuine signed gap-2 inputs.  No field is claimed to be
inhabited; this is a conditional data interface. -/
structure SignedGap2SourceData
    (hull : Set (I.ThetaPilotPoint v))
    (scaledUnit : Nat -> Nat -> Nat -> Set (I.ThetaPilotPoint v))
    (point : Nat -> Nat -> Nat -> I.ThetaPilotPoint v)
    (eps : Real) (D0 D1 : Real) : Prop where
  /-- Signed hull finiteness: hull log-degrees are bounded below. -/
  hull_logDegree_ge :
    ∃ C : Real, ∀ x : I.ThetaPilotPoint v, x ∈ hull ->
      C <= I.sourceLocalLogDegree v x
  /-- Signed scaled-unit region is bounded by the signed hull plus `D0`. -/
  scaledUnit_le_hull :
    ∀ a b c : Nat, IsABCTriple a b c ->
      sourceSetVolumeSigned I v (scaledUnit a b c) <=
        sourceSetVolumeSigned I v hull + ENNReal.ofReal D0
  /-- Signed point log-degree is bounded by weight plus `D1`. -/
  point_logDegree_le :
    ∀ a b c : Nat, IsABCTriple a b c ->
      max 0 (-I.sourceLocalLogDegree v (point a b c)) <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1

theorem signedHullFinite_of_logDegree_ge
    {hull : Set (I.ThetaPilotPoint v)}
    (h : exists C : Real, forall x : I.ThetaPilotPoint v, x ∈ hull ->
      C <= I.sourceLocalLogDegree v x) :
    sourceSetVolumeSigned I v hull < ⊤ := by
  obtain ⟨C, hC⟩ := h
  have hle : sourceSetVolumeSigned I v hull <= ENNReal.ofReal (-C) := by
    unfold sourceSetVolumeSigned
    refine iSup_le_iff.mpr ?_
    intro x
    refine iSup_le_iff.mpr ?_
    intro hx
    exact ENNReal.ofReal_le_ofReal (by linarith [hC x hx])
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

theorem sourceSetVolumeSigned_singleton (x : I.ThetaPilotPoint v) :
    sourceSetVolumeSigned I v {x} = sourcePointVolumeSigned I v x := by
  apply le_antisymm
  · unfold sourceSetVolumeSigned
    refine iSup_le_iff.mpr ?_
    intro y
    refine iSup_le_iff.mpr ?_
    intro hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    rw [hyx]
  · unfold sourceSetVolumeSigned
    exact le_iSup_of_le x (le_iSup_of_le
      (f := fun _ : x ∈ {x} => sourcePointVolumeSigned I v x) (by simp) le_rfl)

theorem sourceSetVolumeSigned_singleton_toReal (x : I.ThetaPilotPoint v) :
    (sourceSetVolumeSigned I v {x}).toReal =
      max 0 (-I.sourceLocalLogDegree v x) := by
  rw [sourceSetVolumeSigned_singleton]
  change (ENNReal.ofReal (-I.sourceLocalLogDegree v x)).toReal = max 0 _
  rw [ENNReal.toReal_ofReal']
  exact max_comm (-I.sourceLocalLogDegree v x) 0

theorem hpoint_of_point_logDegree_le
    {point : Nat -> Nat -> Nat -> I.ThetaPilotPoint v}
    {eps D1 : Real}
    (h : forall a b c : Nat, IsABCTriple a b c ->
      max 0 (-I.sourceLocalLogDegree v (point a b c)) <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1) :
    forall a b c : Nat, IsABCTriple a b c ->
      (sourceSetVolumeSigned I v {point a b c}).toReal <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D1 := by
  intro a b c habc
  rw [sourceSetVolumeSigned_singleton_toReal]
  exact h a b c habc

#check SignedGap2SourceData
#check sourceSetVolumeSigned_singleton_toReal
#check hpoint_of_point_logDegree_le
#check signedHullFinite_of_logDegree_ge

end LeanFormal.IUT.XiFPaper.S2611SignedGap2SourceActual
end