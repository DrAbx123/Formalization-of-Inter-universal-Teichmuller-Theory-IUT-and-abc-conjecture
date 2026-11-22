/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellIQTensorPacket

/-! # Log-shell IQ tensor packet: consumer closure laws -/

namespace LeanFormal.IUT

variable {ι : Type*}

/-- Pointwise addition of two packet members stays in the packet. -/
theorem sourceLogShellIQDirectSumPacket_add_mem
    (D : ι → SourceLogShellDatum)
    {x y : (i : ι) → (D i).K}
    (hx : x ∈ sourceLogShellIQDirectSumPacket D)
    (hy : y ∈ sourceLogShellIQDirectSumPacket D) :
    (fun i => x i + y i) ∈ sourceLogShellIQDirectSumPacket D := by
  rw [sourceLogShellIQDirectSumPacket_mem_iff] at hx hy ⊢
  intro i
  exact (D i).IQSpan.add_mem (hx i) (hy i)

/-- The zero section is a packet member. -/
theorem sourceLogShellIQDirectSumPacket_zero_mem
    (D : ι → SourceLogShellDatum) :
    (0 : (i : ι) → (D i).K) ∈ sourceLogShellIQDirectSumPacket D := by
  rw [sourceLogShellIQDirectSumPacket_mem_iff]
  intro i
  exact (D i).IQSpan.zero_mem

/-- Pointwise negation of a packet member stays in the packet. -/
theorem sourceLogShellIQDirectSumPacket_neg_mem
    (D : ι → SourceLogShellDatum)
    {x : (i : ι) → (D i).K}
    (hx : x ∈ sourceLogShellIQDirectSumPacket D) :
    (fun i => -x i) ∈ sourceLogShellIQDirectSumPacket D := by
  rw [sourceLogShellIQDirectSumPacket_mem_iff] at hx ⊢
  intro i
  exact (D i).IQSpan.neg_mem (hx i)

end LeanFormal.IUT
