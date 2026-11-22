import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSHETransportLaws
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3138: identity anchoring of the (SHE) transport laws

The Card-SHE module `StepXI/SourceSHETransportLaws.lean` introduces the
link-conjugation engine `FPrimeStripLink.conjugate` and the simultaneity square
`SourceSimultaneousHolomorphicExpression` with the (xi-b) consumer wiring
`sheSlot_evidence`.  What is missing there is the *identity anchoring*: that
conjugation by identity strip equivalences does not change a link, hence that
the square transport has the identity transport as its unit.

This file supplies that anchoring law, pointwise on the three fibers
(`Pi`, `G`, `Mon`), and the resulting statement-level preservation of the
simultaneity square and of the (SHE) evidence consumer.  No Kummer leg, no
holomorphic-hull expression and no times-mu upgrade is constructed: this is the
transport-unit law of the reduced Card-SHE interface, not a closure of the
Card-SHE source obligation.

Source: IUT III, Remark 3.11.1, (iii) (SHE); Corollary 3.12, proof Step (xi-b).
-/

namespace LeanFormal.IUT.XiFPaper.S3138SourceSHETransportLawsActual

open LeanFormal.IUT

universe uv upi umon

variable {V : Type uv}
variable {A B A' B' C D : FPrimeStrip.{umon, uv, upi} V}

/-! ## 1. Identity conjugation is the identity on the fibers -/

/-- Conjugation by identity strip equivalences keeps the Pi fiber values. -/
theorem conjugate_refl_refl_mapPi
    (L : FPrimeStripLink A B) (v : V) (x : A.toDPrimeStrip.Pi v) :
    (L.conjugate (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)).mapPi v x =
      L.mapPi v x := by
  rw [FPrimeStripLink.conjugate_mapPi_apply]
  simp [FPrimeStripEquiv.refl, MulEquiv.refl_symm]

/-- Conjugation by identity strip equivalences keeps the G fiber values. -/
theorem conjugate_refl_refl_mapG
    (L : FPrimeStripLink A B) (v : V) (x : A.G v) :
    (L.conjugate (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)).mapG v x =
      L.mapG v x := by
  rw [FPrimeStripLink.conjugate_mapG_apply]
  simp [FPrimeStripEquiv.refl, MulEquiv.refl_symm]

/-- Conjugation by identity strip equivalences keeps the Mon fiber values. -/
theorem conjugate_refl_refl_mapMon
    (L : FPrimeStripLink A B) (v : V) (x : A.Mon v) :
    (L.conjugate (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)).mapMon v x =
      L.mapMon v x := by
  rw [FPrimeStripLink.conjugate_mapMon_apply]
  simp [FPrimeStripEquiv.refl, MulEquiv.refl_symm]

/-- Conjugation by identity strip equivalences keeps the index map. -/
theorem conjugate_refl_refl_index (L : FPrimeStripLink A B) (v : V) :
    (L.conjugate (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)).index v =
      L.index v := rfl

/-! ## 2. The transported simultaneity square is a simultaneous square -/

/-- Transporting a simultaneity square along the identity quadruple of strip
equivalences is again a simultaneity square: the transport has the identity
transport as its unit. -/
theorem transport_refl_refl_sheStatement
    {uH : FPrimeStripLink A B} {lH : FPrimeStripLink C D}
    {lK : FPrimeStripLink A C} {rK : FPrimeStripLink B D}
    (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK) :
    (E.transport (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)
        (FPrimeStripEquiv.refl C) (FPrimeStripEquiv.refl D)).sheStatement :=
  (E.transport (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)
    (FPrimeStripEquiv.refl C) (FPrimeStripEquiv.refl D)).simultaneous

/-- The (xi-b) consumer wiring at the identity transport: the (SHE) slot of a
contract whose statement is the transported reflexive square is inhabited by
the transported simultaneity. -/
theorem sheSlot_evidence_transport_refl
    {uH : FPrimeStripLink A B} {lH : FPrimeStripLink C D}
    {lK : FPrimeStripLink A C} {rK : FPrimeStripLink B D}
    (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK)
    {contract : StepXIContract}
    (h : contract.she =
      (E.transport (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)
        (FPrimeStripEquiv.refl C) (FPrimeStripEquiv.refl D)).sheStatement) :
    contract.she :=
  SourceSimultaneousHolomorphicExpression.sheSlot_evidence
    (E.transport (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)
      (FPrimeStripEquiv.refl C) (FPrimeStripEquiv.refl D)) h

/-- The Pi-fiber component of the transported simultaneity equation at the
identity transport is the original fiber equation. -/
theorem transport_refl_simultaneous_mapPi
    {uH : FPrimeStripLink A B} {lH : FPrimeStripLink C D}
    {lK : FPrimeStripLink A C} {rK : FPrimeStripLink B D}
    (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK)
    (v : V) (x : A.toDPrimeStrip.Pi v) :
    (E.transport (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)
        (FPrimeStripEquiv.refl C) (FPrimeStripEquiv.refl D)).simultaneous_index v
        ▸ ((E.transport (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)
          (FPrimeStripEquiv.refl C) (FPrimeStripEquiv.refl D)).domainExpression.mapPi v x) =
      (E.transport (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)
        (FPrimeStripEquiv.refl C) (FPrimeStripEquiv.refl D)).codomainExpression.mapPi v x :=
  SourceSimultaneousHolomorphicExpression.simultaneous_mapPi_apply
    (E.transport (FPrimeStripEquiv.refl A) (FPrimeStripEquiv.refl B)
      (FPrimeStripEquiv.refl C) (FPrimeStripEquiv.refl D)) v x

end LeanFormal.IUT.XiFPaper.S3138SourceSHETransportLawsActual

end
