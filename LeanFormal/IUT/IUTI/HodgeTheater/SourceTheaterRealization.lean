/-
  Source-side Hodge theater realization packaging.

  Paper anchor: IUT I, Section 4 (the source-side Hodge-theater construction
  from initial Theta-data); audit item `IUT-I.hodge-theater-source`
  (`IUTI/HodgeTheater/SourceObligations.lean:5`).

  This module packages the record-to-theater construction.  A
  `SourceTheaterRealization` adds the two pieces that Definition 3.1 data
  does not carry as fields: an `FPrimeStrip` carrier over the record's
  selected-place carrier and a finite theta packet.  The packaging theorem
  reads off the `HodgeTheater` object; links between realizations induce
  `HodgeTheaterLink`s, and the refl/symm/trans laws of the realization-level
  links map onto the proved theater-link algebra.

  The module also records, as a proved negative result, that the record alone
  does not determine the prime-strip carrier: over the same record and packet
  there are realizations whose carriers at a selected place are `ZMod 2` vs
  `ZMod 4`, and no monoid is isomorphic to both.  So the carrier is a source
  input (matching the audit note "The source construction must provide the
  arithmetic and geometric structures"), not a function of the record.

  Not claimed: construction of the carrier from arbitrary Definition 3.1 data
  alone (source existence); etale, Frobenioid, or Hodge-Arakelov
  compatibility fields of the paper's theaters.
-/
import LeanFormal.IUT.IUTI.HodgeTheater.HodgeTheaterCore
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

set_option linter.checkUnivs false

namespace LeanFormal.IUT

open LeanFormal.IUT.InitialThetaSource

universe uv upi umon

/-! ## 1. Record-to-theater packaging -/

/-- A source-side realization of a Hodge theater over a Definition 3.1
record: the record supplies the arithmetic input, and the realization adds
the D/F prime-strip carrier over the record's selected-place carrier plus a
finite theta packet.  Both added pieces are explicit inputs; neither is
derived from the record (see `carrierNotDeterminedByRecord`). -/
structure SourceTheaterRealization {l : PrimeGeFive}
    (D : SourceInitialThetaCandidate.{uv} l) where
  primeStrip : FPrimeStrip.{umon, uv, upi} D.V
  thetaPacket : FiniteThetaPacket l

namespace SourceTheaterRealization

variable {l : PrimeGeFive} {D : SourceInitialThetaCandidate.{uv} l}

/-- The packaged Hodge theater: arithmetic from the record, carrier and
packet from the realization. -/
def theater (R : SourceTheaterRealization D) : HodgeTheater l D.V where
  arithmetic := D.arithmetic
  primeStrip := R.primeStrip
  thetaPacket := R.thetaPacket

@[simp] theorem theater_arithmetic (R : SourceTheaterRealization D) :
    R.theater.arithmetic = D.arithmetic := rfl

@[simp] theorem theater_primeStrip (R : SourceTheaterRealization D) :
    R.theater.primeStrip = R.primeStrip := rfl

@[simp] theorem theater_thetaPacket (R : SourceTheaterRealization D) :
    R.theater.thetaPacket = R.thetaPacket := rfl

/-- The clause-carrying source record feeds the same packaging through its
candidate. -/
def ofSourceData (S : SourceInitialThetaData l)
    (primeStrip : FPrimeStrip S.candidate.V) (thetaPacket : FiniteThetaPacket l) :
    SourceTheaterRealization S.candidate :=
  { primeStrip := primeStrip, thetaPacket := thetaPacket }

end SourceTheaterRealization

/-! ## 2. Realization links and their algebra -/

/-- A link between two realizations over the same record: a prime-strip
equivalence plus alignment of the theta packet (q and all scales). -/
structure SourceTheaterLink {l : PrimeGeFive} {D : SourceInitialThetaCandidate l}
    (R S : SourceTheaterRealization.{uv, upi, umon} D) where
  stripEquiv : FPrimeStripEquiv R.primeStrip S.primeStrip
  theta_q_eq : R.thetaPacket.q = S.thetaPacket.q
  theta_scale_eq :
    ∀ j : SignedLabel l.value, R.thetaPacket.scale j = S.thetaPacket.scale j

namespace SourceTheaterLink

variable {l : PrimeGeFive} {D : SourceInitialThetaCandidate.{uv} l}
variable {R S T : SourceTheaterRealization D}

def refl (R : SourceTheaterRealization D) : SourceTheaterLink R R where
  stripEquiv := FPrimeStripEquiv.refl R.primeStrip
  theta_q_eq := rfl
  theta_scale_eq := fun _ => rfl

def symm (L : SourceTheaterLink R S) : SourceTheaterLink S R where
  stripEquiv := FPrimeStripEquiv.symm L.stripEquiv
  theta_q_eq := L.theta_q_eq.symm
  theta_scale_eq := fun j => (L.theta_scale_eq j).symm

def trans (L : SourceTheaterLink R S) (M : SourceTheaterLink S T) :
    SourceTheaterLink R T where
  stripEquiv := FPrimeStripEquiv.trans L.stripEquiv M.stripEquiv
  theta_q_eq := L.theta_q_eq.trans M.theta_q_eq
  theta_scale_eq := fun j => (L.theta_scale_eq j).trans (M.theta_scale_eq j)

theorem symm_symm (L : SourceTheaterLink R S) : L.symm.symm = L := by
  cases L
  rfl

theorem refl_trans (L : SourceTheaterLink R S) : trans (refl R) L = L := by
  cases L
  rfl

theorem trans_refl (L : SourceTheaterLink R S) : trans L (refl S) = L := by
  cases L
  rfl

/-- Forgetting the realization layer: a realization link induces a theater
link between the packaged theaters. -/
def toTheaterLink (L : SourceTheaterLink R S) :
    HodgeTheaterLink R.theater S.theater where
  primeStripEquiv := L.stripEquiv
  theta_q_eq := L.theta_q_eq
  theta_scale_eq := L.theta_scale_eq

theorem toTheaterLink_refl (R : SourceTheaterRealization D) :
    (refl R).toTheaterLink = HodgeTheaterLink.refl R.theater := by
  cases R
  rfl

theorem toTheaterLink_symm (L : SourceTheaterLink R S) :
    (L.symm).toTheaterLink = (L.toTheaterLink).symm := by
  cases L
  rfl

theorem toTheaterLink_trans (L : SourceTheaterLink R S)
    (M : SourceTheaterLink S T) :
    (L.trans M).toTheaterLink = (L.toTheaterLink).trans (M.toTheaterLink) := by
  cases L
  cases M
  rfl

end SourceTheaterLink

/-! ## 3. The record does not determine the carrier (negative result) -/

section CarrierNonDetermination

variable {l : PrimeGeFive} (D : SourceInitialThetaCandidate.{uv} l)
variable (packet : FiniteThetaPacket l)

/-- Realization whose prime-strip carries the two-element ring `ZMod 2`
(multiplicatively) at every selected place, with trivial action and degree. -/
def zmodTwoCarrierRealization : SourceTheaterRealization D where
  primeStrip :=
    { Pi := fun _ => Multiplicative (ZMod 2)
      groupPi := fun _ => inferInstance
      G := fun _ => Multiplicative (ZMod 2)
      groupG := fun _ => inferInstance
      proj := fun _ => MonoidHom.id _
      proj_surjective := fun _ => Function.surjective_id
      Mon := fun _ => ZMod 2
      commMonoidMon := fun _ => inferInstance
      action := fun _ =>
        { toFun := fun _ => 1
          map_one' := rfl
          map_mul' := by intro a b; simp }
      degree := fun _ =>
        { toFun := fun _ => 1
          map_one' := rfl
          map_mul' := by intro a b; simp } }
  thetaPacket := packet

/-- Same record and packet, carrier `ZMod 4` at every selected place. -/
def zmodFourCarrierRealization : SourceTheaterRealization D where
  primeStrip :=
    { Pi := fun _ => Multiplicative (ZMod 4)
      groupPi := fun _ => inferInstance
      G := fun _ => Multiplicative (ZMod 4)
      groupG := fun _ => inferInstance
      proj := fun _ => MonoidHom.id _
      proj_surjective := fun _ => Function.surjective_id
      Mon := fun _ => ZMod 4
      commMonoidMon := fun _ => inferInstance
      action := fun _ =>
        { toFun := fun _ => 1
          map_one' := rfl
          map_mul' := by intro a b; simp }
      degree := fun _ =>
        { toFun := fun _ => 1
          map_one' := rfl
          map_mul' := by intro a b; simp } }
  thetaPacket := packet

@[simp] theorem zmodTwoCarrierRealization_thetaPacket :
    (zmodTwoCarrierRealization D packet).thetaPacket = packet := rfl

@[simp] theorem zmodFourCarrierRealization_thetaPacket :
    (zmodFourCarrierRealization D packet).thetaPacket = packet := rfl

@[simp] theorem zmodTwoCarrierRealization_Mon (v : D.V) :
    (zmodTwoCarrierRealization D packet).primeStrip.Mon v = ZMod 2 := rfl

@[simp] theorem zmodFourCarrierRealization_Mon (v : D.V) :
    (zmodFourCarrierRealization D packet).primeStrip.Mon v = ZMod 4 := rfl

theorem noEquivZmodTwoZmodFour : ¬ Nonempty (ZMod 2 ≃ ZMod 4) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  rw [ZMod.card 2, ZMod.card 4] at h
  norm_num at h

/-- The multiplicative-monoid version, derived from the underlying
equivalence. -/
theorem noMulEquivZmodTwoZmodFour : ¬ Nonempty (ZMod 2 ≃* ZMod 4) :=
  fun h => noEquivZmodTwoZmodFour (h.map MulEquiv.toEquiv)

/-- Given a selected place, the two realizations over the same record and
packet are not related by any prime-strip equivalence. -/
theorem zmodCarrierRealizationsNotStripEquiv (v₀ : D.V) :
    ¬ Nonempty (FPrimeStripEquiv
      (zmodTwoCarrierRealization D packet).primeStrip
      (zmodFourCarrierRealization D packet).primeStrip) := by
  rintro ⟨phi⟩
  exact noMulEquivZmodTwoZmodFour ⟨phi.isoMon v₀⟩

/-- No single type is even in bijection with both carriers at the selected
place (so no monoid is isomorphic to both): the record, together with the
packet, does not determine the carrier, and the carrier must be supplied by
the source. -/
theorem carrierNotDeterminedByRecord (v₀ : D.V) :
    ¬ ∃ X : Type, Nonempty
        (X ≃ (zmodTwoCarrierRealization D packet).primeStrip.Mon v₀) ∧
      Nonempty
        (X ≃ (zmodFourCarrierRealization D packet).primeStrip.Mon v₀) := by
  rintro ⟨X, h2, h4⟩
  obtain ⟨e2⟩ := h2
  obtain ⟨e4⟩ := h4
  rw [zmodTwoCarrierRealization_Mon] at e2
  rw [zmodFourCarrierRealization_Mon] at e4
  exact noEquivZmodTwoZmodFour ⟨e2.symm.trans e4⟩

end CarrierNonDetermination

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

def sourceTheaterRealizationPackaging : Obligation :=
  { id := "IUT-I.source-theater-realization"
    source := "IUT I, Section 4 (record-to-theater packaging)"
    status := VerificationStatus.interface
    note :=
      "Packaging layer for the source-side Hodge theater: a realization adds " ++
        "the prime-strip carrier over the record's selected-place carrier and " ++
        "a finite theta packet to Definition 3.1 data; the packaged theater, " ++
        "the realization-link algebra (refl/symm/trans), and the functor to " ++
        "the proved HodgeTheaterLink algebra are certified. The construction " ++
        "from arbitrary Definition 3.1 data alone (source existence) is not " ++
        "provided here; see the carrier non-determination entry."
    dependsOn :=
      [ "IUT-I.initial-theta-data",
        "IUT-I-II.prime-strip-core",
        "IUT-I.hodge-theater-carrier-and-links" ] }

def sourceTheaterCarrierNonDetermination : Obligation :=
  { id := "IUT-I.source-theater-carrier-nondetermination"
    source := "Project negative result (cardinality obstruction)"
    status := VerificationStatus.provedKernel
    note :=
      "Over any fixed Definition 3.1 candidate and any fixed finite theta " ++
        "packet, two source realizations carry ZMod 2 and ZMod 4 monoids at " ++
        "every selected place; no type is in bijection with both carriers " ++
        "(no monoid is isomorphic to both), and given a place no prime-strip " ++
        "equivalence exists between them. The record therefore does not " ++
        "determine the carrier: it must be supplied by the source, matching " ++
        "the audit note of IUT-I.hodge-theater-source."
    dependsOn :=
      [ "IUT-I.source-theater-realization",
        "IUT-I-II.prime-strip-core" ] }

end LeanFormal.IUT.Audit
