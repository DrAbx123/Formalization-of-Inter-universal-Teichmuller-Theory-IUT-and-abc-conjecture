import tmp.sheaf.xif.paper.ConcreteThetaLinkActual
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilyLawsReduction
import LeanFormal.IUT.IUTI.HodgeTheater.ConcreteIntegralHodgeTheaterExample

/-!
# Concrete C3/source-theater theta-packet identification

IUT II, Corollary 4.10 and IUT III, Definition 3.8, (i): the theta packet of the
concrete q-pilot strip is the actual theta packet of the source theater.  The
source Hodge-theater family carries the actual theorem that all family members
have the same theta packet; the concrete Gaussian packet has the actual q/scale
equalities with gaussianFiveThetaQ.

This file constructs:

* ConcreteThetaPacketIdentification: concrete C3 packet, source theater packet,
  and the actual packet equality;
* ConcreteThetaPacketQIdentification: the actual q and scale equalities;
* concreteThetaPacketQIdentification: actual concrete inhabitant built from
  ConcreteThetaLinkActual's evidence and the source family packet equality;
* actual Gaussian packet q/scale equalities for the concrete Gaussian theater.

No empty type, no True/PUnit, no fake identification.  No inequality.
WRITE-ONLY; no local compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.ConcreteThetaPacketIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkActual
open LeanFormal.IUT.XiFPaper.ConcreteC3DonorActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkActual

universe ua upi umon ui

variable {l : PrimeGeFive}

/-- The actual concrete q/scale identification of a C3 theta packet with the
source-theater packet. -/
structure ConcreteThetaPacketQIdentification
    (c3Packet sourcePacket : FiniteThetaPacket l) where
  q_eq : c3Packet.q = sourcePacket.q
  scale_eq : ∀ j : SignedLabel l.value,
    c3Packet.scale j = sourcePacket.scale j

/-- The full concrete C3/source-theater theta-packet identification. -/
structure ConcreteThetaPacketIdentification
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) where
  c3Packet : FiniteThetaPacket l
  sourcePacket : FiniteThetaPacket l
  packet_eq : c3Packet = sourcePacket
  q_identification : ConcreteThetaPacketQIdentification c3Packet sourcePacket

/-- The actual concrete C3 theta packet from ConcreteThetaLinkActual's
evidence. -/
noncomputable def concreteC3ThetaPacket
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    FiniteThetaPacket l :=
  (concreteThetaLinkKummerEvidence I).thetaPacket

/-- The actual source-theater theta packet at the (1,0) family member. -/
noncomputable def concreteSourceThetaPacket
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    FiniteThetaPacket l :=
  (I.theaterAt 1 0).thetaPacket

/-- The actual concrete C3 packet equals the concreteThetaPacket of ConcreteC3. -/
theorem concreteC3ThetaPacket_eq
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    concreteC3ThetaPacket I = concreteThetaPacket I :=
  concreteThetaLinkKummerEvidence_thetaPacket I

/-- The actual packet equality: the concrete C3 packet equals the source theater
packet, via the source Hodge-theater family's actual thetaPacket_eq theorem. -/
theorem concreteC3ThetaPacket_eq_source
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    concreteC3ThetaPacket I = concreteSourceThetaPacket I := by
  rw [concreteC3ThetaPacket_eq]
  change (I.theaterAt 0 0).thetaPacket = (I.theaterAt 1 0).thetaPacket
  simpa [OriginalInput.theaterAt] using
    I.family.thetaPacket_eq (I.indexOf 0 0) (I.indexOf 1 0)

/-- The actual concrete q/scale identification. -/
noncomputable def concreteThetaPacketQIdentification
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    ConcreteThetaPacketQIdentification
      (concreteC3ThetaPacket I) (concreteSourceThetaPacket I) where
  q_eq := congrArg (fun packet : FiniteThetaPacket l => packet.q)
    (concreteC3ThetaPacket_eq_source I)
  scale_eq := fun j =>
    congrArg (fun packet : FiniteThetaPacket l => packet.scale j)
      (concreteC3ThetaPacket_eq_source I)

/-- The actual full concrete packet identification. -/
noncomputable def concreteThetaPacketIdentification
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    ConcreteThetaPacketIdentification I where
  c3Packet := concreteC3ThetaPacket I
  sourcePacket := concreteSourceThetaPacket I
  packet_eq := concreteC3ThetaPacket_eq_source I
  q_identification := concreteThetaPacketQIdentification I

/-- The concrete identification's q equality. -/
theorem concreteThetaPacketIdentification_q
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    (concreteThetaPacketIdentification I).c3Packet.q =
      (concreteThetaPacketIdentification I).sourcePacket.q :=
  (concreteThetaPacketIdentification I).q_identification.q_eq

/-- The concrete identification's scale equality. -/
theorem concreteThetaPacketIdentification_scale
    (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    (j : SignedLabel l.value) :
    (concreteThetaPacketIdentification I).c3Packet.scale j =
      (concreteThetaPacketIdentification I).sourcePacket.scale j :=
  (concreteThetaPacketIdentification I).q_identification.scale_eq j

/-- Actual Gaussian packet q equality for the concrete Gaussian theater. -/
theorem gaussianThetaPacket_q :
    (gaussianFiniteIntegralHodgeTheater l).thetaPacket.q = gaussianFiveThetaQ :=
  gaussianFiniteIntegralHodgeTheater_q l

/-- Actual Gaussian packet scale equality for the concrete Gaussian theater. -/
theorem gaussianThetaPacket_scale (j : SignedLabel l.value) :
    (gaussianFiniteIntegralHodgeTheater l).thetaPacket.scale j =
      realThetaValue gaussianFiveThetaQ j.1 := by
  rw [(gaussianFiniteIntegralHodgeTheater l).thetaPacket.scale_eq,
    gaussianFiniteIntegralHodgeTheater_q]

end LeanFormal.IUT.XiFPaper.ConcreteThetaPacketIdentificationActual
