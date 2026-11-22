import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.ContractSourceReduction

/-!
  # C9 -> IUT bridge: actual hull volume carrier

  This file connects the project's actual hull-volume declarations to the
  bridge data used by the Step-XI finite certificate. It does not introduce a
  toy Output/logVol/h structure.

  Actual declarations used:
  * FiniteHull, StepXIFiniteCertificate, StepXIFiniteCertificate.q_le_theta
    (StepXI/HolomorphicHull/Volume.lean);
  * sourceRealHullVolume, sourceThetaPilotFiniteHull, sourceHullVolume
    (StepXI/CertificateHullWiring.lean; SourceHullInterfaceDischarge.lean);
  * iqHullRealVolume, iqHullFiniteHull
    (StepXI/CertificateHullWiring.lean; IQHullLogVolumeInterface).

  For the source carrier, h is definitionally the real part of the actual
  source hull volume, and hull_upper is the actual FiniteHull.contains field.
  For the q/theta scalars we expose the named amplitude card as a structure;
  the inequality is then StepXIFiniteCertificate.q_le_theta. No h is
  postulated independently of the hull carrier.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe u v ua uv upi umon ui

/-! ## 1. Interface-level hull-volume bridge -/

/-- A bridge from a realized IQHullLogVolumeInterface to the finite-hull
certificate carrier. The field h is not arbitrary: it is the real part of the
actual interface hull log-volume, and hull_upper is the actual
FiniteHull.contains field. -/
structure InterfaceHullVolumeBridge {X : Type u} (W : IQHullLogVolumeInterface X)
    {label : Type v} [Fintype label] (pt : label -> X)
    (hpt : forall i, pt i ∈ W.imageSet) where
  hull : FiniteHull label
  h : Real
  h_eq : h = iqHullRealVolume W
  hull_eq : hull = iqHullFiniteHull W pt hpt
  hull_upper : forall i, hull.volume i <= h

/-- The canonical interface bridge, with h definitionally the real hull
log-volume. -/
def interfaceHullVolumeBridge {X : Type u} (W : IQHullLogVolumeInterface X)
    {label : Type v} [Fintype label] (pt : label -> X)
    (hpt : forall i, pt i ∈ W.imageSet) :
    InterfaceHullVolumeBridge W pt hpt where
  hull := iqHullFiniteHull W pt hpt
  h := iqHullRealVolume W
  h_eq := rfl
  hull_eq := rfl
  hull_upper := fun i => (iqHullFiniteHull W pt hpt).contains i

@[simp] theorem interfaceHullVolumeBridge_h {X : Type u}
    (W : IQHullLogVolumeInterface X) {label : Type v} [Fintype label]
    (pt : label -> X) (hpt : forall i, pt i ∈ W.imageSet) :
    (interfaceHullVolumeBridge W pt hpt).h = iqHullRealVolume W := rfl

@[simp] theorem interfaceHullVolumeBridge_hull {X : Type u}
    (W : IQHullLogVolumeInterface X) {label : Type v} [Fintype label]
    (pt : label -> X) (hpt : forall i, pt i ∈ W.imageSet) :
    (interfaceHullVolumeBridge W pt hpt).hull = iqHullFiniteHull W pt hpt := rfl

theorem interfaceHullVolumeBridge_hull_upper {X : Type u}
    (W : IQHullLogVolumeInterface X) {label : Type v} [Fintype label]
    (pt : label -> X) (hpt : forall i, pt i ∈ W.imageSet) (i : label) :
    (interfaceHullVolumeBridge W pt hpt).hull.volume i <=
      (interfaceHullVolumeBridge W pt hpt).h :=
  (interfaceHullVolumeBridge W pt hpt).hull_upper i

/-! ## 2. Source-level hull-volume bridge (actual sourceHullVolume) -/

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The source hull-volume bridge at a realized place/procession. The field h is
definitionally sourceRealHullVolume, and hull_upper is the actual
FiniteHull.contains of sourceThetaPilotFiniteHull. The finiteness hypothesis is
the one under which sourceHullVolume = ofReal sourceRealHullVolume. -/
structure SourceHullVolumeBridge (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (hfin : I.sourceHullVolume v R n < ⊤) where
  hull : FiniteHull (SignedLabel l.value)
  h : Real
  h_eq : h = I.sourceRealHullVolume v R n
  hull_eq : hull = I.sourceThetaPilotFiniteHull v R n hfin
  hull_upper : forall j, hull.volume j <= h

/-- The canonical source bridge, with h definitionally the real source hull
volume. -/
def sourceHullVolumeBridge (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (hfin : I.sourceHullVolume v R n < ⊤) :
    SourceHullVolumeBridge I v R n hfin where
  hull := I.sourceThetaPilotFiniteHull v R n hfin
  h := I.sourceRealHullVolume v R n
  h_eq := rfl
  hull_eq := rfl
  hull_upper := fun j => (I.sourceThetaPilotFiniteHull v R n hfin).contains j

@[simp] theorem sourceHullVolumeBridge_h (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (hfin : I.sourceHullVolume v R n < ⊤) :
    (sourceHullVolumeBridge I v R n hfin).h =
      I.sourceRealHullVolume v R n := rfl

@[simp] theorem sourceHullVolumeBridge_hull (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) :
    (sourceHullVolumeBridge I v R n hfin).hull =
      I.sourceThetaPilotFiniteHull v R n hfin := rfl

theorem sourceHullVolumeBridge_hull_upper (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value) :
    (sourceHullVolumeBridge I v R n hfin).hull.volume j <=
      (sourceHullVolumeBridge I v R n hfin).h :=
  (sourceHullVolumeBridge I v R n hfin).hull_upper j

/-- Nonemptiness of the signed-label packet, used by the uniform certificate
constructor. This is the actual zero label, not an arbitrary choice. -/
instance signedLabelPacketNonempty : Nonempty (SignedLabel l.value) :=
  ⟨zeroSignedLabel (l := l)⟩

end OriginalInput
end Theorem311Source

/-! ## 3. Amplitude card and q_le_theta -/

/-- Named amplitude card: the actual source hull volume is bounded by the chosen
theta scalar. This is the only inequality supplied outside the hull carrier; h
itself is not a free parameter. -/
structure SourceAmplitudeCard {l : PrimeGeFive} {V : Type uv}
    (I : Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v)
    (n : Theorem311Source.OriginalInput.ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (theta : Real) where
  hull_le_theta :
    (Theorem311Source.OriginalInput.sourceHullVolumeBridge I v R n hfin).h <= theta

namespace Theorem311Source
namespace OriginalInput

/-- Certificate from the actual source hull bridge, a named amplitude card and
the q-side comparison q <= h. This uses StepXIFiniteCertificate.q_le_theta; it
does not postulate h or hull_upper separately. -/
theorem sourceHullVolumeBridge_q_le_theta (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) {q theta : Real}
    (hq : q <= (sourceHullVolumeBridge I v R n hfin).h)
    (amp : LeanFormal.IUT.SourceAmplitudeCard I v R n hfin theta)
    (hqneg : q < 0) :
    q <= theta := by
  have hcert :
      (StepXIFiniteCertificate.ofHullUniform
        (sourceHullVolumeBridge I v R n hfin).hull q theta
        (by
          change q <= I.sourceRealHullVolume v R n
          simpa [sourceHullVolumeBridge_h] using hq)
        (by
          change I.sourceRealHullVolume v R n <= theta
          simpa [sourceHullVolumeBridge_h] using amp.hull_le_theta)
        hqneg).qSigned <=
      (StepXIFiniteCertificate.ofHullUniform
        (sourceHullVolumeBridge I v R n hfin).hull q theta
        (by
          change q <= I.sourceRealHullVolume v R n
          simpa [sourceHullVolumeBridge_h] using hq)
        (by
          change I.sourceRealHullVolume v R n <= theta
          simpa [sourceHullVolumeBridge_h] using amp.hull_le_theta)
        hqneg).thetaSigned :=
    StepXIFiniteCertificate.q_le_theta _
  simpa using hcert

end OriginalInput
end Theorem311Source

end
end LeanFormal.IUT
