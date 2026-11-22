import tmp.sheaf.xif.paper.S2833S2800HregionActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2808S2800HalfNormalizedActual
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
open LeanFormal.IUT.XiFPaper.S2800LineBundleCor312BridgeActual
open scoped ENNReal
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2958HalfIQHullCertificateActual

abbrev S2958l : PrimeGeFive := S2833l

noncomputable abbrev S2958W :
    IQHullLogVolumeInterface (S2800Carrier S2958l) :=
  S2808HalfIQHull S2958l 1

def S2958Pt : Unit -> S2800Carrier S2958l := fun _ => 1

theorem S2958_hpt : forall i, S2958Pt i ∈ S2958W.imageSet := by
  intro i
  change (1 : S2800Carrier S2958l) ∈ ({1} : Set (S2800Carrier S2958l))
  simp

noncomputable def S2958Data : WeightedValues Unit where
  value := fun _ => 0
  weight := fun _ => 1
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by simp

theorem S2958_hvalue :
    forall i, S2958Data.value i =
      (iqHullFiniteHull S2958W S2958Pt S2958_hpt).volume i := by
  intro i
  change (0 : Real) = (S2958W.logVolume ({1} : Set (S2800Carrier S2958l))).toReal
  simpa [S2958l, S2958W, S2808HalfIQHull] using S2833_hull_volume_zero.symm

theorem S2958_hw : forall i, 0 <= S2958Data.weight i := by
  intro i
  norm_num [S2958Data]

theorem S2958_thetaHull_zero : iqHullRealVolume S2958W = 0 := by
  unfold iqHullRealVolume
  simpa [S2958W, S2808HalfIQHull] using S2833_hull_volume_zero

noncomputable def S2958HalfIQHullCertificate :
    StepXIFiniteCertificate Unit :=
  iqHullCertificate S2958W S2958Pt S2958_hpt S2958Data S2958_hvalue S2958_hw
    (iqHullRealVolume S2958W - 1) (iqHullRealVolume S2958W)
    (by
      rw [show S2958W.imageSet = S2958W.hull from rfl]
      rw [iqHull_logVolume_hull_eq_ofReal S2958W]
      apply ENNReal.ofReal_le_ofReal
      linarith [S2958_thetaHull_zero])
    (by rw [iqHull_logVolume_hull_eq_ofReal S2958W])
    (by rw [S2958_thetaHull_zero])
    (by rw [S2958_thetaHull_zero]; norm_num)

theorem S2958_hullVolume_eq :
    (S2958HalfIQHullCertificate.hull).hullVolume = 0 := by
  change iqHullRealVolume S2958W = 0
  exact S2958_thetaHull_zero

theorem S2958_thetaSigned_eq :
    S2958HalfIQHullCertificate.thetaSigned = 0 :=
  S2958_thetaHull_zero

theorem S2958_q_le_theta :
    S2958HalfIQHullCertificate.qSigned <= S2958HalfIQHullCertificate.thetaSigned :=
  StepXIFiniteCertificate.q_le_theta _

/-- Half-IQ-hull centered at the actual log-shell point of an ABC triple. -/
noncomputable abbrev S2958WAt (a b c : Nat) :
    IQHullLogVolumeInterface (S2800Carrier S2958l) :=
  S2808HalfIQHull S2958l (S2781LogShellPoint S2958l a b c)

def S2958PtAt (a b c : Nat) : Unit -> S2800Carrier S2958l :=
  fun _ => S2781LogShellPoint S2958l a b c

theorem S2958_hptAt (a b c : Nat) :
    forall i, S2958PtAt a b c i ∈ (S2958WAt a b c).imageSet := by
  intro i
  change S2781LogShellPoint S2958l a b c ∈
    ({S2781LogShellPoint S2958l a b c} : Set (S2800Carrier S2958l))
  simp

noncomputable def S2958DataAt (a b c : Nat) : WeightedValues Unit where
  value := fun _ => iqHullRealVolume (S2958WAt a b c)
  weight := fun _ => 1
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by simp

theorem S2958_hvalueAt (a b c : Nat) :
    forall i, (S2958DataAt a b c).value i =
      (iqHullFiniteHull (S2958WAt a b c) (S2958PtAt a b c)
        (S2958_hptAt a b c)).volume i := by
  intro i
  rfl

theorem S2958_hwAt (a b c : Nat) :
    forall i, 0 <= (S2958DataAt a b c).weight i := by
  intro i
  norm_num [S2958DataAt]

/-- Nontrivial certificate at the actual log-shell point: hull volume is the
actual half-IQ-hull log-volume, not a self-referential thetaSigned. -/
noncomputable def S2958HalfIQHullCertificateAt
    (a b c : Nat) (habc : IsABCTriple a b c) :
    StepXIFiniteCertificate Unit :=
  iqHullCertificate (S2958WAt a b c) (S2958PtAt a b c)
    (S2958_hptAt a b c) (S2958DataAt a b c)
    (S2958_hvalueAt a b c) (S2958_hwAt a b c)
    (-1) (iqHullRealVolume (S2958WAt a b c) + 1)
    (by
      rw [show ENNReal.ofReal (-1 : Real) = 0 by norm_num]
      exact bot_le)
    (by
      rw [iqHull_logVolume_hull_eq_ofReal (S2958WAt a b c)]
      apply ENNReal.ofReal_le_ofReal
      linarith [iqHullRealVolume_nonneg (S2958WAt a b c)])
    (by linarith [iqHullRealVolume_nonneg (S2958WAt a b c)])
    (by norm_num)

theorem S2958_hullVolumeAt_eq :
    (S2958HalfIQHullCertificateAt a b c habc).hull.hullVolume =
      iqHullRealVolume (S2958WAt a b c) := rfl

#check S2958W
#check S2958HalfIQHullCertificate
#check S2958_hullVolume_eq
#check S2958_thetaSigned_eq
#check S2958_q_le_theta
#print axioms S2958HalfIQHullCertificate
#print axioms S2958_hullVolume_eq
#check S2958HalfIQHullCertificateAt
#print axioms S2958HalfIQHullCertificateAt
#print axioms S2958_hullVolumeAt_eq

end LeanFormal.IUT.XiFPaper.S2958HalfIQHullCertificateActual
end