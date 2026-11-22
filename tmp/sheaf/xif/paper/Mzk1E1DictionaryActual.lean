import tmp.sheaf.xif.paper.Mzk1VPaperActual
import tmp.sheaf.xif.paper.Mzk1ScaledPaper312Actual
import Mathlib.Tactic

/-!
# A912 E1 dictionary + wild hull packet shapes (shehdd)

## E1 dictionary

`E1Dictionary V_norm V_hull` is the **interface** for the paper normalization relation
`V_norm = V_hull` (our paper-normalized `V` equals the hull volume `V`).  It is a
condition, not an assumption; the file proves the equivalent forms and a conditional
consumer for the scaled paper statement.

Instantiation on the actual green objects:
`E1PaperScaledHull T P k := E1Dictionary (VPaper T P k) (thetaScaledLog T k)`, and
`VPaper = thetaScaledLog + qSideContribution`, so this holds iff `qSideContribution P = 0`.

## Wild hull packet

Abstract shape of lana `VcI.lean:806 hullPacket_finite`:
`H_v = ∑_c w_c·∑_j ρ_{c j}·log p`, where `ρ = logShellRadius`
(`VcI.lean:464`); tame value `ρ = 1 − 1/e` (`VcI.lean:844`).  The wild correction is
`∑ w_c·∑_j (ρ_{c j} − (1 − 1/e_{c j}))·log p`; `vcIPacket` adds the `orderVol` term.

No RETRACTED statement.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1E1DictionaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1VPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open scoped BigOperators ENNReal

/-- **E1 dictionary (interface)**: the paper-normalized `V` equals the hull volume `V`. -/
def E1Dictionary (V_norm V_hull : ℝ) : Prop := V_norm = V_hull

theorem E1Dictionary_iff (V_norm V_hull : ℝ) :
    E1Dictionary V_norm V_hull ↔ V_norm = V_hull := Iff.rfl

theorem E1Dictionary_symm {V_norm V_hull : ℝ} (h : E1Dictionary V_norm V_hull) :
    E1Dictionary V_hull V_norm := h.symm

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- E1 on the actual green objects: paper-normalized `VPaper` equals the scaled θ-hull
log-volume reading `thetaScaledLog`. -/
def E1PaperScaledHull (k : ℕ) : Prop :=
  E1Dictionary (VPaper T P k) (thetaScaledLog T k)

/-- `VPaper = thetaScaledLog + qSideContribution`, so E1 holds iff the q-side
contribution vanishes in this normalization. -/
theorem E1PaperScaledHull_iff_qSide_zero (k : ℕ) :
    E1PaperScaledHull T P k ↔ qSideContribution P = 0 := by
  unfold E1PaperScaledHull E1Dictionary VPaper
  constructor <;> intro h <;> linarith

/-- Conditional consumer: under E1, the scaled paper statement is `q ≤ VPaper`. -/
theorem scaledPaper312_iff_of_E1 (k : ℕ) (q : ℝ)
    (hE1 : E1PaperScaledHull T P k) :
    ScaledPaper312Statement T q k ↔ q ≤ VPaper T P k := by
  unfold E1PaperScaledHull E1Dictionary at hE1
  unfold ScaledPaper312Statement
  rw [← hE1]

/-- **Wild hull packet shape** (lana `hullPacket_finite`): `∑_c w_c·∑_j ρ_{c j}·log p`. -/
def WildHullPacket {ι : Type*} [Fintype ι] (w rho : ι → ℝ) (logp : ℝ) : ℝ :=
  ∑ i, w i * rho i * logp

/-- Tame hull packet shape (lana `hullPacket_tame`): `∑_c w_c·∑_j (1 − 1/e_j)·log p`. -/
def TameHullPacket {ι : Type*} [Fintype ι] (w : ι → ℝ) (e : ι → ℝ) (logp : ℝ) : ℝ :=
  ∑ i, w i * ((1 - 1 / e i) * logp)

/-- The wild correction: `∑_c w_c·∑_j (ρ_j − (1 − 1/e_j))·log p`. -/
def WildCorrection {ι : Type*} [Fintype ι] (w rho e : ι → ℝ) (logp : ℝ) : ℝ :=
  ∑ i, w i * ((rho i - (1 - 1 / e i)) * logp)

/-- **Decomposition of the wild hull packet**: `H_v = tame part + wild correction`. -/
theorem wildHullPacket_eq_tame_add_correction {ι : Type*} [Fintype ι]
    (w rho e : ι → ℝ) (logp : ℝ) :
    WildHullPacket w rho logp = TameHullPacket w e logp + WildCorrection w rho e logp := by
  unfold WildHullPacket TameHullPacket WildCorrection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `vcIPacket` adds the packet index `orderVol`:
`VC_v = H_v + orderVol` is the tame-case form; in general the hull/tensor defect is
`H_v − VC_v` (the `orderVol` term).  This definition records the shape, not an identity. -/
def VCIPacketWithOrderVol {ι : Type*} [Fintype ι]
    (w rho : ι → ℝ) (logp orderVol : ℝ) : ℝ :=
  WildHullPacket w rho logp + orderVol

structure E1Row where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def e1Rows : List E1Row :=
  [ ⟨"E1 dictionary", "E1Dictionary V_norm V_hull := V_norm = V_hull (interface, not assumed)", "DEF"⟩
  , ⟨"E1 on green objects", "E1PaperScaledHull T P k := VPaper T P k = thetaScaledLog T k", "DEF"⟩
  , ⟨"E1 iff qSide zero", "E1PaperScaledHull <-> qSideContribution P = 0 (since VPaper = thetaScaledLog + qSide)", "PROVED"⟩
  , ⟨"E1 consumer", "E1 => ScaledPaper312Statement q k <-> q <= VPaper T P k", "PROVED"⟩
  , ⟨"wild hull packet", "H_v = sum_c w_c * sum_j rho_cj * log p (rho = logShellRadius, lana VcI.lean:806)", "DEF"⟩
  , ⟨"wild decomposition", "H_v = tame sum + sum w_c*(rho - (1-1/e))*log p", "PROVED (wildHullPacket_eq_tame_add_correction)"⟩
  , ⟨"VC(I) packet", "vcIPacket = shellExcess + orderVol (lana VcI.lean:794); VCIPacketWithOrderVol records shape", "DEF"⟩
  , ⟨"wild correction bound", "|shellDefect + orderVol| <= sum (3 + log e_j) (lana Gap.lean:438)", "EXTERNAL_LANA"⟩
  , ⟨"remaining", "exact wild rho / paper identification of E1 (qSide=0 or absorbed)", "PENDING"⟩
  , ⟨"scope", "interface/conditional only; no fake hull identity; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem e1Rows_length : e1Rows.length = 10 := rfl

theorem e1Rows_has_pending :
    e1Rows.any (fun r => r.status = "PENDING") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1E1DictionaryActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1E1DictionaryActual.E1PaperScaledHull_iff_qSide_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1E1DictionaryActual.scaledPaper312_iff_of_E1
#print axioms LeanFormal.IUT.XiFPaper.Mzk1E1DictionaryActual.wildHullPacket_eq_tame_add_correction
