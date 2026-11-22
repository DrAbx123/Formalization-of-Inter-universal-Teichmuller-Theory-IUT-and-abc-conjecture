/-
# U-C: C3 producer and the P5/P6 sandwich giving C4 = hCor312

Route section 5.4 (U-C).  The weighted packet hull algebra is owned by
Mzk1UCC3ProducerActual (weighted hull ucWeightedHpkt = sum_a w_a V_a and its
weighted C1 bound).  This file adds the missing sandwich:

* uc_sandwich: from the P5 lower bound -M <= theta_P5, the reading bound
  theta_P5 <= H_pkt and C3: H_pkt <= kappa (A - c_l Q) - M, deduce C4: c_l Q <= A
  (the accepted UCC3 algebra uc_c3_to_c4);
* uc_c4_from_weighted: the same with H_pkt being the actual weighted packet hull
  ucWeightedHpkt w V, the per-packet C1 bounds V a <= B a, and the weighted paper
  identity sum_a w_a B a = kappa (A - c_l Q) - M.

The per-packet volumes V a are the actual packet volumes of david's lane
(Mzk1ULPacketVActual.packetVActual: normalized log-volume of the holomorphic hull
of the actual possible images; actual Kummer parameter and defined exceptional
set) and the weights are the actual local-degree weights of
Mzk1ULWeightedHullActual; no Hpkt = 0 surrogate and no freely chosen weight is
used here.
-/
import tmp.sheaf.xif.paper.Mzk1UCC3Actual
import tmp.sheaf.xif.paper.Mzk1UCC3ProducerActual
import tmp.sheaf.xif.paper.Mzk1ULPacketHull2Actual
import tmp.sheaf.xif.paper.Mzk1ULWeightedHullActual
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import tmp.sheaf.xif.paper.P6HThetaNormalization2Actual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1UCHpktActual

open LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual

/-- Route section 5.4 sandwich: P5 lower bound -M <= theta_P5, reading bound
theta_P5 <= H_pkt, and C3 give C4 = hCor312. -/
theorem uc_sandwich {l A Q M theta Hpkt : ℝ} (hkappa : 0 < kappa l)
    (hP5 : -M ≤ theta) (htheta : theta ≤ Hpkt)
    (hC3 : Hpkt ≤ kappa l * (A - cL l * Q) - M) :
    cL l * Q ≤ A :=
  uc_c3_to_c4 hkappa hP5 htheta hC3

/-- C3 with the weighted packet hull, restated in the file's own namespace. -/
theorem uc_c3 {ι : Type*} [Fintype ι]
    (w hullVol paper : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hpacket : ∀ i, hullVol i ≤ paper i)
    {l A Q M : ℝ}
    (hpaper : ucWeightedPaper w paper = kappa l * (A - cL l * Q) - M) :
    ucWeightedHpkt w hullVol ≤ kappa l * (A - cL l * Q) - M := by
  have hHpkt : ucWeightedHpkt w hullVol ≤ ucWeightedPaper w paper :=
    ucWeightedHpkt_le_paper (w := w) (hullVol := hullVol) (paper := paper) hw hpacket
  exact uc_c3_from_weighted (w := w) (hullVol := hullVol) (paper := paper) hHpkt hpaper

/-- The full U-C chain with the actual weighted packet hull: per-packet C1,
weighted paper identity, P5 lower bound and reading bound give C4. -/
theorem uc_c4_from_weighted {ι : Type*} [Fintype ι]
    (w hullVol paper : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hpacket : ∀ i, hullVol i ≤ paper i)
    {l A Q M theta : ℝ} (hkappa : 0 < kappa l)
    (hP5 : -M ≤ theta)
    (htheta : theta ≤ ucWeightedHpkt w hullVol)
    (hpaper : ucWeightedPaper w paper = kappa l * (A - cL l * Q) - M) :
    cL l * Q ≤ A :=
  uc_sandwich hkappa hP5 htheta
    (uc_c3 w hullVol paper hw hpacket hpaper)
/-! ## 3. Wiring the actual per-packet value V_a (david's ulPacketVOfWitness) -/

universe u2 v2 w2

section ActualPackets

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1ULPacketVActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPacketHull2Actual

variable {K : Type u2} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v2} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w2} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (varpi : (i : ι) → CommonPrimeCompletion (places i (tuple i)))
variable (Phi : (i : ι) → Set (ArithmeticTensorTupleBlock places tuple ≃ₗ[ℚ_[p]]
  ArithmeticTensorTupleBlock places tuple))

/-- The actual per-packet value V_a: david's ulPacketVOfWitness on the actual
tensor-core field product with the actual nonzero Kummer representative. -/
noncomputable def ucActualV (i : ι) : ℝ :=
  Mzk1ULPacketHull2Actual.ulPacketVOfWitness places tuple i (varpi i) (Phi i)

/-- The actual paper bound B_a: david's packetB with the actual exceptional set. -/
noncomputable def ucActualB (exceptional : Finset ι) (i : ι) : ℝ :=
  Mzk1ULPacketVActual.packetB places tuple i (varpi i) exceptional

/-- The actual pointwise C1 bound V_a <= B_a, from the accepted
ulPacketVOfWitness_le_paperBound.  This discharges the hpacket input of the
weighted C3 step at the actual packet. -/
theorem ucActualV_le_ucActualB (exceptional : Finset ι)
    (hvarpi : ∀ i, varpi i ≠ 0)
    (hPhi_ne : ∀ i, (Phi i).Nonempty)
    (hPhi : ∀ i, ∀ phi ∈ Phi i, ∀ u ∈ arithmeticTupleUnitLogLattice places tuple,
      phi u ∈ arithmeticTupleUnitLogLattice places tuple)
    (small_outside : ∀ i, i ∉ exceptional →
      logShellRamificationExponent
        (K := CommonPrimeCompletion (places i (tuple i))) (p := p) ≤ p - 2)
    (i : ι) :
    ucActualV places tuple varpi Phi i ≤ ucActualB places tuple varpi exceptional i :=
  Mzk1ULPacketHull2Actual.ulPacketVOfWitness_le_paperBound places tuple i (varpi i)
    (hvarpi i) (Phi i) (hPhi_ne i) (hPhi i) exceptional small_outside

end ActualPackets

/-! ## 4. Bridge to the U-L hpaper reduction (route 5.4 steps 3-4) -/

/-- The U-C weighted packet hull is literally U-L's Hpkt (the same weighted sum). -/
theorem ucWeightedHpkt_eq_ulHpkt {ι : Type*} [Fintype ι] (w V : ι → ℝ) :
    ucWeightedHpkt w V = Mzk1ULHpktActual.Hpkt w V := rfl

/-- C3 from the actual Step (viii) intermediate bound plus the U-L hpaper reduction
of route 5.4 items 3-4.  The left side is the actual weighted packet hull
sum_a w_a V_a; hprime and hconst are the two prime-count/constant inputs to be
bound to Section2's prime counting. -/
theorem uc_c3_of_stepVIII {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i)
    (l S_ar E_ar Q M d_mod lstar_logs : ℝ) (hl : 0 < l) (hE : 0 ≤ E_ar)
    (hprime : lstar_logs ≤ (4 / 3) * E_ar)
    (hconst : 2 * Real.log l + 56 ≤ (4 / 9) * E_ar)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        kappa l * ((1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 56
          - cL l * Q + (20 / 3) * lstar_logs) - M) :
    ucWeightedHpkt w V ≤
      kappa l * (Mzk1ULHpktActual.paperA d_mod l S_ar E_ar - cL l * Q) - M := by
  rw [ucWeightedHpkt_eq_ulHpkt]
  exact Mzk1ULHpktActual.ul_hpaper_assembled w V B hw hVB l S_ar E_ar Q M
    d_mod lstar_logs hl hE hprime hconst hstepVIII

#check uc_sandwich
#check uc_c3
#check uc_c4_from_weighted
#check ucActualV
#check ucActualB
#check ucActualV_le_ucActualB
#check ucWeightedHpkt_eq_ulHpkt
#check uc_c3_of_stepVIII

/-! ## 5. C3 assembled from the actual Section2 prime counting and paper constants -/

/-- **C3 with both §5.4.4 inputs discharged.**  The prime-count input comes from
the actual Section2 bound (via Mzk1UCC3ProducerActual.primeCounting_mul_log_le_four_thirds),
the constant input from the actual paper constants
(Mzk1ULHpktActual.ul_hpaper_assembled_paperConstants).  The remaining hypotheses
are the U-L Step (viii) intermediate bound, the actual lstar_logs form, and the
numeric comparison of the Section2 threshold with E_ar. -/
theorem uc_c3_of_primeCounting {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i)
    {eMod : Nat} (heM : 1 ≤ eMod)
    {η₀ : ℝ} (hη₀ : 0 < η₀)
    (hπ : ∀ η : ℝ, η₀ ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    (l eta_prm S_ar Q M d_mod x lstar_logs : ℝ)
    (hl : 5 ≤ l) (heta : 0 ≤ eta_prm) (hx : 1 ≤ x)
    (hxE : x ≤ Mzk1ULHpktActual.paperEar eMod l eta_prm)
    (hEta : η₀ ≤ Mzk1ULHpktActual.paperEar eMod l eta_prm)
    (hlstar : lstar_logs = (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        kappa l * ((1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 56
          - cL l * Q + (20 / 3) * lstar_logs) - M) :
    ucWeightedHpkt w V ≤
      kappa l * (Mzk1ULHpktActual.paperA d_mod l S_ar
        (Mzk1ULHpktActual.paperEar eMod l eta_prm) - cL l * Q) - M := by
  have hprime : lstar_logs ≤ (4 / 3) * Mzk1ULHpktActual.paperEar eMod l eta_prm := by
    rw [hlstar]
    exact Mzk1UCC3ProducerActual.primeCounting_mul_log_le_four_thirds hη₀ hπ hx hEta hxE
  rw [ucWeightedHpkt_eq_ulHpkt]
  exact Mzk1ULHpktActual.ul_hpaper_assembled_paperConstants w V B hw hVB heM
    l eta_prm S_ar Q M d_mod lstar_logs hl heta hprime hstepVIII

#print axioms uc_c3_of_primeCounting


/-! ## 6. Closing both §5.4.4 inputs with the actual paper constants -/

/-- The prime-count input hprime for the actual paper constants: with the Section2
threshold η₀ and η_prm ≥ η₀, the actual lstar_logs (π(⌊x⌋₊) log x at the actual
prime argument x = e*_mod l) is at most (4/3) E_ar. -/
theorem hprime_paperConstants {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod) {l : ℝ} (hl : 1 ≤ l) {eta_prm : ℝ} (heta : η0 ≤ eta_prm) :
    Mzk1ULHpktActual.paperLstarLogs eMod l ≤
      (4 / 3) * Mzk1ULHpktActual.paperEar eMod l eta_prm := by
  have heta0 : 0 ≤ eta_prm := le_trans hη0.le heta
  have hl0 : 0 ≤ l := le_trans zero_le_one hl
  have hx : 1 ≤ Mzk1ULHpktActual.paperPrimeArgument eMod l :=
    Mzk1ULHpktActual.paperPrimeArgument_ge_one he hl
  have hxE : Mzk1ULHpktActual.paperPrimeArgument eMod l ≤
      Mzk1ULHpktActual.paperEar eMod l eta_prm :=
    Mzk1ULHpktActual.paperPrimeArgument_le_Ear (eta_prm := eta_prm) heta0
  have hEta : η0 ≤ Mzk1ULHpktActual.paperEar eMod l eta_prm :=
    Mzk1ULHpktActual.paperEar_ge_of_le (l := l) (eta_prm := eta_prm) hl0 heta
  exact Mzk1UCC3ProducerActual.primeCounting_mul_log_le_four_thirds hη0 hπ hx hEta hxE

/-- **C3 with both §5.4.4 inputs closed.**  The prime-count input is
hprime_paperConstants (Section2 donor), the constant input is the paper-constant
producer of Mzk1ULHpktActual.  The only remaining hypothesis is the actual
Step (viii) intermediate inequality. -/
theorem uc_c3_paperConstants {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (l eta_prm S_ar Q M d_mod : ℝ) (hl : 5 ≤ l) (heta : η0 ≤ eta_prm)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        kappa l * ((1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 56
          - cL l * Q + (20 / 3) * Mzk1ULHpktActual.paperLstarLogs eMod l) - M) :
    ucWeightedHpkt w V ≤
      kappa l * (Mzk1ULHpktActual.paperA d_mod l S_ar
        (Mzk1ULHpktActual.paperEar eMod l eta_prm) - cL l * Q) - M := by
  have hl1 : 1 ≤ l := le_trans (by norm_num) hl
  have heta0 : 0 ≤ eta_prm := le_trans hη0.le heta
  have hprime := hprime_paperConstants hη0 hπ he hl1 heta
  rw [ucWeightedHpkt_eq_ulHpkt]
  exact Mzk1ULHpktActual.ul_hpaper_assembled_paperConstants w V B hw hVB he
    l eta_prm S_ar Q M d_mod (Mzk1ULHpktActual.paperLstarLogs eMod l) hl heta0
    hprime hstepVIII

#print axioms hprime_paperConstants
#print axioms uc_c3_paperConstants


/-- kappa l = (l+1)/4 is positive for positive l. -/
theorem kappa_pos {l : ℝ} (hl : 0 < l) : 0 < kappa l := by
  unfold kappa
  linarith

/-- **U-C C4 with both §5.4.4 inputs closed.**  The P5 lower bound -M <= theta_P5,
the U-R reading bound theta_P5 <= H_pkt, the actual C3 (uc_c3_paperConstants) and
the accepted UCC3 algebra give C4 = hCor312.  The only non-U-C inputs are the P5
lower bound (-M <= theta) and the actual Step (viii) intermediate inequality. -/
theorem uc_c4_of_paperConstants {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (l eta_prm S_ar Q M d_mod theta : ℝ) (hl : 5 ≤ l) (heta : η0 ≤ eta_prm)
    (hP5 : -M ≤ theta) (htheta : theta ≤ ucWeightedHpkt w V)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        kappa l * ((1 + 12 * d_mod / l) * S_ar + 2 * Real.log l + 56
          - cL l * Q + (20 / 3) * Mzk1ULHpktActual.paperLstarLogs eMod l) - M) :
    cL l * Q ≤ Mzk1ULHpktActual.paperA d_mod l S_ar
      (Mzk1ULHpktActual.paperEar eMod l eta_prm) :=
  uc_sandwich (kappa_pos (l := l) (by linarith)) hP5 htheta
    (uc_c3_paperConstants w V B hw hVB hη0 hπ he l eta_prm S_ar Q M d_mod hl heta hstepVIII)


/-! ## 7. U-C C4 grounded in the accepted P5 lower bound -/

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual

/-- U-C C4 grounded in the accepted P5 lower bound.  The P5 lower bound
-M <= actualThetaHullLogRoot is the accepted Mzk1P6HThetaNormalization2
(p6_neg_M_le_HTheta2); the reading bound actualThetaHullLogRoot <= H_pkt is the
U-R producer (kurt); the C3 upper is uc_c3_paperConstants.  The only remaining
non-U-C input is the actual Step (viii) intermediate inequality. -/
theorem uc_c4_paperConstants_of_p6 {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (eta_prm S_ar Q d_mod : ℝ) (hl : 5 ≤ (l.value : ℝ)) (heta : η0 ≤ eta_prm)
    (htheta : actualThetaHullLogRoot (l := l) T ≤ ucWeightedHpkt w V)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        kappa (l.value : ℝ) * ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar
          + 2 * Real.log (l.value : ℝ) + 56
          - cL (l.value : ℝ) * Q
          + (20 / 3) * Mzk1ULHpktActual.paperLstarLogs eMod (l.value : ℝ))
          - actualQPilotMagnitudeClassical (l := l) T) :
    cL (l.value : ℝ) * Q ≤ Mzk1ULHpktActual.paperA d_mod (l.value : ℝ) S_ar
      (Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) eta_prm) :=
  uc_c4_of_paperConstants w V B hw hVB hη0 hπ he (l.value : ℝ) eta_prm S_ar Q
    (actualQPilotMagnitudeClassical (l := l) T) d_mod (actualThetaHullLogRoot (l := l) T)
    hl heta
    (LeanFormal.IUT.XiFPaper.P6HThetaNormalization2Actual.p6_neg_M_le_HTheta2 (l := l) T)
    htheta hstepVIII

#print axioms uc_c4_paperConstants_of_p6

end LeanFormal.IUT.XiFPaper.Mzk1UCHpktActual
end