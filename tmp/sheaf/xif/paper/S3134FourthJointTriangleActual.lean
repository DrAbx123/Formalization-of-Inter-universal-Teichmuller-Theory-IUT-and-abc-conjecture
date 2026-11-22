import tmp.sheaf.xif.paper.S3134FourthJointQThetaActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource

/-!
# S3134: the fourth-triangle packet `(hull+det)∘(dsc)SHE + IPL`

IUT III, Corollary 3.12, Steps (xi-b)--(xi-f) (corpus `Inter-universal
Teichmuller Theory III.txt:10823-10899`); the (IPL) property of Remark
3.11.1, (iii) (pagewise `:9843-9907`); the reduced IPL factorization with its
paper attribution at `:9947-9982`.  The fourth triangle combines

* the composite arrow `(hull+det) ∘ (dsc)SHE` of
  `S3134FourthJointCompositeActual`, evaluated at the actual SHE output
  object;
* the actual IPL composite/link data of the 1-column log-theta-lattice
  (constructed from the actual source strip links and the actual conjugated
  Kummer/evaluation layers in `LogKummerCorrespondenceFromSource`);
* the two actual real readouts entering the simultaneous q/Theta comparison
  (`S3134QParameter` and the paper's signed target
  `S3134ThetaHullLogVolumeSigned` = `-|log(Theta)|`).

The packet is genuine data: the composite-field equation, the IPL
factorization `inputLink = composite`, the q-parameter identification, and the
Theta-target identification are all proved from actual data.  The only
remaining input is the exact `S3134QThetaComparisonGap` of the simultaneous
comparison, from which the paper's `Cor312ComparisonData` and the bound
`C_Theta >= -1` are derived.  No sorry, axiom, `True`, `PUnit`, or toy
carrier is used.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1300HDDHullDetActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointCompositeActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource

namespace LeanFormal.IUT.XiFPaper.S3134FourthJointTriangleActual

universe u v uv ua upi umon ui

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)
variable {l : PrimeGeFive} {V : Type uv}
variable (J : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The fourth-triangle packet: the actual composite arrow
`(hull+det)∘(dsc)SHE`, the actual IPL composite of the 1-column
log-theta-lattice, and the two actual real readouts entering the simultaneous
q/Theta comparison. -/
structure S3134FourthJointTriangle
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) where
  /-- The composite arrow `(hull+det)∘(dsc)SHE` at each place. -/
  composite : ∀ v : NumberField.FinitePlace ℚ,
    (oneColumnStructure).localRing v ×
      Set (Fin D.rank → (oneColumnStructure).localField v)
  /-- The composite is the actual fourth-joint composite of the two arrows. -/
  composite_eq : composite = fun v =>
    S3134FourthJointComposite (I := I) (J := J) D C v
  /-- The actual q-parameter read off the 1-column theta packet. -/
  qParameter : ℝ
  qParameter_eq : qParameter = S3134QParameter J
  /-- The paper's signed Theta-side target `-|log(Theta)|`. -/
  thetaHullLogVolume : ℝ
  thetaHullLogVolume_eq : thetaHullLogVolume = S3134ThetaHullLogVolumeSigned (I := I) D
  /-- The actual IPL composite/link data of the 1-column log-theta-lattice. -/
  ipl : IPLActual (G := ActualKummerGroup (I := J))
    (J.fPrimeStripAt 1 0) (J.fPrimeStripAt 1 1) (J.fPrimeStripAt 1 0)
    (J.fPrimeStripAt 0 0) (J.fPrimeStripAt 1 0)

/-- Construction of the fourth-triangle packet from the actual fourth-joint
components, the actual IPL data, and the exact missing comparison input. -/
noncomputable def S3134FourthJointTriangle_ofActuals
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    S3134FourthJointTriangle (I := I) (J := J) D C where
  composite := fun v => S3134FourthJointComposite (I := I) (J := J) D C v
  composite_eq := rfl
  qParameter := S3134QParameter J
  qParameter_eq := rfl
  thetaHullLogVolume := S3134ThetaHullLogVolumeSigned (I := I) D
  thetaHullLogVolume_eq := rfl
  ipl := actualIPLData (I := J)

/-- The packet's composite field is the actual fourth-joint composite. -/
@[simp] theorem S3134FourthJointTriangle_composite
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (v : NumberField.FinitePlace ℚ) :
    (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).composite v =
      S3134FourthJointComposite (I := I) (J := J) D C v :=
  rfl

/-- The packet's q readout is the actual q-parameter. -/
@[simp] theorem S3134FourthJointTriangle_qParameter
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).qParameter =
      S3134QParameter J :=
  rfl

/-- The packet's Theta readout is the paper's signed hull+det log-volume
readout. -/
@[simp] theorem S3134FourthJointTriangle_thetaHullLogVolume
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).thetaHullLogVolume =
      S3134ThetaHullLogVolumeSigned (I := I) D :=
  rfl

/-- The IPL field of the packet satisfies the frozen IPL factorization: the
linking isomorphism equals the composite of the actual Kummer/evaluation
arrows. -/
theorem S3134FourthJointTriangle_ipl_inputLink_eq_composite
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).ipl.inputLink =
      (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).ipl.composite :=
  (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).ipl.inputLink_eq_composite

/-- The IPL input link of the packet is an actual strip equivalence landing on
the q-pilot strip of the 1-column. -/
def S3134FourthJointTriangle_ipl_inputLink_type
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J)) :
    FPrimeStripEquiv (J.fPrimeStripAt 1 0) (J.fPrimeStripAt 1 0) :=
  (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).ipl.inputLink

/-- The simultaneous comparison of the fourth triangle, conditional on exactly
the named comparison gap: the actual q-side log-volume lies in the ray
`R_{<= -|log(Theta)|}` of the actual hull+det readout. -/
theorem S3134FourthJointTriangle_simultaneousComparison
    (D : S1300HDDHullDetSource I)
    (C : SourceSHEHDDCompatibility (I := I) (J := J))
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    (-|Real.log (S3134QParameter J)|) ∈
      hullLogVolumeRay
        (S3134FourthJointTriangle_ofActuals (I := I) (J := J) D C).thetaHullLogVolume :=
  G.simultaneous_comparison

/-- The paper's `Cor312ComparisonData` constructed from the fourth-triangle
packet and the named gap. -/
noncomputable def S3134FourthJointTriangle_comparisonData
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D) :
    Cor312ComparisonData :=
  S3134QThetaComparisonData (I := I) (J := J) D G

/-- The final arithmetic step of Corollary 3.12 for the fourth-triangle packet:
given the linear comparison of the actual packet target with
`C_Theta * |log(q)|`, conclude `C_Theta >= -1`. -/
theorem S3134FourthJointTriangle_final
    (D : S1300HDDHullDetSource I)
    (G : S3134QThetaComparisonGap (I := I) (J := J) D)
    {cTheta : ℝ}
    (hc : S3134ThetaHullLogVolumeSigned (I := I) D ≤
      cTheta * |Real.log (S3134QParameter J)|) :
    -1 ≤ cTheta :=
  S3134QThetaComparison_final (I := I) (J := J) D G hc

/-- Coherence of the IPL slot with the q-side readout of the fourth triangle:
the IPL q-pilot strip `J.fPrimeStripAt 1 0` is the F-prime-strip of the actual
`(1,0)` theater, and the actual q-parameter is the q of that theater's theta
packet.  Both are the same `(1,0)` column of the same qualified theta-link
data (definitional identifications, not identifications of arbitrary data). -/
theorem S3134FourthJointIPLQPilotStrip_coherence :
    J.fPrimeStripAt 1 0 = (J.theaterAt 1 0).primeStrip ∧
      S3134QParameter J = (J.theaterAt 1 0).thetaPacket.q :=
  ⟨rfl, S3134QParameter_eq_theaterQ (J := J)⟩

#check S3134FourthJointTriangle
#check S3134FourthJointTriangle_ofActuals
#check S3134FourthJointIPLQPilotStrip_coherence
#check S3134FourthJointTriangle_ipl_inputLink_eq_composite
#check S3134FourthJointTriangle_simultaneousComparison
#check S3134FourthJointTriangle_comparisonData
#check S3134FourthJointTriangle_final

end LeanFormal.IUT.XiFPaper.S3134FourthJointTriangleActual
