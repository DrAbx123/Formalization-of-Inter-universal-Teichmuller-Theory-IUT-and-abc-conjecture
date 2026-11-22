import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual
import tmp.sheaf.gogopex.Iut.Foundations.QualitativeData
import tmp.sheaf.gogopex.Iut.Foundations.TransportedRegionFamily
import tmp.sheaf.xif.paper.Mzk1HullDetStep3115Actual

/-! Mainline (A516-2): Theorem 3.11 indeterminacies (Ind1/2/3) and the hull+det / SHE-IPL-APT
objects, referenced from real sources: LANA-latest `Multiradial/Spec.lean` (Ind2-group,
`IsmFamily`, `Ind2Group.single`, `UpperSemi`/`UpperSemiCompatible`/`ind3Possible`,
`sUnion_ind3Possible`), our real hull lane `Mzk1HullDetStep3115Actual` (hull/det readouts and
the det-normalized Step (xi-f) comparison), and Gogopex `QualitativeData` (structured
IPL/SHE/APT certificate and its real projection theorems). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311IndHullActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! ## 1. (Ind2): independent copies of the local indeterminacy groups -/

section Ind2

variable {lstar : ℕ} {V : Type*} [DecidableEq V] {Ism : V → Type*} [∀ v, Group (Ism v)]

/-- **O4 (Ind2)-group**: independent copies of `Ism v` for `j ≤ ℓ*`, `i ≤ j`, `v ∈ V`
  (IUT III, Theorem 3.11(i)). -/
abbrev Thm311Ind2Group := Iut.Multiradial.Ind2Group lstar V Ism

/-- A single copy of `Ism v` inside the (Ind2)-group. -/
def thm311Ind2Single (j : Fin (lstar + 1)) (i : Fin (j + 1)) (v : V) (g : Ism v) :
    Thm311Ind2Group (lstar := lstar) (V := V) (Ism := Ism) :=
  Iut.Multiradial.Ind2Group.single j i v g

/-- The single copy acts as `g` on its own summand (LANA real lemma). -/
theorem thm311Ind2Single_apply_self (j : Fin (lstar + 1)) (i : Fin (j + 1)) (v : V)
    (g : Ism v) :
    thm311Ind2Single (lstar := lstar) (V := V) (Ism := Ism) j i v g j i v = g :=
  Iut.Multiradial.Ind2Group.single_apply_self j i v g

end Ind2

/-- **O4 (Ind3): upper semi-compatibility** of a region with the coric region (IUT III,
  Proposition 3.5(ii); Theorem 3.11(ii)). -/
abbrev Thm311UpperSemi {X : Type*} (R S : Set X) : Prop :=
  Iut.Multiradial.UpperSemi R S

/-- A vertical family of regions is upper semi-compatible with `R`. -/
abbrev Thm311UpperSemiCompatible {X : Type*} (img : ℤ → Set X) (R : Set X) : Prop :=
  Iut.Multiradial.UpperSemiCompatible img R

/-- **A region modulo (Ind3)**: `R` stands for every upper semi-compatible region. -/
abbrev Thm311Ind3Possible {X : Type*} (R : Set X) : Set (Set X) :=
  Iut.Multiradial.ind3Possible R

/-- **(Ind3) does not enlarge the union of possible images** (LANA real theorem). -/
theorem thm311_sUnion_ind3Possible {X : Type*} (R : Set X) :
    ⋃₀ Thm311Ind3Possible R = R :=
  Iut.Multiradial.sUnion_ind3Possible R

/-- Upper semi-compatibility is transitive (LANA real lemma). -/
theorem thm311_upperSemi_trans {X : Type*} {R S T : Set X}
    (h₁ : Thm311UpperSemi R S) (h₂ : Thm311UpperSemi S T) :
    Thm311UpperSemi R T :=
  Iut.Multiradial.UpperSemi.trans h₁ h₂

/-! ## 2. hull + det readouts and the det-normalized Step (xi-f) comparison -/

section HullDet

variable {label : Type} [Fintype label] [DecidableEq label]

/-- **O7/O8 object**: the hull/det state of the hull lane (positive packet + q-parameter). -/
abbrev Thm311HullDetState :=
  LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.HullDetState label

/-- The hull readout `log(packetDet)`. -/
def thm311HullReadout (x : Thm311HullDetState (label := label)) : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.hullReadout x

/-- The det readout `-log|q|`. -/
def thm311DetReadout (x : Thm311HullDetState (label := label)) : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.detReadout x

/-- **Step (xi-f) comparison criterion**: `hullReadout ≤ detReadout` iff `packetDet·q ≤ 1`
  (our real hull-lane theorem). -/
theorem thm311_hull_le_det_iff (x : Thm311HullDetState (label := label)) :
    thm311HullReadout x ≤ thm311DetReadout x ↔
      LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.packetDet x.packet * x.q ≤ 1 :=
  LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.hullReadout_le_detReadout_iff x

/-- **Step (xi-f) comparison, proved**: from `packetDet·q ≤ 1` we get
  `hullReadout ≤ detReadout` (our real hull-lane theorem). -/
theorem thm311_step3115_comparison (x : Thm311HullDetState (label := label))
    (h : LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.packetDet x.packet * x.q ≤ 1) :
    thm311HullReadout x ≤ thm311DetReadout x :=
  LeanFormal.IUT.XiFPaper.Mzk1HullDetStep3115Actual.step3115_comparison_hullDet x h

end HullDet

/-! ## 3. SHE / IPL / APT (structured qualitative certificate) -/

section Qualitative

open Iut.RealLineCopy
open Iut.RealLineCopy.QualitativeData

variable {source target : Copy} {index : Type*}
variable (family : TransportedRegionFamily source target index)
variable (cert : StructuredCertificate family)

/-- **O11/O2 (IPL)**: the structured input-prime-strip-link datum of the certificate
  (Gogopex real theorem `StructuredCertificate.hasStructuredIPL`). -/
theorem thm311_hasStructuredIPL : HasStructuredIPL family :=
  StructuredCertificate.hasStructuredIPL cert

/-- **O11 (SHE)**: simultaneous holomorphic expressibility of the certificate
  (Gogopex real theorem `StructuredCertificate.hasStructuredSHE`). -/
theorem thm311_hasStructuredSHE : HasStructuredSHE family :=
  StructuredCertificate.hasStructuredSHE cert

/-- **O2 (APT)**: algorithmic parallel transport of the certificate (Gogopex real theorem
  `StructuredCertificate.hasStructuredAPT`). -/
theorem thm311_hasStructuredAPT : HasStructuredAPT family :=
  StructuredCertificate.hasStructuredAPT cert

end Qualitative

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311IndHullActual