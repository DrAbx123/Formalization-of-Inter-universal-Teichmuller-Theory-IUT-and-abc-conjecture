import tmp.sheaf.lana_latest.Iut.HodgeTheater.HodgeTheater
import tmp.sheaf.gogopex.Iut.Foundations.QualitativeData

/-! Mainline (A515-2): the Theorem 3.11 Hodge-theater objects from the real LANA-latest
`Iut.HodgeTheater.HodgeTheater` module (IUT I, Definitions 6.11/6.13, Remark 6.12.2): the
`D-Θ^{±ell}NF` label layer with `Iso ≃ ℤˣ` and `card_iso = 2`, its `ΘNF`-bridge
`toThetaNF`, the processions, the `Θ^{±ell}NF` Hodge theaters `ThetaPmEllNFHT D` with the
lift-surjectivity `toLabels_surjective`, `nonempty_iso`, and the theater `ofData D` built from
initial Θ-data.  Also the link to Gogopex qualitative Hodge-theater identifiers. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311HodgeTheaterActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! ## 1. The `D-Θ^{±ell}NF` label layer -/

section LabelLayer

variable {ℓ : ℕ} [OddPrime ℓ] {V : Type}

/-- **Theorem 3.11 object**: the `D-Θ^{±ell}NF`-Hodge theater label layer (IUT I,
  Definition 6.13(ii)). -/
abbrev Thm311DThetaPmEllNFHT := Iut.HodgeTheater.DThetaPmEllNFHT ℓ V

/-- The underlying `D-ΘNF`-Hodge theater (IUT I, Definition 6.13(i); LANA real def). -/
def thm311ToThetaNF (A : Thm311DThetaPmEllNFHT (ℓ := ℓ) (V := V)) :
    Iut.HodgeTheater.DThetaNFHT ℓ :=
  Iut.HodgeTheater.DThetaPmEllNFHT.toThetaNF A

/-- **The label-layer automorphism group is `±1`** (IUT I, Remark 6.12.2(ii); LANA real
  theorem `isoEquiv`). -/
def thm311LabelIsoEquiv (A B : Thm311DThetaPmEllNFHT (ℓ := ℓ) (V := V)) :
    A.Iso B ≃ ℤˣ :=
  Iut.HodgeTheater.DThetaPmEllNFHT.isoEquiv A B

/-- **`card_iso = 2`**: any two `D-Θ^{±ell}NF` label layers have exactly two isomorphisms
  (LANA real theorem). -/
theorem thm311Label_card_iso (A B : Thm311DThetaPmEllNFHT (ℓ := ℓ) (V := V)) :
    Nat.card (A.Iso B) = 2 :=
  Iut.HodgeTheater.DThetaPmEllNFHT.card_iso A B

/-- The model label layer (LANA real def `model`). -/
def thm311LabelModel : Thm311DThetaPmEllNFHT (ℓ := ℓ) (V := V) :=
  Iut.HodgeTheater.DThetaPmEllNFHT.model (ℓ := ℓ) (V := V)

end LabelLayer

/-! ## 2. The `Θ^{±ell}NF` Hodge theater of initial Θ-data -/

section ThetaHodgeTheater

variable (D : Iut.InitialThetaData.{0})

/-- **Theorem 3.11 object**: the full `Θ^{±ell}NF`-Hodge theater relative to initial
  Θ-data `D`, with the attached prime-strips and global Frobenioids (IUT I,
  Definition 6.13(i)). -/
abbrev Thm311ThetaPmEllNFHT := Iut.HodgeTheater.ThetaPmEllNFHT D

/-- **Every isomorphism of the `D-Θ^{±ell}NF` label layers lifts** to the full theaters
  (surjectivity half of IUT I, Corollaries 5.6(ii), 6.12(i); LANA real theorem
  `toLabels_surjective`). -/
theorem thm311_toLabels_surjective (A B : Thm311ThetaPmEllNFHT D) :
    Function.Surjective (fun f : A.Iso B => f.labels) :=
  Iut.HodgeTheater.ThetaPmEllNFHT.toLabels_surjective A B

/-- Any two `Θ^{±ell}NF` Hodge theaters over the same initial Θ-data are isomorphic
  (LANA real theorem `nonempty_iso`). -/
theorem thm311_thetaTheater_nonempty_iso (A B : Thm311ThetaPmEllNFHT D) :
    Nonempty (A.Iso B) :=
  Iut.HodgeTheater.ThetaPmEllNFHT.nonempty_iso A B

/-- The Hodge theater built from initial Θ-data (LANA real def `ofData`): the models of
  IUT I Examples 4.3, 4.4, 6.2, 6.3 and the tautological prime-strips. -/
def thm311_thetaTheaterOfData : Thm311ThetaPmEllNFHT D :=
  Iut.HodgeTheater.ThetaPmEllNFHT.ofData D

/-- The `±`-label procession of the `D-Θ^{±ell}NF` layer (LANA real def `procPm`). -/
def thm311_labelProcPm (A : Iut.HodgeTheater.DThetaPmEllNFHT ℓ V) :
    Iut.Procession (AbsFl ℓ) :=
  Iut.HodgeTheater.DThetaPmEllNFHT.procPm A

end ThetaHodgeTheater

/-! ## 3. Bookkeeping link to Gogopex `QualitativeData` -/

open Iut.RealLineCopy.QualitativeData

/-- The qualitative Hodge-theater identifier of the domain side. -/
def domainTheaterQualitativeId : HodgeTheaterId where
  side := HodgeTheaterSide.domain
  label := "D-Θ±ellNF (domain)"

/-- The qualitative Hodge-theater identifier of the codomain side. -/
def codomainTheaterQualitativeId : HodgeTheaterId where
  side := HodgeTheaterSide.codomain
  label := "D-Θ±ellNF (codomain)"

/-- The qualitative holomorphic-structure record attached to the Θ-link (Bookkeeping only;
  the mathematical Θ-link data is the LANA `HodgeTheater`/`FRlf` machinery). -/
def thetaLinkHolomorphicStructure : HolomorphicStructure where
  theater := domainTheaterQualitativeId
  structureLabel := "arithmetic holomorphic structure at (0,0)"

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311HodgeTheaterActual