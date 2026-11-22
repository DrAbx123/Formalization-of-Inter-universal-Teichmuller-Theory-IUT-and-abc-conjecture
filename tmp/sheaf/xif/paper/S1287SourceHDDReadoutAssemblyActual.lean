import tmp.sheaf.xif.paper.S1262HDDLocalLatticeActual
import tmp.sheaf.xif.paper.S1275SHEDDNonLatticeFieldsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1287SourceHDDReadoutAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1262HDDLocalLatticeActual
open LeanFormal.IUT.XiFPaper.S1275SHEDDNonLatticeFieldsActual

universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable (I : Input Label Choice)

/-- Actual HDD local lattice from S1262. -/
noncomputable def s1287HDDLocalLattice :
    S1215HDDLocalLattice (I := I) :=
  s1262HDDLocalLattice (I := I)

/-- Actual SHE localization from S1275. -/
noncomputable def s1287SHELocalization :
    SourceLocalizationExpression oneColumnStructure (Theorem311Output I) :=
  s1275SHELocalization (I := I)

/-- Actual SHE output/readout donor from actualSHEOutput. -/
noncomputable def s1287SHEOutput : SHEOutputActual I :=
  actualSHEOutput I

/-- Actual reading/readout map from actualSHEOutput. -/
noncomputable def s1287Readout (v : NumberField.FinitePlace ℚ)
    (o : Theorem311Output I) : (oneColumnStructure).localRing v :=
  (actualSHEOutput I).readingMap v o

/-- Assembled actual fields available for SourceHDDReadout: HDD local lattice,
SHE localization, SHE output, and the actual readout map. -/
structure S1287ActualHDDReadoutFields where
  hddLocalLattice : S1215HDDLocalLattice (I := I)
  sheLocalization :
    SourceLocalizationExpression oneColumnStructure (Theorem311Output I)
  sheOutput : SHEOutputActual I
  readout : ∀ v : NumberField.FinitePlace ℚ, Theorem311Output I →
    (oneColumnStructure).localRing v

noncomputable def s1287ActualHDDReadoutFields :
    S1287ActualHDDReadoutFields (I := I) where
  hddLocalLattice := s1287HDDLocalLattice (I := I)
  sheLocalization := s1287SHELocalization (I := I)
  sheOutput := s1287SHEOutput (I := I)
  readout := s1287Readout (I := I)

@[simp] theorem s1287ActualHDDReadoutFields_hddLocalLattice :
    (s1287ActualHDDReadoutFields (I := I)).hddLocalLattice =
      s1262HDDLocalLattice (I := I) := rfl

@[simp] theorem s1287ActualHDDReadoutFields_sheLocalization :
    (s1287ActualHDDReadoutFields (I := I)).sheLocalization =
      s1275SHELocalization (I := I) := rfl

@[simp] theorem s1287ActualHDDReadoutFields_sheOutput :
    (s1287ActualHDDReadoutFields (I := I)).sheOutput =
      actualSHEOutput I := rfl

@[simp] theorem s1287ActualHDDReadoutFields_readout
    (v : NumberField.FinitePlace ℚ) (o : Theorem311Output I) :
    (s1287ActualHDDReadoutFields (I := I)).readout v o =
      (actualSHEOutput I).readingMap v o := rfl

end LeanFormal.IUT.XiFPaper.S1287SourceHDDReadoutAssemblyActual

end
