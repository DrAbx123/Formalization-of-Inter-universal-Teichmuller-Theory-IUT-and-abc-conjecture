import tmp.sheaf.xif.paper.S2092PaperOtriActual
import tmp.sheaf.xif.paper.S2040S2057InterfaceActual
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient

/-! # S2040: paper O^tri carrier / q_v / O^× / O^×μ from S2092

Fills the paper O^tri attachment carrier, q_v, O^× and the **torsion quotient**
`O^×μ = paperOUnits / torsion` from S2092's actual paper objects.  The roots of
unity `paperOUnitsMu = rootsOfUnity (2l)` of S2092 are *not* used as O^×μ; they
are recorded separately as the `2l`-root indeterminacy subgroup and proved to lie
in the torsion kernel of the quotient map.  The completion root is the remaining
Prop obligation. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2040PaperOtriFromS2092Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2092PaperOtriActual
open LeanFormal.IUT.XiFPaper.S2040S2057InterfaceActual
open LeanFormal.IUT.XiFPaper.S2040RootStackThetaPilotActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The paper `O^×μ`: the actual unit group modulo its full torsion subgroup
(TimesMuQuotient), not the roots-of-unity subgroup. -/
abbrev s2040PaperOUnitsMu : Type :=
  TimesMuQuotient (paperOUnits T b)

/-- The quotient map `O^× → O^×μ`. -/
noncomputable def s2040PaperOUnitsMuMap :
    paperOUnits T b →* s2040PaperOUnitsMu T b :=
  TimesMuQuotient.quotientMap

theorem s2040PaperOUnitsMuMap_ker :
    MonoidHom.ker (s2040PaperOUnitsMuMap T b) =
      CommGroup.torsion (paperOUnits T b) :=
  TimesMuQuotient.quotientMap_ker

theorem s2040PaperOUnitsMuMap_surjective :
    Function.Surjective (s2040PaperOUnitsMuMap T b) :=
  TimesMuQuotient.quotientMap_surjective

/-- S2092's roots of unity `μ_{2l}` are contained in the torsion kernel; they are
NOT the quotient itself. -/
theorem s2040PaperMu2L_mem_torsion (ζ : paperOUnitsMu T b) :
    (ζ : paperOUnits T b) ∈ CommGroup.torsion (paperOUnits T b) := by
  rw [CommGroup.mem_torsion]
  exact isOfFinOrder_iff_pow_eq_one.mpr
    ⟨2 * l.value, twoL_pos l, paperOUnitsMu_pow T b ζ⟩

theorem s2040PaperMu2L_quotient_trivial (ζ : paperOUnitsMu T b) :
    s2040PaperOUnitsMuMap T b (ζ : paperOUnits T b) = 1 := by
  rw [s2040PaperOUnitsMuMap, TimesMuQuotient.quotientMap_apply]
  exact (QuotientGroup.eq_one_iff _).mpr (s2040PaperMu2L_mem_torsion T b ζ)

/-- Exact missing Galois action on the paper O^×.  The quotient action is
constructed below from any such action.  No inhabitant is asserted. -/
structure S2040PaperOUnitsGaloisActionRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  G : Type u
  [groupG : Group G]
  action : G →* MulAut (paperOUnits T b)

/-- Once a Galois action on `O^×` is supplied, TimesMuQuotient gives the
descended action on `O^×μ`, compatible with the quotient map. -/
noncomputable def s2040PaperOUnitsMuActionOfGalois
    {G : Type u} [Group G]
    (action : G →* MulAut (paperOUnits T b)) :
    G →* MulAut (s2040PaperOUnitsMu T b) :=
  TimesMuQuotient.action action

theorem s2040PaperOUnitsMuActionOfGalois_quotientMap
    {G : Type u} [Group G]
    (action : G →* MulAut (paperOUnits T b))
    (g : G) (u : paperOUnits T b) :
    s2040PaperOUnitsMuActionOfGalois T b action g
        (s2040PaperOUnitsMuMap T b u) =
      s2040PaperOUnitsMuMap T b (action g u) :=
  TimesMuQuotient.action_quotientMap action g u

/-- The paper O^tri/q_v/O^×/O^×μ attachment is actual; `O^×μ` is the actual
torsion quotient.  Only the completion 2l-th root `paperOtriRootMissing` remains
as the Prop obligation. -/
noncomputable def s2040PaperOtriAttachmentActual :
    S2040PaperOtriAttachmentRequired (l := l) T b where
  Otri := paperOtri (l := l) T b
  qv := paperQV (l := l) T b
  OUnits := paperOUnits (l := l) T b
  OUnitsMu := s2040PaperOUnitsMu (l := l) T b
  qv_root_attachment := paperOtriRootMissing (l := l) T b
  OUnitsMu_attachment :=
    (MonoidHom.ker (s2040PaperOUnitsMuMap (l := l) T b) =
        CommGroup.torsion (paperOUnits (l := l) T b)) ∧
      Function.Surjective (s2040PaperOUnitsMuMap (l := l) T b) ∧
        ∀ ζ : paperOUnitsMu (l := l) T b,
          s2040PaperOUnitsMuMap (l := l) T b (ζ : paperOUnits (l := l) T b) = 1
  norm_law := ‖(paperQV (l := l) T b : paperKv (l := l) T b)‖ < 1

theorem s2040PaperOtriAttachmentActual_OUnitsMu_attachment :
    (s2040PaperOtriAttachmentActual T b).OUnitsMu_attachment := by
  exact ⟨s2040PaperOUnitsMuMap_ker T b,
    s2040PaperOUnitsMuMap_surjective T b,
    s2040PaperMu2L_quotient_trivial T b⟩

theorem s2040PaperOtriAttachmentActual_norm_law :
    (s2040PaperOtriAttachmentActual T b).norm_law :=
  paperQV_norm_lt_one (l := l) T b

/-- The only remaining paper root datum is S1413's completion 2l-th root. -/
theorem s2040PaperOtriAttachment_root_required :
    (s2040PaperOtriAttachmentActual T b).qv_root_attachment =
      paperOtriRootMissing (l := l) T b := rfl

#check s2040PaperOUnitsMu
#check s2040PaperOUnitsMuMap
#check s2040PaperOUnitsMuMap_ker
#check s2040PaperOUnitsMuMap_surjective
#check s2040PaperMu2L_quotient_trivial
#check S2040PaperOUnitsGaloisActionRequired
#check s2040PaperOUnitsMuActionOfGalois
#check s2040PaperOtriAttachmentActual
#check s2040PaperOtriAttachmentActual_OUnitsMu_attachment

end LeanFormal.IUT.XiFPaper.S2040PaperOtriFromS2092Actual
end
