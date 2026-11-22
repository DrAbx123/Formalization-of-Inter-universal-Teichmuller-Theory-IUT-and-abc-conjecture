import tmp.sheaf.xif.paper.S2089FiniteAbelianSubextensionActual
import tmp.sheaf.xif.paper.S2027LocalArtinActual

-- S2046 M2 port: PadicField.artin through S2089 galoisGroupEquiv and
-- S2027 galoisGroupMaximalAbelian to the topological abelianization.
-- The torsion equivalence itself remains exact missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046M2S2089Port

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual

variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p)

/-- PadicField.artin for the local field of U. -/
noncomputable def S2046ArtinToMaxAbelian :
    (localField p U)ˣ →*
      Gal(↥(PadicField.maxAbelian (localField p U) (AlgebraicClosure ℚ_[p])) /
        localField p U) :=
  PadicField.artin (p := p) (K := localField p U)
    (Ω := AlgebraicClosure ℚ_[p])

/-- The Artin map transported through S2089's Galois-group equivalence. -/
noncomputable def S2046ArtinToMaximalAbelian :
    (localField p U)ˣ →*
      Gal(↥(maximalAbelianExtension p U) / localField p U) :=
  (galoisGroupEquiv U).toMonoidHom.comp (S2046ArtinToMaxAbelian U)

/-- The Artin map on S2027's topological abelianization carrier. -/
noncomputable def S2046ArtinToTopological :
    (localField p U)ˣ →*
      TopologicalAbelianization (localGaloisGroup p U) :=
  ((galoisGroupMaximalAbelian p U).symm.toMonoidHom).comp
    (S2046ArtinToMaximalAbelian U)

/-- Exact M2a torsion statement on the topological abelianization. -/
abbrev S2046M2TorsionRequired : Type :=
  mu p U ≃* CommGroup.torsion
    (TopologicalAbelianization (localGaloisGroup p U))

/-- Exact M2c carrier comparison statement. -/
abbrev S2046M2CarrierRequired : Type :=
  CommGroup.torsion (Abelianization ↥U) ≃*
    CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U))

/-- Conditional M2 source datum from the two exact missing inputs. -/
noncomputable def S2046LocalArtinSourceDataOf
    (hartin : ∀ U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p,
      S2046M2TorsionRequired (p := p) U)
    (hcarrier : ∀ U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p,
      S2046M2CarrierRequired (p := p) U) :
    LocalArtinSourceData p where
  artin := hartin
  carrier := hcarrier

theorem S2046M2_sufficient
    (hartin : ∀ U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p,
      S2046M2TorsionRequired (p := p) U)
    (hcarrier : ∀ U : LeanFormal.IUT.XiFPaper.S2017VerlagerungActual.Index p,
      S2046M2CarrierRequired (p := p) U) :
    Nonempty (LocalArtinSourceData p) :=
  ⟨S2046LocalArtinSourceDataOf (p := p) hartin hcarrier⟩

#check S2046ArtinToMaxAbelian
#check S2046ArtinToMaximalAbelian
#check S2046ArtinToTopological
#check S2046M2TorsionRequired
#check S2046M2CarrierRequired
#check S2046LocalArtinSourceDataOf
#check S2046M2_sufficient

#print axioms S2046ArtinToMaxAbelian
#print axioms S2046ArtinToMaximalAbelian
#print axioms S2046ArtinToTopological
#print axioms S2046LocalArtinSourceDataOf
#print axioms S2046M2_sufficient

end LeanFormal.IUT.XiFPaper.S2046M2S2089Port

end