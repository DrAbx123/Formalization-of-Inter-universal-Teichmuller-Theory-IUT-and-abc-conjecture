import tmp.sheaf.xif.paper.S1932BuildB3Adapted

noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1881D9D7bActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1732SourceAssemblyActual
open LeanFormal.IUT.XiFPaper.S1886D9OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1898EllipticInvolutionActual

/-! ## 5. The sign action and its packaging -/

/-- The identity equivalence of the actual S1726 fiber. -/
noncomputable def S1932IdEquiv : Bicategory.Equivalence S1898Stack S1898Stack where
  hom := 𝟙 S1898Stack
  inv := 𝟙 S1898Stack
  unit := (ρ_ (𝟙 S1898Stack)).symm
  counit := ρ_ (𝟙 S1898Stack)
  left_triangle := by
    apply Iso.ext
    exact (S1932StrongTransSubsingleton _ _).elim _ _

/-- **The coherent sign action of `{+-1}` on the actual S1726 orbicurve.**
Its inversion is the actual elliptic involution `S1898EllipticInvolution`. -/
noncomputable def S1932SignAction (l : PrimeGeFive) :
    Iut.OrbicurveSignAction S1726Orbicurve where
  diagram := S1932Diagram
  atBase := S1932IdEquiv
  inversion := S1932Sigma
  generator_identification := by
    rw [S1932Diagram_map_generator]
    exact Iso.mk
      ((λ_ S1932Sigma).hom ▷ (𝟙 S1898Stack) ≫ (ρ_ S1932Sigma).hom)
      ((λ_ S1932Sigma).inv ≫ (ρ_ (𝟙 S1898Stack ≫ S1932Sigma)).inv)
      ((S1932StrongTransSubsingleton _ _).elim _ _)
      ((S1932StrongTransSubsingleton _ _).elim _ _)
  inversionSquared := S1932SigmaSqIso

theorem S1932SignAction_inversion_eq (l : PrimeGeFive) :
    (S1932SignAction l).inversion = S1898EllipticInvolution l := rfl

theorem S1932SignAction_inversion_ne_id (l : PrimeGeFive) :
    (S1932SignAction l).inversion ≠ Pseudofunctor.StrongTrans.id S1898Stack :=
  S1898EllipticInvolution_ne_id l

/-- The generator of the sign action acts by the actual elliptic involution. -/
theorem S1932SignAction_generator (l : PrimeGeFive) :
    (S1932SignAction l).diagram.map signActionGenerator = S1932Sigma :=
  S1932Diagram_map_generator

/-- **The sign-action packaging of S1886 is filled.** -/
noncomputable def S1932SignActionPackaging (l : PrimeGeFive) :
    S1898SignActionPackaging l where
  action := S1932SignAction l
  inversion_eq := rfl

theorem S1932SignActionPackaging_nonempty (l : PrimeGeFive) :
    Nonempty (S1898SignActionPackaging l) := ⟨S1932SignActionPackaging l⟩

end LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

end
