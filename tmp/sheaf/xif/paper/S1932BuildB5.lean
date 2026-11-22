import tmp.sheaf.xif.paper.S1932BuildB4

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

/-! ## 6. The exact remaining datum: the quotient `C_F = X_F/{+-1}` -/

/-- The exact remaining datum of the paper's `C_F` after this file: the sign
quotient of the actual S1726 orbicurve for the constructed action, with the
sign-invariant quotient morphism and the bicategorical universal property.
No quotient stack is constructed or postulated here. -/
structure S1932CFQuotient (l : PrimeGeFive) where
  /-- The quotient orbicurve `C_F`. -/
  cF : Iut.HyperbolicOrbicurve ((S1732A l).F)
  /-- Its paper signature `(1,1)^pm`. -/
  cF_signature : cF.signature = sourceTypeOneOnePlusMinus
  /-- The sign-invariant quotient morphism `X_F -> C_F`. -/
  quotient : Iut.OrbicurveSignInvariantMorphism (S1932SignAction l) cF
  /-- The bicategorical universal property of the quotient. -/
  quotientWitness : Iut.OrbicurveSignQuotientWitness (S1932SignAction l) quotient

/-- The constructed action plus the quotient datum is the paper-faithful
`S1886PaperCF`. -/
theorem S1932PaperCF_of_quotient {l : PrimeGeFive} (Q : S1932CFQuotient l) :
    Nonempty (S1886PaperCF l) :=
  ⟨{ action := S1932SignAction l
     cF := Q.cF
     cF_signature := Q.cF_signature
     quotient := Q.quotient
     quotientWitness := Q.quotientWitness }⟩

/-- The exact first missing proposition after this file. -/
def S1932FirstMissing (l : PrimeGeFive) : Prop :=
  Nonempty (S1932CFQuotient l)

theorem S1932FirstMissing_to_PaperCF {l : PrimeGeFive} (h : S1932FirstMissing l) :
    Nonempty (S1886PaperCF l) :=
  h.elim S1932PaperCF_of_quotient

/-- Conversely, every paper-faithful `S1886PaperCF` supplies a sign action on
the actual S1726 orbicurve together with quotient data for it; the sign action
itself is already constructed in this file. -/
theorem S1932PaperCF_gives_quotientData {l : PrimeGeFive}
    (h : Nonempty (S1886PaperCF l)) :
    (Nonempty (S1898SignActionPackaging l)) ∧
      ∃ (A : Iut.OrbicurveSignAction S1726Orbicurve)
        (cF : Iut.HyperbolicOrbicurve ((S1732A l).F)),
        cF.signature = sourceTypeOneOnePlusMinus ∧
          ∃ q : Iut.OrbicurveSignInvariantMorphism A cF,
            Nonempty (Iut.OrbicurveSignQuotientWitness A q) := by
  obtain ⟨Q⟩ := h
  exact ⟨S1932SignActionPackaging_nonempty l,
    ⟨Q.action, Q.cF, Q.cF_signature, Q.quotient, ⟨Q.quotientWitness⟩⟩⟩

end LeanFormal.IUT.XiFPaper.S1932SignActionQuotientActual

end
