import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion

/-!
# ShehddEllipticTorsionGaloisConsumerActualAdapted — elliptic torsion Galois-action consumer

STEP 0 prior-art (reuse only; A475 search: elliptic torsion assets found):
* Foundations/Geometry/EllipticTorsion.lean: AllNTorsionRational, Torsion23Rational
  (IUT I, Definition 3.1(b)), LTorsion = torsionBy l, galoisActionOnPoint
  (+_one/_mul), galoisActionOnLTorsion, galoisActionOnLTorsionLinearEquiv
  (+_one/_mul), galoisActionOnLTorsionLinearEquivHom and the GeneralLinearGroup
  representation.

This file packages the absolute-Galois action on closure points and the l-torsion linear
representation as one consumer.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddEllipticTorsionGaloisConsumerActualAdapted

open LeanFormal.IUT

universe u

variable {F : Type u} [Field F]

/-- **PROVED consumer:** the absolute-Galois action on closure points is a homomorphism:
identity acts trivially and multiplication composes. -/
theorem galoisActionOnPoint_hom_consumer (X : PuncturedEllipticCurve F) :
    X.galoisActionOnPoint (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) =
        AddMonoidHom.id X.AlgebraicClosurePoint ∧
      (∀ sigma tau : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        X.galoisActionOnPoint (sigma * tau) =
          (X.galoisActionOnPoint sigma).comp (X.galoisActionOnPoint tau)) :=
  ⟨galoisActionOnPoint_one X, fun sigma tau => galoisActionOnPoint_mul X sigma tau⟩

/-- **PROVED consumer:** the l-torsion Galois action is a monoid representation
`Gal -> GL(E[l])` with identity/multiplication laws. -/
theorem ltorsion_galois_representation_consumer (X : PuncturedEllipticCurve F)
    (l : PrimeGeFive) :
    X.galoisActionOnLTorsionLinearEquiv l
        (1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) =
        LinearEquiv.refl (ZMod l.value) (X.LTorsion l) ∧
      (∀ sigma tau : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F,
        X.galoisActionOnLTorsionLinearEquiv l (sigma * tau) =
          X.galoisActionOnLTorsionLinearEquiv l sigma *
            X.galoisActionOnLTorsionLinearEquiv l tau) :=
  ⟨X.galoisActionOnLTorsionLinearEquiv_one l,
    fun sigma tau => X.galoisActionOnLTorsionLinearEquiv_mul l sigma tau⟩

/-- Row record: reused torsion assets vs the consumer interface. -/
def ellipticTorsionRows : List (String × String × String) :=
  [ ("rational torsion predicates (AllNTorsionRational, Torsion23Rational)", "REUSED DEF", "IUT I Def 3.1(b) layer")
  , ("l-torsion module = torsionBy, ZMod l module structure", "REUSED DEF/INSTANCE", "LTorsion / lTorsionModule")
  , ("Galois action on closure points", "REUSED DEF/PROVED", "galoisActionOnPoint + _one/_mul + stabilizer_isOpen")
  , ("l-torsion linear representation and GL form", "REUSED DEF/PROVED", "galoisActionOnLTorsionLinearEquivHom / GeneralLinearRepresentation")
  , ("consumer bundles", "COMPOSED PROVED", "galoisActionOnPoint_hom_consumer, ltorsion_galois_representation_consumer") ]

theorem ellipticTorsionRows_length : ellipticTorsionRows.length = 5 := rfl

#check galoisActionOnPoint_hom_consumer
#check ltorsion_galois_representation_consumer
#check ellipticTorsionRows_length

end LeanFormal.IUT.XiFPaper.ShehddEllipticTorsionGaloisConsumerActualAdapted
end
