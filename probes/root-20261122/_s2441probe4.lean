/-
Probe 4 for S2441.
-/
import tmp.sheaf.xif.paper.S2243RangeCompatibilityActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual

noncomputable section
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open LeanFormal.IUT.PuncturedEllipticCurve
open LeanFormal.IUT.XiFPaper.S2243RangeCompatibilityActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual

example (A : GL (Fin 2) (ZMod 5)) (v : Fin 2 → ZMod 5) :
    (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv v = A • v := by
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv]
  rw [Matrix.GeneralLinearGroup.toLin_apply]
  rfl

/-- The projection to affine points of the Galois action is the affine point map. -/
theorem S2441galoisActionProjAffine (sigma : S2229GaloisGroup)
    (P : S1720Curve.AlgebraicClosurePoint) :
    S1906ProjAffineEquiv (S1720Curve.galoisActionOnPoint sigma P) =
      S2056PointMap sigma (S1906ProjAffineEquiv P) := by
  dsimp only [galoisActionOnPoint]
  simp only [AddMonoidHom.coe_comp, AddEquiv.coe_toAddMonoidHom, Function.comp_apply]
  rw [AddEquiv.apply_symm_apply]

/-- The affine torsion equivalence is the projective-affine equivalence. -/
theorem S2441AffineTorsionEquiv_coe (P : S1720Curve.LTorsion S1982Five) :
    ((S2172AffineTorsionEquiv P : S2056Torsion) : S2056W.Point) =
      S1906ProjAffineEquiv (P : S1720Curve.AlgebraicClosurePoint) := rfl

/-- The affine basis is the transported projective basis. -/
theorem S2441AffineBasis_coe (v : Fin 2 → ZMod S1982Five.value) :
    ((S2172AffineBasis v : S2056Torsion) : S2056W.Point) =
      S1906ProjAffineEquiv ((S1982Basis v : S1720Curve.LTorsion S1982Five) :
        S1720Curve.AlgebraicClosurePoint) := rfl

/-- The matrix representation acts through the affine basis. -/
theorem S2441BasisMatrix_smul (sigma : S2229GaloisGroup)
    (v : Fin 2 → ZMod S1982Five.value) :
    S2056PointMap sigma ((S2172AffineBasis v : S2056Torsion) : S2056W.Point) =
      ((S2172AffineBasis
        (((S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis)
            sigma) • v) : S2056Torsion) : S2056W.Point) := by
  have h := galoisLTorsionMatrixRepresentation_acts S1987Five S1720Curve
    S1982Basis sigma v
  rw [S2441AffineBasis_coe, S2441AffineBasis_coe]
  rw [← S2441galoisActionProjAffine sigma
    ((S1982Basis v : S1720Curve.LTorsion S1982Five) :
      S1720Curve.AlgebraicClosurePoint)]
  rw [← h]
  congr 1
  exact congrArg S1982Basis (by
    rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
      Matrix.GeneralLinearGroup.toLin_apply]
    rfl)

/-- The base nonzero torsion point attached to a pair representative. -/
noncomputable def S2441BasePoint (x : S2009Pairs) : S2056NonzeroTorsion :=
  ⟨S2172AffineBasis x.1, by
    intro h
    have h' : S2172AffineBasis x.1 = (0 : S2056Torsion) := Subtype.ext h
    have hx0 : x.1 = 0 := S2172AffineBasis.injective (by rw [h', map_zero])
    exact isRep_ne_zero x.1 x.2 hx0⟩

/-- Unfolding of the basis-compatible pair map at the base point. -/
theorem S2441PairMap_eq (x : S2009Pairs) :
    S2180PairMap S2172AffineBasis x =
      ⟨{S2441BasePoint x, -S2441BasePoint x}, by
        rw [Finset.card_pair (S2056_ne_neg (S2441BasePoint x))]
        exact ⟨rfl, by intro Q hQ; rw [Finset.mem_insert, Finset.mem_singleton] at hQ;
          rcases hQ with rfl | rfl
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          · exact Finset.mem_insert_self _ _⟩⟩ := by
  classical
  unfold S2180PairMap
  sorry

end