import tmp.sheaf.xif.paper.Mzk1Prop58iConcreteActual

/-!
# Mzk1Prop58iArithmeticDerivedActual — derived arithmetic laws for the Prop 5.8(i)
concrete invariants (new theorems; no copies/bookkeeping; no axiom/sorry).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop58iArithmeticDerivedActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iConcreteActual

universe u

variable {D : SourceLogShellDatum.{u}} {f e m : ℕ}

/-- Derived: the residue characteristic of the invariants is D.p. -/
theorem invariants_p (I : Prop58iConcreteInvariants D f e m) : I.p = D.p := rfl

/-- Derived: the invariant p* is the paper's p*. -/
theorem invariants_pStar (I : Prop58iConcreteInvariants D f e m) :
    I.pStar = paperPStar D.p := rfl

/-- Derived: the invariant p* is positive. -/
theorem invariants_pStar_pos (I : Prop58iConcreteInvariants D f e m) : 0 < I.pStar := by
  rw [invariants_pStar]
  exact paperPStar_pos D.p D.hp

/-- Derived: p* equals the tree source log-shell star. -/
theorem invariants_pStar_eq_star (I : Prop58iConcreteInvariants D f e m) :
    I.pStar = sourceLogShellStar D.p := by
  rw [invariants_pStar, sourceLogShellStar_eq_paperPStar D.p D.hp]

/-- Derived: the residue cardinality is exactly p^f. -/
theorem invariants_residueCardinality (I : Prop58iConcreteInvariants D f e m) :
    I.residueCardinality = D.p ^ f := rfl

/-- Derived: the residue cardinality is positive. -/
theorem invariants_residueCardinality_pos (I : Prop58iConcreteInvariants D f e m) :
    0 < I.residueCardinality := by
  rw [invariants_residueCardinality]
  exact pow_pos D.hp.pos f

/-- Derived: the absolute degree is exactly f*e. -/
theorem invariants_absoluteDegree (I : Prop58iConcreteInvariants D f e m) :
    I.absoluteDegree = f * e := rfl

/-- Derived: the absolute degree is positive for positive f and e. -/
theorem invariants_absoluteDegree_pos (I : Prop58iConcreteInvariants D f e m)
    (hf : 0 < f) (he : 0 < e) : 0 < I.absoluteDegree := by
  rw [invariants_absoluteDegree]
  exact Nat.mul_pos hf he

/-- Derived: the p-th-root order is exactly p^m. -/
theorem invariants_pthRootsOrder (I : Prop58iConcreteInvariants D f e m) :
    I.pthRootsOrder = D.p ^ m := rfl

/-- Derived: the p-th-root order is positive. -/
theorem invariants_pthRootsOrder_pos (I : Prop58iConcreteInvariants D f e m) :
    0 < I.pthRootsOrder := by
  rw [invariants_pthRootsOrder]
  exact pow_pos D.hp.pos m

/-- Derived: the invariant image is contained in the unit image. -/
theorem invariants_image_subset (I : Prop58iConcreteInvariants D f e m) :
    I.invariantImage ⊆ I.unitImage := by
  intro a ha
  exact preLogShell_subset_unitLayer D ha

/-- Derived: p divides p*. -/
theorem invariants_p_dvd_pStar (I : Prop58iConcreteInvariants D f e m) : D.p ∣ I.pStar := by
  rw [invariants_pStar, paperPStar]
  split_ifs with h
  · exact dvd_mul_right D.p D.p
  · exact dvd_refl D.p

#check invariants_pStar_pos
#check invariants_pStar_eq_star
#check invariants_residueCardinality_pos
#check invariants_absoluteDegree_pos
#check invariants_pthRootsOrder_pos
#check invariants_image_subset
#check invariants_p_dvd_pStar

end LeanFormal.IUT.XiFPaper.Mzk1Prop58iArithmeticDerivedActual
end
