import tmp.sheaf.xif.paper.S2548Prime1249Actual

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2656Residue1249Actual

open LeanFormal.IUT.XiFPaper.S2548Prime1249Actual

theorem phi1249_surjective : Function.Surjective phi1249 := by
  intro x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨algebraMap ℤ A n, phi1249_int n⟩

noncomputable def residueEquiv1249 :
    A ⧸ p1249 ≃+* ZMod 1249 :=
  phi1249.quotientKerEquivOfSurjective phi1249_surjective

@[simp] theorem residueEquiv1249_mk (x : A) :
    residueEquiv1249 (Ideal.Quotient.mk p1249 x) = phi1249 x := rfl

#check residueEquiv1249
#check residueEquiv1249_mk
#print axioms residueEquiv1249

end LeanFormal.IUT.XiFPaper.S2656Residue1249Actual
end
