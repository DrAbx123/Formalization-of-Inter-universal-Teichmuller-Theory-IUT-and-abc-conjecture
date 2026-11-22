import tmp.sheaf.xif.paper.S2893A6QIsStackActual
import tmp.sheaf.xif.paper.S1971ActionStackificationActual
import tmp.sheaf.xif.paper.S2975bA6QPresheafHomSheaf
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual
open LeanFormal.IUT.XiFPaper.S2975bA6QPresheafHomSheaf
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
namespace LeanFormal.IUT.XiFPaper.S2993A6QIsStackNoGo

/-- Explicit failure of effective descent: an etale covering sieve with a
frontier descent datum that is not in the essential image of toDescentData.
This is the exact obstruction named by S1971's trivial-sign-torsor argument. -/
structure S2993TrivialSignTorsorObstruction where
  U : Iut.SchemeOverField S2847A6.F
  R : Sieve U
  hR : R ∈ Iut.SchemeOverField.etaleTopology S2847A6.F U
  D : S2882A6Q.DescentData (fun f : R.arrows.category => f.obj.hom)
  not_effective : ∀ M : S2882A6Q.obj { as := Opposite.op U },
    ¬ Nonempty
      ((S2882A6Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).obj M ≅ D)

/-- Unconditional no-go: Q is not even a prestack, hence not a stack. -/
theorem S2993_not_isStack :
    ¬ S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F) :=
  S2975b_not_isStack

/-- Unconditional no-go: Q is not a prestack. -/
theorem S2993_not_isPrestack :
    ¬ S2882A6Q.IsPrestack (Iut.SchemeOverField.etaleTopology S2847A6.F) :=
  S2975b_not_isPrestack

/-- A trivial-sign-torsor obstruction refutes IsStack. -/
theorem S2993_not_isStack_of_obstruction
    (H : S2993TrivialSignTorsorObstruction) :
    ¬ S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F) := by
  intro hstack
  have hE : (S2882A6Q.toDescentData
      (fun f : H.R.arrows.category => f.obj.hom)).EssSurj :=
    hstack.essSurj_of_sieve H.R H.hR
  obtain ⟨M, ⟨e⟩⟩ := hE.mem_essImage H.D
  exact H.not_effective M ⟨e⟩

#check S2993TrivialSignTorsorObstruction
#check S2993_not_isStack
#check S2993_not_isPrestack
#check S2993_not_isStack_of_obstruction
#print axioms S2993_not_isStack
#print axioms S2993_not_isPrestack
#print axioms S2993_not_isStack_of_obstruction

end LeanFormal.IUT.XiFPaper.S2993A6QIsStackNoGo