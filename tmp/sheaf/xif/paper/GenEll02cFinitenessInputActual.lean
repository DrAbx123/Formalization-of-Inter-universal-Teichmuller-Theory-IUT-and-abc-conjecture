import tmp.sheaf.xif.paper.GenEll02Prop14Actual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.GenEll02Prop14Actual

namespace LeanFormal.IUT.XiFPaper.GenEll02cFinitenessInputActual

/-- **Exact paper-input registration, Prop 1.4(iv) finiteness** (corpus 323-427,
Silv1 Thm 2.1 style): for a positive integer d, C in R, ample L_Q, the set of points
x in X(Q)<=d with ht_L(x) <= C is finite.  This is a class-B paper input (the paper
derives it from Silv1 Thm 2.1 and the Fubini-Study/Chow machinery); it is registered
here explicitly, not assumed silently. -/
def Prop14FinitenessPaperInput (X : Type) (boundedSet : Set X → Prop)
    (htL : X → Real) (C : Real) : Prop :=
  HeightBoundedPointsFinite X boundedSet htL C

/-- The registered finiteness input is exactly the Prop 1.4(iv) component of the
Proposition14Statement shape. -/
theorem prop14_iv_of_finitenessInput {X : Type} {boundedSet : Set X → Prop}
    {htL : X → Real} {C : Real}
    (h : Prop14FinitenessPaperInput X boundedSet htL C) :
    HeightBoundedPointsFinite X boundedSet htL C :=
  h

def s3135FinitenessCitations : List (String × String) :=
  [ ("Prop 1.4(iv)", "corpus 323-427: ample L_Q, points of X(Q)<=d with ht_L <= C finite (Silv1 Thm 2.1 style; Fubini-Study/Chow argument) — class B paper input"),
    ("status", "registered as Prop14FinitenessPaperInput; not derived from the tree (no finiteness-of-bounded-height-points theorem for this height layer exists in LeanFormal)") ]

theorem s3135FinitenessCitations_length : s3135FinitenessCitations.length = 2 := rfl

#check Prop14FinitenessPaperInput
#check prop14_iv_of_finitenessInput
end LeanFormal.IUT.XiFPaper.GenEll02cFinitenessInputActual
end
