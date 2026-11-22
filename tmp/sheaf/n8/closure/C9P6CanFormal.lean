import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.N8Closure.C9P6CanFormal

universe u v

/-- Abstract BPS full-poly groupoid: F^value x mu data determine the
full-poly-isomorphism class. -/
structure BPSFullPoly (BPS : Type u) (FData : Type v) where
  data : BPS -> FData
  Iso : BPS -> BPS -> Prop
  refl : forall X, Iso X X
  trans : forall {X Y Z}, Iso X Y -> Iso Y Z -> Iso X Z
  data_determines : forall {X Y}, data X = data Y -> Iso X Y

/-- Closed-loop data: LGP-link from Sq to Sout, and sQ1-sQ4 produce
the same F^value x mu data as Sq. -/
structure ClosedLoop (BPS : Type u) (FData : Type v)
    extends BPSFullPoly BPS FData where
  Sq : BPS
  Sout : BPS
  hLGP : Iso Sq Sout
  hSameData : data Sout = data Sq

namespace ClosedLoop

variable {BPS : Type u} {FData : Type v} (C : ClosedLoop BPS FData)

theorem hSQ : C.Iso C.Sout C.Sq :=
  C.data_determines C.hSameData

theorem closed : C.Iso C.Sq C.Sq :=
  C.trans C.hLGP C.hSQ

end ClosedLoop

/-- A3 membership data: R_poss is a set of possible output log-volumes;
hcan is an upper bound for R_poss; Qcan is the q-pilot log-volume. -/
structure A3Membership (BPS : Type u) (FData : Type v)
    extends ClosedLoop BPS FData where
  Rposs : Set Real
  Qcan : Real
  hcan : Real
  logVol : BPS -> Real
  Qcan_eq : Qcan = logVol Sq
  Sq_possible : logVol Sq ∈ Rposs
  Rposs_upper : forall x, x ∈ Rposs -> x <= hcan

namespace A3Membership

variable {BPS : Type u} {FData : Type v} (A : A3Membership BPS FData)

theorem membership : A.Qcan ∈ A.Rposs := by
  rw [A.Qcan_eq]
  exact A.Sq_possible

theorem p6_can : A.Qcan <= A.hcan :=
  A.Rposs_upper A.Qcan A.membership

end A3Membership

end LeanFormal.IUT.N8Closure.C9P6CanFormal

end