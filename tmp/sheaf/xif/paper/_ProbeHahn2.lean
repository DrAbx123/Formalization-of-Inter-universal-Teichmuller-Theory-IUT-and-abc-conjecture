import Mathlib.RingTheory.HahnSeries.Basic
open HahnSeries
variable {K : Type} [Field K]
#check (1 : HahnSeries Int K)
#check HahnSeries.C (1:K)
#check (HahnSeries.single (1:Int) (1:K) : HahnSeries Int K)
#check (HahnSeries.single (1:Int) (1:K))^2