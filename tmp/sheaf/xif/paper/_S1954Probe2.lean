import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Complex Set

variable (a b : ℂ) (x : ℂ)

#check @segment
#check @segment_eq_image
#check @segment_eq_image'
#check @left_mem_segment
#check @right_mem_segment
#check @convex_segment
#check @segment_symm
#check @isCompact_segment
#check @Metric.mem_closedBall
#check @Metric.mem_sphere
#check @Metric.sphere
#check @isCompact_closedBall
#check @convex_closedBall
#check @Convex.linear_preimage
#check @smul_mem_segment
#check @add_mem_segment
#check @mem_segment_iff_smul
#check @Set.mem_segment

example : IsCompact (Metric.closedBall (0:ℂ) Real.pi) := isCompact_closedBall _ _
example : Convex ℝ (Metric.closedBall (0:ℂ) Real.pi) := convex_closedBall _ _
