# Stage model / CharacteristicSplitting audit

## What the stage model gives

`sourceFiniteStageModelFrobenioid.stageRationalFunctions` is
`GroupLikeAddMonoidOn (StageBase place)` with

  obj stage := Additive stage.unopˣ

i.e. a group-like rational-function object.  `stageModelDivisor` is the
normalized additive valuation into the Grothendieck group of the divisorial
monoid.

`LinearBaseIdentityEndomorphism` carries a `rationalFunction` in this
group-like object, plus divisor and balance.  If every such rational function
is invertible inside the same monoid, then O^triangle is group-like and
O^times = O^triangle; the characteristic quotient is trivial and tau = 1 is a
trivial characteristic splitting.

## Why this matters

A trivial tau would make `CharacteristicSplitting` easy, but the resulting
split Frobenioid would be too weak: the paper's O^triangle has a nontrivial
characteristic quotient.  Using tau = 1 here would be another too-weak
shortcut.

## Required check

1. Is `LinearBaseIdentityEndomorphism` in the stage model a group?  If yes,
   O^times = O^triangle and the stage model is not the paper Frobenioid.
2. If not, identify the non-unit rational functions and define tau as the
   characteristic submonoid of Definition 2.3 with nontrivial quotient.
3. Only then can CharacteristicSplitting / SplitFrobenioidPresentation be
   used for O_tri and q_v^(1/2l).

## Current status

CharacteristicSplitting is still missing.  Do not instantiate it with tau=1
until the stage model's O^triangle/O^times is verified to be nontrivial.
