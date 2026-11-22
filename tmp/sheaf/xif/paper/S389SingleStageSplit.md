# S389: single-stage split Frobenioid base and exact missing

Date: 2026-10-29. No ramification-transition hard fit; no fake split.

## Source reading

IUT I Examples 3.2-3.4 / Definition 5.2(ii) (and repo wiki summary):

* at a bad place, the split Frobenioid is built from the q_v^(1/2l)
  generator and the characteristic splitting tau = N * log_Phi(q_v);
* the object is local at one stage/place; the paper does not require the
  global ramification-transition section of the stage model.

Existing repo:

* SplitFrobenioidPresentation / CharacteristicSplitting are defined in
  Iut.Foundations.Frobenioid;
* stageModelFrobenioidPresentation is over StageBase place =
  (StageIndex place)^op, which has the ramification transition arrows.
  Using it directly for the local split object would force a global
  ramification section, which the task forbids.

## Correct base category

The single-stage object must use a one-object base category, not the full
StageBase.  S389 records the closest actual candidate:

SingleStageBase := full subcategory of StageBase on the terminal object
op bottom.  It has one object and only the identity endomorphism
(singleStageBase_single_object), i.e. no ramification transition arrows.

## Exact missing specification

SingleStageSplitFrobenioidSpec place:
* base : SingleStageBase place;
* S : SplitFrobenioidPresentation;
* base_is_single_stage : Prop;
* uniformizer : Prop;
* tau_eq_uniformizer_powers : Prop (tau = pi^N).

SingleStageSplitFrobenioidRequired := Nonempty spec; no inhabitant.

No actual SplitFrobenioidPresentation over SingleStageBase is constructed:
the repo has no local one-object Frobenioid presentation with a
CharacteristicSplitting tau=pi^N.  The full stage model's global
ramification section is not used.

No fake split, no completion/L, no inequality.

## Correction (Lead): CANDIDATE/LOCAL only

SingleStageBase and SingleStageSplitFrobenioidSpec are candidate/local models,
not the paper D_v split Frobenioid. The paper D_v has many finite etale covers;
the one-object model cannot replace it. Do not use as a paper object.
