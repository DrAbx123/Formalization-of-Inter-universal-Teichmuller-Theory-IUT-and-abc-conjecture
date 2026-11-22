# Single-stage objects: CANDIDATE / LOCAL, not paper D_v split Frobenioid

Date: 2026-10-29. Correction from Lead.

## Correction

S389SingleStageBase / S389SingleStageSplitFrobenioidSpec and any S396-style
restricted Phi/data/presentation are CANDIDATE/LOCAL models.  They are NOT
the paper split Frobenioid D_v of IUT I Examples 3.2-3.4 / Definition 5.2(ii).

Reason: the paper D_v has many finite etale covers as objects; it is not a
one-object category.  SingleStageBase is the full subcategory of the stage
base on the terminal stage, hence one object and only identity arrows.  That
is useful as a local toy/model to test presentation/transport, but it cannot
be used as the paper D_v object.

## Status labels

CANDIDATE/LOCAL:
* S389 SingleStageBase, singleStageBase_single_object;
* S389 SingleStageSplitFrobenioidSpec, SingleStageSplitFrobenioidRequired;
* any S396 restrictedPhi/restrictedData/preFrobenioidPresentation/
  rationalMonoidTransport over SingleStageBase (S396 was not completed and
  its unfinished file has been removed; it was never queued);
* S369 nativeStageFrobenioidPresentation is an actual stage-model
  presentation, but it is not paper D_v either; stage model has
  ramification transitions;
* S357/S373/S376 O_tri/tau/CharacteristicSplitting data are candidate
  structural data for the local split, not the paper split Frobenioid.

AUTHORITATIVE STATUS:
* S346: O_tri(T_x)/root-stack carrier remains exact missing; do not use
  completion root (S342) or single-stage local model as the paper object.
* S342: completion 2l-root is impossible for qVFamily; all completion-root
  conclusions remain INVALID.

## Rule

Do not call any single-stage presentation the paper D_v or
Definition 5.2(ii) split Frobenioid.  It may be used only as a local
candidate/model, and any paper object claim must wait for the actual
finite-etale-cover split Frobenioid construction.
