# Agent bootstrap helper, version 1

This standard-library helper performs bounded recovery handshakes over the
existing state CLI. Each child calls as itself; its actual direct parent
separately authorizes an explicit batch and calls as itself. It does not schedule
models, dispatch DSH, change the service/schema, authenticate identities or enforce
filesystem isolation.

Command:

    python -B D:\lean\tools\agent_bootstrap.py --db EXACT_REGISTERED_DATABASE

Send one UTF-8 or ASCII-escaped JSON object on stdin and close stdin. Stdout is
flushed ASCII JSON Lines. The helper reads UTF-8 explicitly and calls the fixed
sibling agent_state.py with ASCII JSON through python -B -X utf8. Prefer ASCII
JSON through PowerShell, which may otherwise transcode text before Python sees it.
No helper database or journal is created. Initialize the complete frozen tree
through the existing service first.

## Child call

Every field is required; extras are rejected. Replace example IDs/digests with
registered values. The all-zero digest is only a placeholder.

~~~json
{
  "schema": "agent-bootstrap/v1",
  "mode": "child",
  "ticket": "child-a-bootstrap-v1",
  "actor_id": "child_a",
  "parent_id": "supervisor",
  "context": {
    "run_id": "example-v1",
    "protocol_version": "iut-agent-tree/2026-10-13-v1",
    "contract_digest": "0000000000000000000000000000000000000000000000000000000000000000"
  },
  "from_generation": 1,
  "recovery_generation": 2,
  "limits": {"timeout_seconds": 30, "max_cas_retries": 4},
  "continuation": null
}
~~~

The recovery generation must equal the from generation plus one. At the from
generation, only NOT_READY/PAUSED with no pending feedback or operations may begin
recovery. At the recovery generation, RECOVERING waits for the actual parent,
READY starts itself, and RUNNING succeeds without another mutation.

Reenter with the same ticket and generation pair. Do not increment the pair just
because a call timed out. The registered root may use parent_id "@user", but its
operator must submit resume through the existing state CLI; parent mode below
accepts ordinary registered parent agents only.

## Actual-parent batch call

Run concurrently with the child calls, or after children publish their waiting
receipts. Parent context belongs to the parent; each child has its own context.

~~~json
{
  "schema": "agent-bootstrap/v1",
  "mode": "parent",
  "ticket": "supervisor-bootstrap-batch-v1",
  "actor_id": "supervisor",
  "generation": 2,
  "context": {
    "run_id": "example-v1",
    "protocol_version": "iut-agent-tree/2026-10-13-v1",
    "contract_digest": "1111111111111111111111111111111111111111111111111111111111111111"
  },
  "children": [
    {
      "agent_id": "child_a",
      "context": {
        "run_id": "example-v1",
        "protocol_version": "iut-agent-tree/2026-10-13-v1",
        "contract_digest": "0000000000000000000000000000000000000000000000000000000000000000"
      },
      "recovery_generation": 2
    }
  ],
  "limits": {"timeout_seconds": 30, "max_cas_retries": 4},
  "continuation": null
}
~~~

The parent must be READY/RUNNING/PAUSED with no pending feedback or operations.
The 1 to 64 unique children must be its direct children in the same run/protocol.
Before each new resume, the entire selected batch is checked. At
recovery_generation - 1, NOT_READY/PAUSED is awaited. At the expected generation,
RECOVERING is resumed and READY/RUNNING is complete. Wrong parent, context or
generation rejects the batch before its next mutation. A child's real feedback,
PENDING/UNKNOWN operation or FINISHED state is instead reported in blocked_children;
other valid children still proceed. Once those other children are ready, the
result is blocked/CHILDREN_BLOCKED, not a claim that the whole batch is ready.
Parent mode never starts a child.

A batch is not atomic: earlier successful resumes remain if a later child blocks.
Each mutation uses the earliest validated parent revision; intervening state
changes produce CAS conflict instead of bypassing a clean-state check.

## Limits, receipts and continuation

Tickets are stable ASCII IDs of at most 64 characters. Other IDs use the state
service syntax. Digests are 64 lowercase hexadecimal characters. timeout_seconds
is an integer 1 through 60; max_cas_retries is an integer 0 through 8. Booleans,
duplicate JSON keys, non-finite numbers and unknown fields are rejected. Input
is bounded to one MiB of UTF-8 bytes.

Receipts contain schema, status, mode, ticket, observations, continuation,
cas_conflicts, blocked_children and an optional code. Each blocked-child item has
only agent_id and code. Observations contain only agent_id, parent_id,
generation, state, revision and contract_digest. Invalid-input receipts have null
mode/ticket/continuation and empty observations. Private checkpoints, replies,
operation descriptions, raw service output and tracebacks are never forwarded.

| Status | Meaning | Exit |
| --- | --- | --- |
| pending | Original mutation recorded in the emitted continuation before dispatch | Intermediate |
| waiting | Waiting for actual parent or children | Intermediate |
| retrying | Explicit REVISION_CONFLICT | Intermediate |
| ready | Child RUNNING, or all selected children READY/RUNNING | 0 |
| rejected | Invalid input or continuation intent mismatch | 1 |
| blocked | Known service/state/context/precondition refusal | 2 |
| timeout | Wait budget exhausted; readiness not established | 2 |
| unknown | Unavailable mutation/service receipt or unclassified failure | 3 |

Retain the latest receipt as it arrives. Pass its continuation unchanged in the
same request to continue. Intent fields, including ticket and child order, must
stay identical; limits may change. The handle contains an intent digest, per-step
CAS counters and an optional pending record. Together with the original input,
it reconstructs the exact mutation including request ID and expected revision.
It is not an authentication token.

Before each mutation the pending receipt is flushed. If the process is killed,
the caller must retain that receipt: there is no helper journal. An uncertain
response is reconciled by replaying only the identical state request at most once
per invocation. If still uncertain, the handle remains pending and exit 3 is
returned. INTERNAL_ERROR and ambiguous storage I/O/busy responses are treated
conservatively this way.

Only explicit REVISION_CONFLICT permits a freshly inspected local attempt with a
new attempt ID. Counters accumulate per step across continuation; exceeding the
retry budget returns blocked/REVISION_CONFLICT. Limits can subsequently be raised
within the documented maximum. A historical replay is followed by current
inspection and never licenses work by an old generation.

An incoming pending handle cannot skip fresh safety checks: at a past revision its
request can only replay a cached receipt or conflict; at the current revision it
must pass context, parent, generation and clean-state checks before applying.
Hand-editing handles is not a supported continuation mechanism.

Each subprocess call has a five-second timeout capped by the remaining budget;
polls sleep at most 0.1 seconds. A read cut off by the overall deadline returns
timeout if no mutation is pending. OS process creation/termination can add
scheduling overhead; this is not a hard real-time deadline.

FINISHED, WAITING_FEEDBACK and pending feedback/PENDING/UNKNOWN operations require
ordinary owner/parent handling. Nothing is auto-replied, resolved or reopened.
Parent mode deliberately requires a clean parent, even though the lower-level
service allows some recovery control while waiting.

Keep one active execution instance per logical node/ticket. If every receipt was
lost after an uncertain call, reconcile through the existing service before
assuming a result. Observations describe snapshots, not an everlasting guarantee
against later changes. This helper never repeats a DSH/model/compiler task.

## Native event wakeups

A dispatched parent may end its native turn while remaining logically RUNNING.
When a child has a real result/request, use followup_task to wake an idle non-root
direct parent, keeping the same task objective and parent chain. For root use
send_message. A message alone does not wake an idle non-root parent. This is a
convention for existing collaboration tools, not an MCP scheduler in the helper.

On result delivery or slot release, supervisors still check runnable registered
siblings. One blocked child does not block independent sibling tasks.
