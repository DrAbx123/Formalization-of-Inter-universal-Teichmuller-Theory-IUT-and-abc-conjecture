# Durable coordination state CLI, version 1

This implements the second layer of the coordination design: a validated role tree,
exclusive file ownership metadata, frozen task contracts, transactional state,
instance generations, recovery handshakes, pending feedback, and append-only events.
It does not invoke DeepSeek, edit Lean, authenticate callers, run a scheduler, or
enforce filesystem permissions. The actor and generation fields are trusted local
metadata. Anyone who can invoke this CLI with arbitrary metadata is not prevented
from impersonating another actor. Database access must be restricted separately.

The protocol is `iut-agent-tree/2026-10-13-v1`; the SQLite schema is version 1.
Only Python's standard library is required. Run from PowerShell:

```powershell
$stateDatabase = 'D:\lean\logs\coordination\agent-state.sqlite'
$request | ConvertTo-Json -Depth 40 -Compress |
    python -B D:\lean\tools\agent_state.py --db $stateDatabase
```

Each invocation reads one JSON object on stdin and prints one JSON object on stdout.
Successful calls exit 0 and return
`{"ok":true,"revision":1,"result":{},"replayed":false}`.
Rejected calls exit 1 and return
`{"ok":false,"error":{"code":"REVISION_CONFLICT","message":"..."}}`.
No Python traceback or private snapshot is intentionally printed on a failed call.
Requests larger than four MiB, duplicate JSON keys, non-finite numbers, missing
fields, extra fields, and unknown operations are rejected.

## Initialize the complete tree before execution

`init` requires exactly `op`, `request_id`, `expected_revision`, `run_id`,
`protocol_version`, and `agents`. The initial expected revision is zero. The full
tree is checked and committed atomically; rejected manifests do not initialize a
partial tree. An initialized database cannot be replaced through this API.

Each agent must contain exactly:

| Field | Required value |
| --- | --- |
| `agent_id` | Unique stable identifier |
| `parent_id` | Existing parent identifier, or `null` for the unique root |
| `role`, `provider`, `model` | Explicit nonempty strings; metadata, not provider calls |
| `files` | Explicit list of at most 32 exact `{path, mode}` entries |
| `contract` | Full frozen contract described below |

Stable identifiers are case-sensitive ASCII strings of 1 to 128 characters,
matching `[A-Za-z0-9][A-Za-z0-9_.:/-]{0,127}` across the entire value. The first
character must be a letter or digit; subsequent characters may also be `_`, `.`,
`:`, `/`, or `-`. This applies to agent, run, request, dependency, feedback, and
operation IDs. For example, `root`, `state_supervisor`, `persistence_owner`, and
`scenario_owner` are valid; `/root` is invalid because it starts with `/`.
Internal slashes are permitted, as in `root/state_supervisor`. Parent and actor
IDs must match registered agent IDs exactly, with the explicit `@user` operator
exception described below. External execution paths such as `/root` must have an
explicitly registered mapping to their stable IDs; they are not converted silently.

The parent relation must be connected, acyclic, and have exactly one root. It has
no fixed depth; the current manifest size limit is 4096 agents. All nodes initially
have generation 1, state `NOT_READY`, empty private checkpoint/public summary,
and no pending feedback or operations. No node can start before recovery and its
direct parent's explicit `resume`. The root's registered parent is represented
by `parent_id: null`; its controlling caller is `actor_id: "@user", generation: 0`.

File modes are `read`, `write`, `read_write`, or `append`. These register intent
only. Even two read-only owners cannot share a file. Drive-qualified absolute
Windows paths are canonicalized case-insensitively; existing file identities are
also checked for hard-link aliases. Existing reparse aliases are resolved through
filesystem metadata. UNC/device paths, wildcard/environment/short-name syntax,
alternate streams, `.`/`..`, trailing dots/spaces, and directory entries are
rejected conservatively. No source file contents are read for ownership checking.
Path registration is not an OS gateway, and future filesystem alias changes are
not prevented. A changed canonical resolution fails subsequent state validation.

A contract contains exactly `version`, `target`, `variables`, `quantifiers`,
`assumptions`, `conclusion`, and `dependencies`. The three plural mathematical
fields are explicit lists of nonempty strings, including an empty list when none
apply. Dependencies are explicit `{dependency_id, version, evidence}` objects.
All other contract values are nonempty strings. Evidence is supplied metadata;
the program does not verify a mathematical claim, a Lean compilation, or an
external effect. The SHA256 `contract_digest` covers the entire canonical JSON
contract, including assumptions and dependency versions. It is returned publicly.

There is no contract, parent, provider, model, or ownership editing operation.
A changed task requires an explicitly versioned new run in a distinct database;
it cannot silently change a current theorem's hypotheses or conclusion. Cross-run
ownership handoff remains an explicit external coordination responsibility.

This minimal complete one-node manifest is valid JSON. Include every planned
descendant in `agents` before initialization for a multi-agent run.

```json
{
  "op": "init",
  "request_id": "initialize-example-v1",
  "expected_revision": 0,
  "run_id": "example-coordination-v1",
  "protocol_version": "iut-agent-tree/2026-10-13-v1",
  "agents": [
    {
      "agent_id": "coordinator",
      "parent_id": null,
      "role": "root coordinator",
      "provider": "openai",
      "model": "explicitly-recorded-model",
      "files": [],
      "contract": {
        "version": "1",
        "target": "Coordinate the registered example task",
        "variables": [],
        "quantifiers": [],
        "assumptions": ["The operator supplies authorized local metadata"],
        "conclusion": "Every resumed node has a matching parent confirmation",
        "dependencies": []
      }
    }
  ]
}
```

## Inspect and recover after a restart

An operator can obtain the root's current generation and digest without knowing
its previous execution generation:

```json
{"op":"inspect","actor_id":"@user","generation":0,"agent_id":"coordinator"}
```

The response contains current `revision`, and `result.run_id`,
`result.protocol_version`, and `result.agent`. A self-inspect using the node's
current generation includes its private checkpoint, feedback response, original
operation descriptions, and resolution evidence. A direct parent sees only the
child's public summary, target label/version/digest, ownership metadata, pending
feedback, and operation IDs/statuses. The operator can inspect only the root's
public view. Grandparents and unrelated agents cannot inspect a node.

Every mutation other than `init` requires exactly these common fields plus its
operation-specific fields:

```json
{
  "op": "begin_recovery",
  "request_id": "coordinator-recovery-1",
  "expected_revision": 1,
  "actor_id": "coordinator",
  "generation": 1,
  "agent_id": "coordinator",
  "context": {
    "run_id": "example-coordination-v1",
    "protocol_version": "iut-agent-tree/2026-10-13-v1",
    "contract_digest": "COPY_THE_COMPLETE_DIGEST_FROM_INSPECT"
  }
}
```

Use the actual revision, generation, and digest returned by the previous call.
Successful `begin_recovery` increments the node's generation and enters
`RECOVERING`. The previous generation cannot commit another transition. Existing
feedback remains pending. Every pending task operation becomes `UNKNOWN`;
recovery never guesses that an external action succeeded.

The unique direct parent must then send `resume`, using the target's context,
the parent's current actor generation, and the target's new recovery generation:

```json
{
  "op": "resume",
  "request_id": "coordinator-resume-1",
  "expected_revision": 2,
  "actor_id": "@user",
  "generation": 0,
  "agent_id": "coordinator",
  "context": {
    "run_id": "example-coordination-v1",
    "protocol_version": "iut-agent-tree/2026-10-13-v1",
    "contract_digest": "COPY_THE_COMPLETE_DIGEST_FROM_INSPECT"
  },
  "recovery_generation": 2
}
```

Children use their registered parent's ID instead of `@user`. That parent must
have completed its own recovery. `READY`, `RUNNING`, `PAUSED`, and
`WAITING_FEEDBACK` parents can confirm a child's recovery. Allowing this control
operation while waiting avoids a recovery deadlock; it leaves the parent's own
wait and prohibition on substantive work unchanged. A `RECOVERING` parent cannot
approve a child. A resumed target becomes `READY`, or remains
`WAITING_FEEDBACK` when it still needs an answer. Only a `READY` node can `start`.

## Operations and exact additional fields

| `op` | Additional fields | Allowed transition or scope |
| --- | --- | --- |
| `begin_recovery` | None | Self, any state except `FINISHED`; fences the old generation |
| `resume` | `recovery_generation` | Direct parent, target `RECOVERING`; preserves unanswered feedback |
| `start` | None | Self, `READY` to `RUNNING` |
| `pause` | None | Self, `RUNNING` to `PAUSED`; use recovery/resume before restarting |
| `checkpoint` | `checkpoint` object, `summary` string | Self, `RUNNING` or `PAUSED`; summary is intentionally public |
| `wait` | `feedback_id`, `message` | Self, `RUNNING` or `PAUSED` to `WAITING_FEEDBACK` |
| `reply` | `feedback_id`, `target_generation`, `response` object | Direct parent, target waiting/recovering; exact ID/context/current target generation |
| `begin_operation` | `operation_id`, `description` | Self, `RUNNING`; records a pending task action only |
| `resolve_operation` | `operation_id`, `operation_generation`, `outcome`, `evidence` | Self, `RUNNING` or `PAUSED`; explicitly reconciles a pending or unknown action |
| `finish` | None | Self, `RUNNING` to `FINISHED`; rejects pending feedback/operations or any unfinished direct child |

The responding parent must be `READY`, `RUNNING`, or `PAUSED`. A successful reply
to `WAITING_FEEDBACK` makes the target `READY`; a reply during `RECOVERING` leaves
it `RECOVERING` until a matching `resume`. Responses are private to the recipient
on later inspect calls. Feedback IDs and operation IDs cannot be reused within
an agent's frozen contract. Root feedback is answered by `@user`.
Supervisors finish only after their children have finished, preserving the parent
needed to resume each child. By the same rule at each depth, unfinished descendants
cannot be stranded beneath a finished ancestor.

`resolve_operation.operation_generation` is the generation at the original
`begin_operation`, even after recovery has fenced that generation. Its actor
generation must be the current instance. Outcomes are `SUCCEEDED`, `FAILED`, or
`CANCELLED`; evidence must be a nonempty string. The explicit resolution and
evidence persist privately, while event history exposes the operation ID/outcome.
No provider/API calls are executed or automatically reconciled.

## Revisions, retries, history, and failure boundaries

Each successful mutation creates one increasing global revision, snapshot, public
event, request fingerprint, and original response in the same SQLite transaction.
Concurrent callers using the same expected revision cannot both commit. Reusing
the same request ID with the exact same complete JSON request returns the original
response with `replayed: true` and no second event, even when its expected revision
is now old. Changing any request content while reusing the ID is rejected.
An exact historical replay may describe an old generation; it is a receipt for
an already committed action, not permission for that generation to perform work.
Inspect current state after recovering a lost response.

Read public events using the current actor generation:

```json
{"op":"history","actor_id":"coordinator","generation":2,"after_revision":0}
```

Events include their revision/request ID and a public `event` object. Scope is the
actor and its direct children; `@user` sees only root events. Private checkpoint,
reply payload, operation description, and resolution evidence are excluded.
Events are bounded to the read's reported revision. Public summaries and feedback
messages are deliberately public; do not put private checkpoint material in them.
Every event has exactly `op`, `agent_id`, `actor_id`, `state`, `generation`, and
`summary`, with these operation-specific additions: `wait`/`reply` add
`feedback_id`; `begin_operation` adds `operation_id`/`status`;
`resolve_operation` adds `operation_id`/`outcome`. Other operations have no extras.

The store validates schema/protocol versions, current snapshot hashes, event-chain
consistency, cached response structure, and contiguous revisions. SQL triggers
reject event updates/deletes. These checks detect corruption; they are not a
cryptographic defense against an operator able to rewrite the database and hashes.
Missing stores, inconsistent snapshots, stale generations, stale contexts, unknown
agents, and failed transitions fail closed. No missing fields are inferred.
SQLite transactions use durable settings, but backups, media failure, and operating
system account isolation remain deployment responsibilities.

The blackbox regression command is:

```powershell
python -B D:\lean\tools\test_agent_state.py
```

The test owner uses only its registered test database and exact SQLite sidecars.
The implementation owner separately tests storage transactions on its registered
storage database. Test counts and exact versions belong in the append-only audit
ledger, rather than being asserted permanently by this usage document.
