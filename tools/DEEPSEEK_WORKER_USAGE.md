# Bounded DeepSeek worker

This Python standard-library CLI submits one small bounded text task to a
selected DeepSeek model. A returned `candidate` is model output, not a Lean proof.
The worker does not read project source, run Lean, install packages, change Codex
configuration, or change the model of the current Codex chat. It executes the
existing sibling `agent_state.py` CLI as a non-model service; it does not inspect
that service's source. The state implementation remains responsible for its
registered ownership and lifecycle checks. This adapter is not a filesystem or
identity security gateway.

The implemented network protocol is Chat Completions. Configured `chat` is an
alias for `chat_completions`; `responses` is recognized but returns
`needs_feedback / RESPONSES_UNSUPPORTED`. There is no automatic protocol or model
fallback. Direct mode accepts only the official HTTPS DeepSeek endpoint, with an
optional `/v1` prefix. Config mode requires an explicit provider and a model whose
name contains `deepseek`. An explicit profile must agree with both selections.

## Commands

Use Python 3.11 or newer, without bytecode writes:

```powershell
python -B D:\lean\tools\deepseek_worker.py inspect-config --config C:\absolute\fixture.toml --provider deepseek --model deepseek-flash
python -B D:\lean\tools\deepseek_worker.py execute
```

`execute` reads exactly one JSON object from standard input (at most 32 KiB) and
writes one JSON result. Exit status is 0 for a candidate and 2 for other worker
statuses. CLI usage errors also use argparse's exit status 2. `inspect-config`
optionally accepts `--profile NAME`. Its successful result contains only provider,
model, base URL, wire protocol, and authentication field names; it does not read
credential environment values. It reports a short fixed error code for unsupported
or incomplete configuration.

Direct mode credentials must be provided only in the child process environment by
the authorized caller. Never put a key in a command argument, request packet,
fixture, task, checkpoint, or log. The adapter reads only the environment names
explicitly selected by `api_key_env`, `env_key`, or `env_http_headers`. It removes
those names from the environment passed to the state CLI. Config mode also accepts
an explicitly configured `experimental_bearer_token` or static `http_headers`.
Duplicate authentication headers and reserved transport headers are rejected.
`requires_openai_auth` alone returns `AUTH_SOURCE_REQUIRED`; no `auth.json` or
other credential file is searched. Nonempty query parameters are explicitly
unsupported. No configuration file is modified.

## Frozen request

The required shape is:

```json
{
  "schema": "deepseek-worker/v1",
  "request_id": "review-example",
  "state": {
    "db": "D:/absolute/registered-run.sqlite",
    "agent_id": "deepseek_worker",
    "generation": 2,
    "expected_revision": 7,
    "run_id": "registered-example-run",
    "protocol_version": "iut-agent-tree/2026-10-13-v1",
    "contract_digest": "REPLACE_WITH_REGISTERED_64_HEX_DIGEST"
  },
  "selection": {
    "mode": "direct",
    "provider": "deepseek",
    "base_url": "https://api.deepseek.com",
    "model": "deepseek-flash",
    "wire_api": "chat_completions",
    "api_key_env": "DEEPSEEK_API_KEY"
  },
  "task": {
    "kind": "dependency_graph",
    "question": "State the direct prerequisite of conclusion C.",
    "dependencies": [
      {"name": "A", "statement": "A has no prerequisites.", "status": "established", "version": "graph-v1"},
      {"name": "C", "statement": "C requires A.", "status": "established", "version": "graph-v1"}
    ],
    "required_dependencies": ["A", "C"]
  },
  "budget": {"max_output_tokens": 512, "timeout_seconds": 45}
}
```

Config mode replaces `selection` with exactly:

```json
{"mode":"config","config":"C:/absolute/config.toml","provider":"explicit-provider","model":"deepseek-flash"}
```

Supported task kinds are `dependency_graph` and `bounded_text`; both use the same
question, dependency, hash, and response schema. Other kinds are rejected. The
adapter does not implement a graph-sorting oracle or verify answer semantics.
Only `profile` is optional in that config selection. Direct mode and all task,
dependency, budget, and state objects reject unknown fields. There are no arbitrary
message, source, attachment, or file-body fields. Task text must be plain prose;
obvious source declarations and code fences are rejected. This conservative text
check is not a general source-code classifier or an isolation boundary. Inputs
must already satisfy the registered no-source task contract.

Dependency `status` is `established` or `missing`. `established` records a caller's
registered assumption; the adapter does not verify mathematical proofs. Missing
required names or required dependencies marked missing produce `needs_feedback`
without sending HTTP. Names are unique. Limits are 32 dependencies, a 2,000-character
question, 2,000 characters per statement, 1–1,024 output tokens, and 1–60 seconds
of total network wait. There are no automatic retries.

Before dispatch, the existing state database must contain the complete registered
task and an `assumptions` entry equal to:

```python
"task_packet_sha256=" + hashlib.sha256(
    json.dumps(
        {name: packet[name] for name in ("selection", "task", "budget")},
        sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
).hexdigest()
```

Exactly one such entry is required. `task_packet_digest(packet)` exposes the same
convention for callers. The adapter compares the actual self-inspection state
against `run_id`, protocol, `contract_digest`, generation, latest revision,
`RUNNING` state, provider, and model. Thus changing a task, selection, or budget
requires an appropriately registered contract; replacing only the packet's hash
does not authorize the change. A pending operation blocks dispatch. A previously
resolved operation using the same `request_id` also blocks redispatch.

## Results and durable operations

The base result is `{schema, request_id, status}`. Status is `candidate`,
`needs_feedback`, `rejected`, or `unknown`. A fixed `code` describes non-candidate
outcomes. A state-backed result includes `state: {revision, generation}`.

`candidate` contains `candidate: {answer: string, used_dependencies: [name]}`.
Names must be unique registered established dependencies. The adapter verifies
this shape, not the truth or completeness of the answer. A remote
`needs_feedback` response contains `feedback: {reason, missing_dependencies}`.
A locally missing premise instead returns `missing_dependencies` with code
`MISSING_DEPENDENCY` and performs no network operation.

The remote response must be HTTP 200 JSON, at most 64 KiB, with one assistant
choice, `finish_reason: "stop"`, no tool/function calls, and content containing one
strict JSON object of one of these shapes:

```json
{"status":"candidate","answer":"A precedes C.","used_dependencies":["A","C"]}
{"status":"needs_feedback","reason":"A prerequisite is unavailable.","missing_dependencies":["B"]}
```

Duplicate JSON keys, invalid constants, extra payload fields, invalid dependency
names, code fences, truncation, and reflected credential values are rejected.
HTTP error bodies, headers, exception text, credentials, and full configurations
are never returned in diagnostics. All redirects are refused; proxy discovery is
disabled so configured credentials travel directly to the selected endpoint.
DeepSeek requests explicitly set `thinking: {type: "disabled"}` and JSON output
mode. No tools or streaming are enabled.

Before HTTP, the adapter calls `begin_operation` with the request ID. After a
definitive response, it stores the sanitized result in `checkpoint`, then resolves
the operation. Accepted candidate/feedback results resolve `SUCCEEDED`; rejected
responses resolve `FAILED`. A failure to preserve or resolve the receipt yields
`unknown` and leaves an operation blocking redispatch.

A total network deadline bounds how long the caller waits, including a slow
response body. The socket timeout is also set. On timeout or another ambiguous
network failure, `begin_recovery` marks the pending operation `UNKNOWN` and fences
the old generation. The server may already have received the request: timeout
does not mean cancellation. Explicit parent recovery/resume and a decision about
the unknown operation are required before continuing. An unfinished daemon
transport blocks other in-process requests; the one-shot CLI exits after recording
the unknown outcome. Each state CLI call has a separate 15-second limit, so total
CLI wall time can exceed the configured network deadline.

The adapter processes one request at a time in one process. Atomic state revision
checks and pending-operation gates prevent duplicate dispatch against the same
node across processes. It is not a global multi-process scheduler. Live call-count
authorization remains the parent coordinator's responsibility; this CLI never
creates extra calls or retries itself.

A previously resolved request returns `needs_feedback / ALREADY_EXECUTED`, without
another HTTP call or any mutation of its existing receipt. This is a caller-action
gate, not a successful replay of a model result. A config with both `env_key` and
`experimental_bearer_token` returns `rejected / DUPLICATE_AUTH_HEADER`; neither
source is silently preferred.

## Append-only implementation record

- 2026-10-14: Registered owner `adapter_owner`, generation 2, run
  `deepseek-adapter-implementation-20261014`, contract `deepseek-adapter-v1`.
  Both owned files were absent before implementation. A separate configuration
  owner reported that the existing Codex configuration specifies the current GPT
  Responses provider, with no explicit DeepSeek target. The adapter owner did not
  read that configuration. Direct mode was authorized after the root obtained an
  explicit official endpoint and verified the model identifier. No real credential
  or network request was received or executed by this owner.
- 2026-10-14: Implemented the frozen `deepseek-worker/v1` packet, task hash binding,
  exact state CLI lifecycle, strict Chat Completions parsing, configured credential
  sources, redirect refusal, bounded input/output, and total network wait.
  `python -B D:\lean\tools\deepseek_worker.py --help` passed. Independent blackbox
  validation is delegated to the exclusive test owner; no test result or live
  connectivity claim is established by this entry.
- 2026-10-14: The root explicitly authorized adding `bounded_text` alongside
  `dependency_graph` before delivery. Both retain the exact task hash and named
  dependency gates. The prompt now addresses the registered bounded question;
  no source execution or semantic oracle was added. The registered live graph
  packet and its hash remain unchanged. Independent validation was instructed to
  add one bounded-text positive case and retain unsupported-kind rejection.
- 2026-10-14: The independent validator reported an initial direct-request smoke
  pass, including one dispatch, target/model/budget/disabled-thinking checks, and
  a sanitized durable `SUCCEEDED` receipt. Its first larger run reported 30 tests
  with 12 failures: ten reused stale fixture generations after database reset,
  one supplied two conflicting Authorization sources, and one expected the wrong
  replay-gate status. These were identified as fixture/expectation issues and a
  corrected run was requested. This entry does not claim the corrected run passed.
- 2026-10-14: The validator reported the corrected affected/new set passed:
  seven test methods covering 17 cases in 28.586 seconds. Covered cases included
  strict remote responses, missing/unknown dependency names, config redaction,
  bounded-text success, unsupported kinds, redirect refusal, and no extra HTTP on
  replay. It then added exact before/after durable replay equality and an explicit
  duplicate-auth rejection assertion; those additional results are still pending
  at this entry. No real network call has been run by the adapter owner.
- 2026-10-14: Independent validation completed its final affected run: three
  methods covering 12 cases passed in 22.166 seconds. Replay produced
  `needs_feedback / ALREADY_EXECUTED`, one total transport call, identical durable
  inspection results, and an unchanged revision. Duplicate authentication sources
  produced `rejected / DUPLICATE_AUTH_HEADER` before transport and preserved
  revision 7. Ten strict envelope cases passed with fresh fixture generations
  derived from actual init summaries and checked as `NOT_READY`, generation 1,
  before recovery to generation 2. The final test file has 34 methods covering 50
  distinct scenarios; 26 unchanged methods passed in the first run and eight
  corrected/new methods have subsequent passing evidence. A full 34-method run
  after fixture corrections was not performed; no such full-run claim is made.
  The redirect check used a fabricated HTTP 302 response, not a wire-level test of
  urllib's redirect handler. The test owner read no adapter source and issued no
  actual network request. Its reported test source SHA256 is
  `8F7C1AE926755968BDD17996252B50B88FDE016E7D6A16016B4A0526B8299B86`.
- 2026-10-14: Rehashed and froze the production adapter for the root's authorized
  single live request. Worker SHA256:
  `AD695EDE0CBDA055FD6A6FE4895628A28BC7CAEBDA6E3AD32B3D766A035A7355`.
  The adapter owner will not change this file during the live-call window. The
  independently owned test database was reported at revision 10 with worker
  generation 2 `RUNNING`, no pending operations, and a `FAILED` resolution from
  the final deliberately malformed response case. The test/database contents were
  not read by this owner. The live result remains pending at this entry.
- 2026-10-14: The root reported one successful real generation using the frozen
  production SHA256 above and the registered `deepseek-flash` direct Chat
  Completions selection. The worker CLI exited 0 with `status: candidate`, answer
  `A,B,C,D`, and `used_dependencies: [A, B, C, D]`. The root independently checked
  the exact four-node set, no duplicate nodes, and the precedence constraints
  A→B, A→C, B→D, C→D. The live state reached revision 17, generation 2. Exactly
  one generation request was made, with no retries. This verifies that bounded
  registered graph task and its transport/state integration; it is not a Lean
  proof or evidence of arbitrary theorem-proving ability.
- 2026-10-14: Before that live CLI launch, the root's service preparation hit a
  Node REPL `ReferenceError` because `process` was unavailable. The root verified
  the live state was still revision 14, `RUNNING`, with no pending operation, then
  launched the absolute Python executable with a temporary minimal process
  environment. The reported failure preceded adapter execution and did not
  require a production code change. The key stayed with the root and was never
  sent to the adapter or validation owners. No further API calls or tests were
  authorized or performed by this owner after receiving the successful result.
