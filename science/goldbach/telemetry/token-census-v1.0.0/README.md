# LIMEX Goldbach Research Run: Token Telemetry Census

**Study date:** 16 September 2026  
**Observed research window:** 1 September 2026, 18:47:42.915 UTC to 15 September 2026, 01:55:05.072 UTC  
**Release endpoint:** `goldbach-v1.8.767`  
**Mathematical status:** `GLOBAL_GOLDBACH_STATUS = NO_PROOF`  
**Global all-host token total:** `NOT_IDENTIFIABLE`

## Executive summary

This document reports a retrospective census of locally available token telemetry for the LIMEX Goldbach research run. Two operationally separated audit lines independently reconstructed and classified the available records before a separate COO adjudication.

The defensible result is a **local Goldbach-related classification envelope of 4,800,018,574 to 5,327,048,926 provider-reported tokens**, or **4.800018574 to 5.327048926 billion tokens**.

This range is not a confidence interval. It expresses deterministic classification uncertainty: its lower endpoint includes only turns classified as Goldbach-only under the adjudicated method, while its upper endpoint additionally includes all mixed turns that cannot be prorated without inventing information.

Nine visible remote Windows tasks have no token ledger in the local evidence package. Their contribution was neither assumed to be zero nor estimated. An exact global total is therefore not identifiable from the available evidence.

The study does **not** establish:

- a proof of the binary Goldbach conjecture;
- energy consumption or energy savings;
- monetary cost, cost savings, ROI, or commercial efficiency;
- model superiority, productivity gain, or research quality;
- a complete end-to-end disclosure of OpenAI's inference infrastructure;
- external peer review or independent replication.

## 1. Research question

> How many provider-reported tokens are locally observable for the Goldbach research quest from the first explicit Goldbach instruction through the verified deployment of `goldbach-v1.8.767`, under conservative turn-level attribution rules?

The unit of analysis is the locally recorded model turn. The measured quantity is provider-reported token telemetry, not unique words, unique semantic content, FLOPs, joules, wall-clock active work, or billed currency.

## 2. Study design

The correct study description is:

> A retrospective observational token-telemetry census with two operationally separated analysis lines and subsequent adjudication.

The project uses the expression *double-blind* only in a narrow operational sense: the two audit lines were instructed to work independently and were not given the other line's intermediate or final result before submission. This is not a classical double-blind trial. There were no blinded participants, randomized interventions, placebo controls, or external adjudicators.

Because the study is a census of available telemetry rather than a random sample:

- no p-value is applicable;
- no sampling-based confidence interval is applicable;
- no statistical-significance claim is made;
- uncertainty arises from turn classification, legacy telemetry, mixed-purpose turns, and unavailable remote-host ledgers.

### 2.1 Temporal and event boundary

| Boundary | Evidence-bound definition |
|---|---|
| Start | First explicit Goldbach prompt at `2026-09-01T18:47:42.915Z`, source ordinal `299287`, turn `01a05e30-a126-7531-a8d4-5e20038edcd3` |
| End | Completed deployment of `goldbach-v1.8.767` at `2026-09-15T01:55:05.072Z`, turn `01a0a28c-477e-7ec1-9d1f-9192deedade6` |
| Elapsed calendar span | `1,148,842.157` seconds, approximately `13.296784` days |

The start prompt occurred inside an already-running provider-accounted turn. Audit Line A applied a prompt-level boundary using the last cumulative counter immediately before the Goldbach prompt and excluded `8,645,268` pre-prompt tokens from that turn. Audit Line B retained the complete turn. This difference is disclosed rather than silently normalized away.

## 3. Data sources and counting rules

### 3.1 Primary local source

The primary source is a local Codex session JSONL ledger:

```text
SHA-256: b046c9b4ce11e6115dd37a67c4e7b791f0b3918f12cedd8cba2fc0c0b7a0c82c
Size:    5,179,705,804 bytes
Lines:   502,924
```

The raw source contains private and commercially sensitive content and is not suitable for unrestricted publication. Reproducibility must therefore rely on controlled access, the derived audit artifacts, exact hashes, transparent scripts, and, where appropriate, sanitized fixtures.

Twenty-nine whole-file parse anomalies were reported by one parser, all before the measured Goldbach window; the other parser reported zero. Both audit lines found zero parse failures inside the adjudicated measurement window. The defensible statement is therefore limited to the measured window.

### 3.2 Token semantics

The census applies these rules:

1. `total_tokens = input_tokens + output_tokens`.
2. `cached_input_tokens` is a subset of `input_tokens` and is not added again.
3. `reasoning_output_tokens` is a subset of `output_tokens` and is not added again.
4. Modern local turns are counted once using the final `turn_token_usage` snapshot for each `(thread_id, turn_id)`.
5. Cumulative `thread_token_usage` values are never summed as if they were independent observations.
6. Cache hits remain included when they appear in provider telemetry. The reported billions are gross processed or accounted token units, not billions of unique lexical tokens.
7. An early legacy segment is reconstructed from cumulative counters and remains partial at turn level.
8. Mixed turns are not fractionally allocated. They are reported as a separate uncertainty component.
9. Missing remote ledgers are not imputed.

The tokenizer implementation and version were not independently audited. Accordingly, the result is explicitly described as *provider-reported token telemetry*.

## 4. Results

### 4.1 Adjudicated local result

| Quantity | Tokens | Billion tokens | Interpretation |
|---|---:|---:|---|
| Goldbach-only lower classification bound | **4,800,018,574** | **4.800018574** | Locally observed; semantic classification remains partial |
| Mixed and non-separable | **527,030,352** | **0.527030352** | Locally observed; Goldbach share not identifiable |
| Goldbach-related local upper classification bound | **5,327,048,926** | **5.327048926** | Lower bound plus all mixed turns |
| Non-Goldbach sidequests in the same chronology | **1,850,247,823** | **1.850247823** | Excluded from Goldbach attribution |
| Full observed local chronology | **7,177,296,749** | **7.177296749** | Includes sidequests and locally observable guardian reviews |
| Remote Windows contribution | not observable | not observable | Nine tasks; no local token ledger |

Exact reconciliation:

```text
4,800,018,574 + 527,030,352 = 5,327,048,926
5,327,048,926 + 1,850,247,823 = 7,177,296,749
```

### 4.2 Independent audit lines

| Measure | Line A | Line B |
|---|---:|---:|
| Local chronology | 7,177,296,749 | 6,992,896,767 |
| Goldbach-only classification | 4,800,018,574 | 4,857,024,799 |
| Mixed classification | 527,030,352 | 368,899,295 |
| Goldbach-related upper value | 5,327,048,926 | 5,225,924,094 |
| Guardian reviews included | yes | no |
| Exact prompt boundary applied | yes | no |

The chronology difference reconciles exactly:

```text
7,177,296,749 - 6,992,896,767 = 184,399,982

192,354,896  locally observed guardian-review tokens
- 8,645,268  pre-prompt tokens removed by Line A
+   690,354  later legacy total-only tokens
= 184,399,982
```

Line A was selected for the full local quest scope because guardian reviews are real model turns within the audited process and because it applies the exact start boundary. The disagreement in semantic turn classification is preserved through the reported envelope rather than resolved by averaging.

### 4.3 Descriptive composition

Using the full observed local chronology as denominator:

- Goldbach-related classification envelope: approximately **66.88% to 74.22%**;
- clearly non-Goldbach sidequests: approximately **25.78%**;
- locally observed guardian reviews: approximately **2.68%**.

These percentages are descriptive accounting ratios. They are not estimates of scientific productivity, useful work, efficiency, or causal impact.

## 5. Hardware disclosure

### 5.1 Locally observed collection and audit workstation

The following snapshot was read from the local audit host on 16 September 2026:

| Component | Observed value |
|---|---|
| Device class | Apple MacBook Pro |
| Model identifier | `Mac17,6` |
| Model number | `Z1N20007XD/A` |
| SoC | Apple M5 Max |
| CPU topology | 18 cores, reported by macOS as 6 Super and 12 Performance cores |
| Unified memory | 64 GB |
| Architecture | ARM64 |
| Operating system | macOS 26.5, build `25F71` |
| Kernel | Darwin 25.5.0, `RELEASE_ARM64_T6050` |
| System firmware | `18000.120.36` |
| OS loader | `18000.120.36` |
| System Integrity Protection | enabled |

Serial numbers, hardware UUIDs, provisioning identifiers, credentials, account identifiers, and private filesystem content are intentionally excluded.

This workstation executed local orchestration, formal builds, file and hash checks, and the telemetry analysis. The snapshot does not prove that every historical client-side action ran on an unchanged host configuration.

### 5.2 Hardware not observed by this study

The following hardware is outside the available evidence:

- OpenAI inference servers, accelerators, storage, network fabric, and power systems;
- scheduler placement and geographic region for individual model calls;
- the hardware configurations of the nine remote Windows tasks;
- physical power draw at the workstation, network, data center, or accelerator level.

No end-to-end hardware, energy, or carbon claim is therefore made.

## 6. Software and model stack

### 6.1 Locally observed audit-day utilities

| Component | Observed version or state |
|---|---|
| Codex CLI installed on audit day | `codex-cli 0.146.0` |
| Codex client/runtime versions present in session metadata | `0.146.0-alpha.3.1`, `0.153.0-alpha.5`, `0.153.0`, `0.153.4`, `0.154.0-alpha.6.2` |
| Node.js | `v24.13.1`; binary SHA-256 `29ecb10b64e8de28f5073f0b91f2fdc9ee60a0e21995edfcacb02eb0aae01a79` |
| jq | `jq-1.7.1-apple` |
| Git | `2.50.1 (Apple Git-155)`; binary SHA-256 `179301dcb41ea78accc3fa0048a7e6f6710d891945a751a34addd622020c1818` |
| zsh | `5.9` |
| shasum | `6.02` |

These are observed current or recorded client-side values. They are not evidence that the entire software stack remained unchanged throughout the 13.3-day window.

The census and reconciliation utilities are JavaScript ES modules. The audited scripts use Node.js built-ins including `fs`, `path`, `readline`, `crypto`, and `url`; no third-party npm dependency was detected in those scripts. Node.js `v24.13.1` is the reproduction runtime observed on the audit day, not a cryptographically bound historical runtime for every earlier census invocation.

### 6.2 Recorded model phases

The primary local thread records both OpenAI GPT-5.6 SOL and GPT-6 Astra at `xhigh` reasoning effort:

- the first Goldbach turn is recorded under GPT-5.6 SOL;
- the first GPT-6 Astra execution context appears at `2026-09-05T10:19:29.927Z`;
- the primary thread returns to GPT-5.6 SOL at `2026-09-07T17:25:46.742Z`;
- GPT-6 Astra appears again from `2026-09-08T17:34:04.376Z`;
- GPT-5.6 SOL appears again from `2026-09-08T21:12:09.718Z` through the deployment endpoint;
- the measured window contains 574 GPT-5.6 SOL and 260 GPT-6 Astra primary-thread `turn_context` records.

Some local delegated records additionally bind the same model families at `high` effort. These counts and settings describe context records, not token attribution. This census does not assign exact token totals to either model, and it does not compare their quality or efficiency. Child-agent, guardian, and remote-host model coverage is not complete enough for a defensible per-model allocation.

### 6.3 Provider-side software not observed

The evidence package does not expose or independently verify:

- model weights or serving revisions;
- server-side tokenizer implementation;
- inference runtime, kernels, quantization, batching, or speculative decoding;
- scheduler and cache implementation;
- data-center operating system and driver stack;
- provider-side retries, routing, or physical resource allocation.

The phrase *complete stack disclosure* therefore applies only to the locally observed client, audit, and formal-verification layers. It does not apply to the full provider infrastructure.

## 7. Formal mathematics stack and status

The token census and the Lean proof capsule answer different questions. Token telemetry measures recorded processing volume. Lean checks whether specified terms inhabit specified propositions under their explicit assumptions. Neither validates the other.

The released formal capsule records:

| Item | Value |
|---|---|
| Release tag | `goldbach-v1.8.767` |
| Recorded Git commit | `5d4678f8f7a1d1015ade42a469736974f5ba084c` |
| Lean | `leanprover/lean4:v4.33.1` |
| Mathlib revision | `0df444a360eaa60ab8c11dca51a86af692955474` |
| Root module | `GoldbachCircleMethodActualQ3FullConditionalClosureV18767` |
| Custom source modules in recorded closure | 634 |
| Custom axiom declarations | 0 |
| `sorryAx` | 0 |
| Theorem status | `KERNEL_PROVED_CONDITIONAL` |
| Denominator scope | `q=3_PROJECT_BRANCH` |
| Minor-arc closure | `OPEN` |
| Global Goldbach status | `NO_PROOF` |

The final conditional theorem composes an eventual scale condition, a fixed-modulus distribution estimate supplied as an explicit hypothesis, a signed local-density reserve supplied as an explicit hypothesis, and an audited absorption step for the literal q=3 project branch. The capsule does not construct inhabitants for the two substantive open inputs, close all denominator channels, close the minor arcs, or prove the binary Goldbach conjecture.

## 8. Reproducibility and provenance

The study package contains:

- the human-readable and machine-readable COO synthesis;
- independent Line A and Line B reports;
- machine-readable line results and reconciliation artifacts;
- turn-classification tables;
- extraction, legacy-reconstruction, classification, aggregation, and verification scripts;
- SHA-256 manifests for the principal outputs;
- separate README audits for scientific claims and stack/provenance disclosure.

Primary synthesis artifacts:

| Artifact | SHA-256 |
|---|---|
| `GOLDSTANDARD_GOLDBACH_TOTAL_TOKEN_CENSUS_V1.md` | `03677857b5cab43ad6b378afee4675fa79e2a2b6ee139954b21401d72395f253` |
| `GOLDSTANDARD_GOLDBACH_TOTAL_TOKEN_CENSUS_V1.json` | `30b2fd9c12e73f470b3f46bb98cae272240aac648f4d482e27a8cabcee9c23b2` |
| Line A report | `b5644c9e2ba93b5ffbfae3acddd1a2bb2b21deb54f12b20256ed15371bd1098b` |
| Line A machine result | `6d749f632f86107d01429c49b5c71dfd2e34619cdb6d75cd0cc5d48e4b07edfe` |
| Line B report | `c4a280af3f69e43bfb12314a33f5392c828d4aef2a4d56f5d126f5523bff9e69` |
| Line B machine result | `c52f25b4b347eca7d3d9066a89893fe3c1017b5a0985952bc905f2cbf493d3ff` |
| Scientific-claims README Audit A | `3b1edf3e15751e19b15a67a3f2f6b11482cd8210fb26cc7ce06814b3e5218ae1` |
| Stack/provenance README Audit B | `91df08c38a9dbb672b3cdd2defff0995f958897216d345620294f566aaebfd5a` |

An independent reviewer can inspect the derived artifacts and scripts without receiving unrestricted access to private correspondence. Full raw-data reproduction requires controlled access to the hashed JSONL or a separately verified, de-identified derivative. This is a declared evidence-access limitation.

## 9. Peer-review posture

This README is structured to support serious review, but the present state is **internally audited through two independently implemented lines, not externally peer-reviewed**.

### Strengths

- exact event boundaries and stable identifiers;
- explicit counting semantics that prevent cache and reasoning-token double counting;
- two independently implemented audit lines;
- exact arithmetic reconciliation of their chronology difference;
- retained disagreement rather than forced consensus;
- machine-readable outputs and cryptographic hashes;
- transparent separation of observed and unobserved infrastructure;
- explicit negative claims and fail-closed handling of missing remote data.

### Threats to validity

1. **Classification validity:** Mixed turns cannot be allocated exactly without token-level semantic labels.
2. **Coverage validity:** Nine remote Windows tasks lack local token ledgers.
3. **Legacy telemetry:** The early segment is reconstructed from cumulative counters and remains partial at turn level.
4. **Instrumentation validity:** The provider tokenizer and telemetry implementation were not independently audited.
5. **Historical configuration:** The current workstation snapshot does not prove an unchanged historical client environment.
6. **Analyst independence:** SFH developed LIMEX, ran the project, commissioned both audit lines, and performed adjudication.
7. **External reproducibility:** Raw logs cannot be openly published without exposing private or commercially sensitive material.
8. **No counterfactual:** There is no matched non-LIMEX Goldbach run from which a causal efficiency effect could be estimated.

### Conflict-of-interest statement

SFH developed LIMEX, conducted the Goldbach research run, generated the telemetry, commissioned the internal audit lines, and performed final adjudication. The independent dual-line method reduces implementation and classification risk but does not replace independent external review.

## 10. Business interpretation

The evidence supports a capacity-planning and governance case study, not a performance or savings claim.

The run demonstrates why long-horizon agentic research requires:

- project- and turn-level scope identifiers;
- immutable telemetry and reproducible extraction rules;
- separate accounting for productive work, mixed work, sidequests, and audit overhead;
- explicit ledger export from every worker host;
- model-transition recording;
- cost and energy telemetry kept separate from token counts;
- formal status flags that prevent research volume from being mistaken for mathematical completion.

For business planning, the measured envelope establishes workload magnitude and reveals two material governance issues: mixed-scope work creates attribution uncertainty, and missing remote ledgers prevent complete cost-center accounting. Both are operational findings. Neither proves that LIMEX reduces tokens, time, cost, or energy.

A defensible ROI or efficiency study would require a preregistered matched-task design, a stable model/runtime policy, complete all-host telemetry, identical quality criteria, independent scoring, and direct billing or power measurements. Without those elements, converting the present census into savings percentages would be pseudo-precision.

## 11. Data availability and privacy

Derived reports, classification tables, scripts, receipts, and hashes can be shared subject to project release policy. Raw session logs contain user messages, private correspondence, local paths, and potentially sensitive operational context. They must remain access-controlled unless a separate privacy review approves a de-identified derivative.

No credential, authentication secret, hardware identifier, or unrestricted raw transcript is required to verify the published arithmetic.

## 12. Decision status and next gate

```text
LOCAL_GOLDBACH_ONLY_LOWER_BOUND      = 4.800018574_BILLION_TOKENS
LOCAL_GOLDBACH_RELATED_UPPER_BOUND   = 5.327048926_BILLION_TOKENS
LOCAL_FULL_CHRONOLOGY                = 7.177296749_BILLION_TOKENS
REMOTE_WINDOWS_TOKEN_USAGE           = NOT_IDENTIFIABLE
GLOBAL_EXACT_GOLDBACH_TOKEN_TOTAL     = NOT_IDENTIFIABLE
ENERGY_INFERENCE                      = NOT_PERFORMED
COST_ROI_EFFICIENCY_INFERENCE         = NOT_PERFORMED
EXTERNAL_PEER_REVIEW                  = NOT_EXECUTED
GLOBAL_GOLDBACH_STATUS                = NO_PROOF
```

The single evidence-completing next gate is to acquire authenticated final token ledgers for the nine remote Windows tasks and rerun the unchanged census. Until then, the local classification envelope is the maximum defensible quantitative statement.
