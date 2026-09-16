---
status: Goldstandard
scope: LIMEX Settle only; separate from LIMEX Science
language: en-US
source_basis: Gemini draft supplied by Marcus, revised with Marcus' clarifications on 2026-09-15
fact_boundaries:
  - LIMEX Settle is offered under commercial licenses.
  - Relevant settlement state is anchored to Bitcoin Layer 1 through Merkle-root commitments.
  - LIMEX Settle is designed as a Bitcoin-anchored Layer 2 settlement framework.
  - LIMEX Settle provides deterministic protocol-level finality independently of individual Bitcoin block intervals.
---

# Preface: Settlement on a Bitcoin-Anchored Foundation

## Acknowledging Satoshi Nakamoto

Bitcoin introduced a practical model for digitally scarce assets and decentralized settlement. LIMEX Settle is developed with respect for that contribution and for the engineering discipline behind it.

Bitcoin Layer 1 is intentionally conservative. Its security model and decentralized consensus make it a durable settlement anchor, while its block-based design limits the frequency of on-chain transactions.

This creates an important engineering challenge: how can frequent and low-value settlement activity be supported without weakening the guarantees of the Bitcoin base layer?

## The Role of LIMEX Settle

LIMEX Settle is designed as a Bitcoin-anchored Layer 2 settlement framework. It aims to support frequent settlement activity outside the cadence of Bitcoin blocks while preserving a verifiable connection to Bitcoin Layer 1.

LIMEX Settle provides deterministic protocol-level finality independently of individual Bitcoin block intervals. Relevant settlement state is aggregated into Merkle-root commitments anchored to Bitcoin Layer 1, creating an auditable cryptographic reference to the base layer.

Settlement therefore operates across two complementary layers: LIMEX Settle governs continuous protocol-level state transitions, while Bitcoin Layer 1 remains the base-layer anchor for the committed settlement state.

LIMEX Settle is built around three principles:

- **High-Frequency Settlement**  
  The architecture is intended to support continuous micro-state updates outside Bitcoin block intervals.

- **Efficient Execution**  
  LIMEX Settle pursues resource-aware settlement paths suited to high-volume and machine-to-machine use cases.

- **Formal Rigor**  
  Like the wider LIMEX architecture, Settle is designed around deterministic rules, traceable state transitions, and auditable protocol behavior.

LIMEX Settle does not seek to replace Bitcoin Layer 1. It provides additional settlement infrastructure for use cases that require a higher execution frequency than the base layer alone can provide.

LIMEX Settle is offered under commercial licenses. Its objective is to preserve the strengths of the Bitcoin base layer while making its settlement foundation usable for more demanding digital workflows.

**Marcus & Tobias**  
*LIMEX Core Architecture*

---

## Released implementation status

This release contains a deterministic settlement and release-seal reference
core. It does not contain or claim a productive Bitcoin, Lightning, wallet,
bank, treasury, bridge, sequencer, prover, or payment-provider connection.
Bitcoin anchoring describes the intended system architecture; productive
anchoring remains a separate integration and validation stage.

The embedded cleanroom core is byte-identical to the validated release
candidate. Its historical blocked-publication gate is retained unchanged as
evidence. Distribution authority is supplied by the signed outer release
wrapper.

### Verification values

- Core package root SHA-256: `90e2793ed93f952b5b3c96b0dccc1fb4036d95ed1205306ccd205a79729b65fa`
- Release content root SHA-256: `84690914566dd0ffcd05fcf707a3acad440a1e99490233e029db0507f701cd25`
- Release content manifest SHA-256: `1e501eeab83d5699e603021b02a7e100cae07d6baf7d1c3969a8dc45e7f7f3a9`
- ZIP SHA-256: `1e965623a42f0a196e768f9124c0e1295b8b4437a979e6486ca3343e4d55ded7`
- CEO authority envelope SHA-256: `e084b9b4450e2e7da77c0b39e375242fcbd1c650f3d133f077e466cd63867c88`
- Licence: proprietary; all rights reserved; no licence granted

The CEO confirms that the relevant applications were filed on 2026-09-15,
acknowledged by the DPMA, and approved for release by Dr. Karl and Max. The
official DPMA receipt was not yet transferred by counsel when these release
bytes were bound and is therefore not represented as an embedded byte-bound
receipt.
