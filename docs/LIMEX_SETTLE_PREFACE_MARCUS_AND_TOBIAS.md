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
