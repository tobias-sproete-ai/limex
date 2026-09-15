import GoldbachCircleMethodCaseSelectedPointwiseGoldbachTransferV18262

/-!
# Goldbach V1.8.263: exceptional-zero gap attestation repair

V1.8.260 named the active real parameter `beta`, while V1.8.261 passed it
directly to `powerWeight b = n^(-b)`.  The source correction instead requires
`b = 1 - beta`, so that `n^(-b) = n^(beta-1)`.  This append-only successor
repairs the semantic interface and retains V1.8.260--262 as a negative audit
trace rather than rewriting them.
-/

open scoped Classical BigOperators

set_option autoImplicit false

namespace GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263

open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- Proof-carrying active exceptional-zero data with the zero location and
its power-weight gap separated definitionally. -/
structure ExceptionalZeroGapAttestation
    (Q : ℕ)
    (ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop) where
  slot : StructurallyAdmissibleActiveSlot Q
  beta : ℝ
  beta_pos : 0 < beta
  beta_lt_one : beta < 1
  attested : ExceptionalZeroAt slot beta

/-- The exponent consumed by `powerWeight` is the zero gap, not the zero
location. -/
def ExceptionalZeroGapAttestation.zeroGap
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt) : ℝ :=
  1 - d.beta

theorem zeroGap_pos
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt) :
    0 < d.zeroGap := by
  unfold ExceptionalZeroGapAttestation.zeroGap
  linarith [d.beta_lt_one]

theorem zeroGap_nonneg
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt) :
    0 ≤ d.zeroGap :=
  (zeroGap_pos d).le

theorem zeroGap_lt_one
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt) :
    d.zeroGap < 1 := by
  unfold ExceptionalZeroGapAttestation.zeroGap
  linarith [d.beta_pos]

theorem zeroGap_le_one
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt) :
    d.zeroGap ≤ 1 :=
  (zeroGap_lt_one d).le

/-- Kernel-level semantic identity required by the source correction. -/
theorem powerWeight_zeroGap_eq_beta_sub_one
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt) (n : ℕ) :
    powerWeight d.zeroGap n = (n : ℝ) ^ (d.beta - 1) := by
  unfold powerWeight ExceptionalZeroGapAttestation.zeroGap
  congr 1
  ring

/-- The old direct substitution `b := beta` agrees with the required gap
only at beta=1/2. -/
theorem beta_eq_zeroGap_iff_eq_half (beta : ℝ) :
    beta = 1 - beta ↔ beta = 1 / 2 := by
  constructor <;> intro h <;> linarith

theorem beta_ne_zeroGap_of_half_lt (beta : ℝ) (hbeta : 1 / 2 < beta) :
    beta ≠ 1 - beta := by
  intro h
  have := (beta_eq_zeroGap_iff_eq_half beta).mp h
  linarith

/-- Corrected proof-carrying branch decision. -/
inductive ExceptionalZeroGapCase
    (Q : ℕ)
    (ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop) : Type
  | absent
      (no_zero : ∀ (e : StructurallyAdmissibleActiveSlot Q) (beta : ℝ),
        0 < beta → beta < 1 → ¬ ExceptionalZeroAt e beta)
  | active (data : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)

end GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263

