import GoldbachCircleMethodCanonicalLocalizedIntervalFactorizationV18310
import GoldbachCircleMethodAttestedVariableWeightIntervalReserveV18274

/-!
# Goldbach V1.8.311: canonical localized interval reserve

The proof-carrying zero-gap interval reserve is transported into the actual
canonical localized-localized channel.  The exact squared totient scale and
both previously audited losses remain visible.  No positivity of the final
right-hand side is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodCanonicalLocalizedIntervalReserveV18311

open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292
open GoldbachCircleMethodAttestedVariableWeightIntervalReserveV18274
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodCanonicalLocalizedIntervalFactorizationV18310
open GoldbachCircleMethodExceptionalZeroGapAttestationRepairV18263
open GoldbachCircleMethodLocalizedReducedPairExactFactorizationV18308
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258
open GoldbachCircleMethodActualUnitPairArithmeticV18194
open GoldbachCircleMethodZeroGapReserveScaleV18266

/-- The squared complex totient scale acts on real parts as the literal square
of the corresponding real ratio. -/
theorem localizedTotientScale_sq_mul_re
    {Q : ℕ} (active : PositiveLevel Q) (z : ℂ) :
    (localizedTotientScale active * localizedTotientScale active * z).re =
      ((active.val : ℝ) / (active.val.totient : ℝ)) *
        ((active.val : ℝ) / (active.val.totient : ℝ)) * z.re := by
  have hscale : localizedTotientScale active =
      (((active.val : ℝ) / (active.val.totient : ℝ) : ℝ) : ℂ) := by
    unfold localizedTotientScale
    norm_num
  rw [hscale]
  let a : ℝ := (active.val : ℝ) / (active.val.totient : ℝ)
  change (((a : ℂ) * (a : ℂ) * z).re = a * a * z.re)
  simp [Complex.mul_re, Complex.mul_im]

/-- Endpoint geometry of the exact block-pair interval supplies all carrier
hypotheses required by the variable-weight interval theorem. -/
theorem blockPair_interval_geometry
    (B N : ℕ) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N) :
    let A := blockPairLower B N
    let T := blockPairUpper B N - blockPairLower B N + 1
    A ≤ N ∧ A + T ≤ N + 1 ∧
      A ∈ blockCarrier B ∧ N - A ∈ blockCarrier B ∧
      (∀ i ∈ Finset.range T, A + i ∈ blockCarrier B) ∧
      (∀ i ∈ Finset.range T, N - (A + i) ∈ blockCarrier B) := by
  dsimp only
  have hB : 1 ≤ B := by
    have hI := hInterval
    unfold blockPairLower blockPairUpper at hI
    omega
  have hUN : blockPairUpper B N ≤ N := by
    unfold blockPairUpper
    omega
  have hA_mem : blockPairLower B N ∈ blockCarrier B := by
    have hIcc : blockPairLower B N ∈
        Finset.Icc (blockPairLower B N) (blockPairUpper B N) :=
      Finset.mem_Icc.mpr ⟨le_rfl, hInterval⟩
    have hp : blockPairLower B N ∈ pairFirstCarrier (blockCarrier B) N := by
      rw [pairFirstCarrier_block_eq_Icc B N hB hBN]
      exact hIcc
    exact (Finset.mem_filter.mp hp).1
  have hNA_mem : N - blockPairLower B N ∈ blockCarrier B := by
    have hIcc : blockPairLower B N ∈
        Finset.Icc (blockPairLower B N) (blockPairUpper B N) :=
      Finset.mem_Icc.mpr ⟨le_rfl, hInterval⟩
    have hp : blockPairLower B N ∈ pairFirstCarrier (blockCarrier B) N := by
      rw [pairFirstCarrier_block_eq_Icc B N hB hBN]
      exact hIcc
    exact (Finset.mem_filter.mp hp).2
  refine ⟨hInterval.trans hUN, ?_, hA_mem, hNA_mem, ?_, ?_⟩
  · calc
      blockPairLower B N +
          (blockPairUpper B N - blockPairLower B N + 1) =
          blockPairUpper B N + 1 := by
        rw [← Nat.add_assoc, Nat.add_sub_of_le hInterval]
      _ ≤ N + 1 := Nat.add_le_add_right hUN 1
  · intro i hi
    have hiT : i < blockPairUpper B N - blockPairLower B N + 1 :=
      Finset.mem_range.mp hi
    have hIcc : blockPairLower B N + i ∈
        Finset.Icc (blockPairLower B N) (blockPairUpper B N) := by
      simp only [Finset.mem_Icc]
      omega
    have hp : blockPairLower B N + i ∈
        pairFirstCarrier (blockCarrier B) N := by
      rw [pairFirstCarrier_block_eq_Icc B N hB hBN]
      exact hIcc
    exact (Finset.mem_filter.mp hp).1
  · intro i hi
    have hiT : i < blockPairUpper B N - blockPairLower B N + 1 :=
      Finset.mem_range.mp hi
    have hIcc : blockPairLower B N + i ∈
        Finset.Icc (blockPairLower B N) (blockPairUpper B N) := by
      simp only [Finset.mem_Icc]
      omega
    have hp : blockPairLower B N + i ∈
        pairFirstCarrier (blockCarrier B) N := by
      rw [pairFirstCarrier_block_eq_Icc B N hB hBN]
      exact hIcc
    exact (Finset.mem_filter.mp hp).2

/-- The actual canonical localized-localized block channel inherits the
proof-carrying interval reserve, scaled by the exact squared totient ratio.
The terminal and spatial-variation costs are not hidden or absorbed. -/
theorem canonical_localized_pair_reserve_with_costs
    {Q : ℕ}
    {ExceptionalZeroAt : StructurallyAdmissibleActiveSlot Q → ℝ → Prop}
    (hQ : 1 ≤ Q) (d : ExceptionalZeroGapAttestation Q ExceptionalZeroAt)
    (B N : ℕ) (R : ℝ)
    (hr3 : 3 < d.slot.val.1.val) (hEven : Even N)
    (hB : 4 ≤ B) (hBN : B ≤ N)
    (hInterval : blockPairLower B N ≤ blockPairUpper B N)
    (hR : 1 < R) (hactiveR : (d.slot.val.1.val : ℝ) ≤ R) :
    let T := blockPairUpper B N - blockPairLower B N + 1
    (((d.slot.val.1.val : ℝ) /
          (d.slot.val.1.val.totient : ℝ)) ^ 2) *
        ((((T / d.slot.val.1.val : ℕ) : ℝ) *
              ((unitPairCount d.slot.val.1.val (N : ℤ) : ℝ) *
                zeroGapReserveScale d.zeroGap B / 6) -
            4 * ((T % d.slot.val.1.val : ℕ) : ℝ) -
            8 * d.zeroGap * (T : ℝ) ^ 2 / (B : ℝ))) ≤
      (localizedLocalizedPairSum hQ (blockCarrier B) d.slot.val N
        d.zeroGap (logWeight R canonicalLogBump)).re := by
  dsimp only
  rcases blockPair_interval_geometry B N hBN hInterval with
    ⟨hAN, hend, hA, hNA, hleft, hright⟩
  have hbase := attested_variable_weight_interval_reserve_with_costs
    d N (blockPairLower B N)
      (blockPairUpper B N - blockPairLower B N + 1) B
      hr3 hEven hB hAN hend hA hNA hleft hright
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (sq_nonneg ((d.slot.val.1.val : ℝ) /
      (d.slot.val.1.val.totient : ℝ)))
  rw [localizedLocalizedPairSum_canonical_block_eq_scale_mul_variableInterval
    hQ B N d.slot.val d.zeroGap R hR hactiveR
      (by omega : 1 ≤ B) hBN hInterval]
  rw [localizedTotientScale_sq_mul_re]
  simpa only [pow_two] using hscaled

end GoldbachCircleMethodCanonicalLocalizedIntervalReserveV18311
