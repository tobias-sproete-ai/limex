import GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774

/-!
# V1.8.775: canonical actual q=3 profile ceiling and reserve-dominance decision

The exact centered residue-selector profile of V1.8.774 is finite.  This
module therefore constructs, on the unchanged actual von-Mangoldt source, its
canonical finite supremum ceiling without any external hypothesis.

The resulting Sinc debit is composed with the exact base reserve.  This gives
an unconditional lower envelope for the actual composite reserve and shows
that an eventual positive floor for that envelope implies the corresponding
actual-source floor.

Finiteness alone does not prove that the canonical debit is asymptotically
smaller than the base reserve.  Neither that dominance nor an unbounded
actual negative sequence is proved here.  The requested decision gate
therefore remains fail-closed and `proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical
open Filter Topology

namespace GoldbachCircleMethodActualQ3CanonicalProfileCeilingReserveDominanceDecisionV18775

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodUniformModelReserveCubicScaleV18639
open GoldbachCircleMethodActualQ3SplitPrefixBudgetV18735
open GoldbachCircleMethodActualQ3PrefixLocalDensityExtractionV18753
open GoldbachCircleMethodActualModelQ3PreLoweringRecombinationV18769
open GoldbachCircleMethodActualModelQ3CompositeReserveFloorDecisionV18770
open GoldbachCircleMethodActualQ3ResidueSelectorMainProfileAbsorptionV18774

/-- The complete prefix carrier is nonempty, including when `M = 0`. -/
theorem range_succ_nonempty (M : Nat) :
    (Finset.range M.succ).Nonempty := by
  exact ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ M)⟩

/-- Sharp canonical finite actual-source ceiling: the supremum of the
centered profile on the complete prefix carrier `0 <= k <= M`. -/
noncomputable def actualQ3CanonicalCenteredProfileCeiling
    (M n : Nat) : Real :=
  (Finset.range M.succ).sup' (range_succ_nonempty M)
    (fun k => ‖actualQ3CenteredResidueSelectorPairProfile M n k‖)

theorem actualQ3CanonicalCenteredProfileCeiling_nonneg
    (M n : Nat) :
    0 ≤ actualQ3CanonicalCenteredProfileCeiling M n := by
  unfold actualQ3CanonicalCenteredProfileCeiling
  have hmem : 0 ∈ Finset.range M.succ :=
    Finset.mem_range.mpr (Nat.zero_lt_succ M)
  exact (norm_nonneg
    (actualQ3CenteredResidueSelectorPairProfile M n 0)).trans
      (Finset.le_sup'
        (fun k => ‖actualQ3CenteredResidueSelectorPairProfile M n k‖) hmem)

/-- Every actual centered-profile coordinate is bounded by the canonical L1
ceiling.  This is finite source mathematics, not an asymptotic estimate. -/
theorem actualQ3CenteredResidueSelectorPairProfile_norm_le_canonicalCeiling
    (M n k : Nat) (hk : k ≤ M) :
    ‖actualQ3CenteredResidueSelectorPairProfile M n k‖ ≤
      actualQ3CanonicalCenteredProfileCeiling M n := by
  unfold actualQ3CanonicalCenteredProfileCeiling
  have hmem : k ∈ Finset.range M.succ := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
  exact Finset.le_sup'
    (fun j => ‖actualQ3CenteredResidueSelectorPairProfile M n j‖) hmem

/-- The previously open pointwise ceiling interface is now inhabited on the
literal actual source by a canonical finite quantity. -/
theorem actualQ3CanonicalCenteredProfileCeiling_isCeiling
    (M n : Nat) :
    ActualQ3CenteredResidueSelectorProfileCeiling M n
      (actualQ3CanonicalCenteredProfileCeiling M n) := by
  constructor
  · exact actualQ3CanonicalCenteredProfileCeiling_nonneg M n
  · intro k hk
    exact actualQ3CenteredResidueSelectorPairProfile_norm_le_canonicalCeiling
      M n k hk

/-- Canonical actual-source debit obtained from the sharp project Sinc
variation and the inhabited finite profile ceiling. -/
noncomputable def actualQ3CanonicalCenteredProfileDebit
    (M n : Nat) (q : PairedOddBase (oddProjectRadius M)) : Real :=
  actualQ3VariationScale M q *
    actualQ3CanonicalCenteredProfileCeiling M n

theorem actualQ3LocalDensityTriangularRemainder_norm_le_canonicalDebit
    {M n : Nat} (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M) :
    ‖actualQ3LocalDensityTriangularRemainder M q n‖ ≤
      actualQ3CanonicalCenteredProfileDebit M n q := by
  unfold actualQ3CanonicalCenteredProfileDebit
  exact actualQ3LocalDensityTriangularRemainder_norm_le_of_profileCeiling
    hM q hn (actualQ3CanonicalCenteredProfileCeiling_isCeiling M n)

/-- Literal lower envelope after paying the canonical actual-source debit. -/
noncomputable def actualQ3CanonicalProfileAbsorptionGap
    (M R n : Nat) (P : Real)
    (q : PairedOddBase (oddProjectRadius M)) : Real :=
  actualQ3ResidueSelectorBaseReserve M R n P q -
    actualQ3CanonicalCenteredProfileDebit M n q

/-- The canonical gap is an unconditional lower bound for the actual
composite reserve.  No sign is asserted for the gap itself. -/
theorem actualQ3CanonicalProfileAbsorptionGap_le_actualCompositeReserve
    {M R n : Nat} {P : Real}
    (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (hn : n ≤ M) :
    actualQ3CanonicalProfileAbsorptionGap M R n P q ≤
      actualModelQ3PreLoweringCompositeReserve M R n P q := by
  unfold actualQ3CanonicalProfileAbsorptionGap
    actualQ3CanonicalCenteredProfileDebit
  exact baseReserve_sub_profileDebit_le_actualCompositeReserve
    hM q hn (actualQ3CanonicalCenteredProfileCeiling_isCeiling M n)

/-- The exact remaining positive-floor obligation, now containing no free
profile ceiling. -/
def EventualActualQ3CanonicalProfileAbsorptionGapFloor
    (rho : Real) : Prop :=
  ∀ᶠ M : Nat in atTop,
    ∀ R : Nat, 1 ≤ R → 16 * R ^ 3 < M →
      ∀ q : PairedOddBase (oddProjectRadius M),
        ∀ n : Nat, 2 * n ∈ evenTargetBlock M → q.val.val = 3 →
          rho * (M : Real) ≤
            actualQ3CanonicalProfileAbsorptionGap M R n
              (cubicModelScale R) q

/-- A positive floor for the canonical lower envelope transports to the
literal actual-source composite reserve. -/
theorem eventualActualModelQ3CompositeReserveFloor_of_canonicalGapFloor
    (rho : Real)
    (hGap : EventualActualQ3CanonicalProfileAbsorptionGapFloor rho) :
    EventualActualModelQ3CompositeReserveFloor rho := by
  filter_upwards [hGap] with M hM
  intro R hR hScale q n hTarget hq
  have hMpos : 0 < M := by omega
  have hUpper :=
    ((mem_evenTargetBlock_iff M (2 * n)).mp hTarget).2.1
  have hn : n ≤ M := by omega
  exact (hM R hR hScale q n hTarget hq).trans
    (actualQ3CanonicalProfileAbsorptionGap_le_actualCompositeReserve
      hMpos q hn)

/-- The opposing actual-source negative sequence excludes every strictly
positive eventual floor for the canonical lower envelope as well. -/
theorem not_canonicalGapFloor_of_unbounded_actual_negative
    (rho : Real) (hrho : 0 < rho)
    (hnegative : UnboundedActualModelQ3CompositeReserveNegative) :
    ¬ EventualActualQ3CanonicalProfileAbsorptionGapFloor rho := by
  intro hGap
  exact
    (not_eventual_positive_floor_of_unbounded_actual_negative
      rho hrho hnegative)
      (eventualActualModelQ3CompositeReserveFloor_of_canonicalGapFloor
        rho hGap)

end GoldbachCircleMethodActualQ3CanonicalProfileCeilingReserveDominanceDecisionV18775
