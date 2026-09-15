import GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292
import GoldbachCircleMethodNoncoprimeLocalizedAdjustedVanishingV18305

/-!
# Goldbach V1.8.306: localized reduced-pair support

The exact noncoprime vanishing theorem is propagated through the
localized-localized convolution.  Its support is reduced, without loss or
estimation, to pairs for which both coordinates are units modulo the active
conductor.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLocalizedReducedPairSupportV18306

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292
open GoldbachCircleMethodNoncoprimeLocalizedAdjustedVanishingV18305

/-- The localized-localized kernel vanishes unless both coordinates are
coprime to the active conductor. -/
theorem localizedLocalizedKernel_canonical_eq_zero_of_not_pair_coprime
    {Q : ℕ} (hQ : 1 ≤ Q) (e : CharacterSlot Q)
    (N n : ℕ)
    (hpair : ¬ (Nat.Coprime n e.1.val ∧ Nat.Coprime (N - n) e.1.val))
    (b R : ℝ) (hR : 1 < R) (hactiveR : (e.1.val : ℝ) ≤ R) :
    localizedLocalizedKernel hQ e N n b
        (logWeight R canonicalLogBump) = 0 := by
  unfold localizedLocalizedKernel
  by_cases hn : Nat.Coprime n e.1.val
  · have hcomp : ¬ Nat.Coprime (N - n) e.1.val := by
      intro h
      exact hpair ⟨hn, h⟩
    rw [divisorLocalizedAdjustedFactor_canonical_eq_zero_of_not_coprime
      hQ e.1 e.2 (N - n) hcomp b R hR hactiveR]
    simp
  · rw [divisorLocalizedAdjustedFactor_canonical_eq_zero_of_not_coprime
      hQ e.1 e.2 n hn b R hR hactiveR]
    simp

/-- Exact reduced-residue support projection of the localized-localized pair
sum. -/
theorem localizedLocalizedPairSum_canonical_eq_reducedPairs
    {Q : ℕ} (hQ : 1 ≤ Q) (J : Finset ℕ) (e : CharacterSlot Q)
    (N : ℕ) (b R : ℝ) (hR : 1 < R)
    (hactiveR : (e.1.val : ℝ) ≤ R) :
    localizedLocalizedPairSum hQ J e N b
        (logWeight R canonicalLogBump) =
      ∑ n ∈ (pairFirstCarrier J N).filter
          (fun n => Nat.Coprime n e.1.val ∧
            Nat.Coprime (N - n) e.1.val),
        localizedLocalizedKernel hQ e N n b
          (logWeight R canonicalLogBump) := by
  unfold localizedLocalizedPairSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hnCarrier
  by_cases hpair :
      Nat.Coprime n e.1.val ∧ Nat.Coprime (N - n) e.1.val
  · simp [hpair]
  · rw [if_neg hpair]
    exact localizedLocalizedKernel_canonical_eq_zero_of_not_pair_coprime
      hQ e N n hpair b R hR hactiveR

end GoldbachCircleMethodLocalizedReducedPairSupportV18306

