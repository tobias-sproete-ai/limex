import GoldbachCircleMethodLocalizedReducedPairSupportV18306
import GoldbachCircleMethodLocalizedAdjustedExactDichotomyV18307

/-!
# Goldbach V1.8.308: localized reduced-pair exact factorization

On the canonical plateau, the localized-localized channel is factored exactly
into the square of the active totient ratio and a finite reduced-residue pair
sum carrying the literal spatial powers and primitive character values.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLocalizedReducedPairExactFactorizationV18308

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodExceptionalWeightBoundaryV18128
open GoldbachCircleMethodBlockPairCarrierV18227
open GoldbachCircleMethodAdjustedModelFourChannelPartitionV18292
open GoldbachCircleMethodLocalizedReducedPairSupportV18306
open GoldbachCircleMethodLocalizedAdjustedExactDichotomyV18307

/-- The active-conductor scalar carried by each localized adjusted factor. -/
noncomputable def localizedTotientScale {Q : ℕ}
    (active : PositiveLevel Q) : ℂ :=
  (active.val : ℂ) / (active.val.totient : ℂ)

/-- Literal exceptional-character shape of a reduced residue pair. -/
noncomputable def localizedReducedPairShape {Q : ℕ}
    (e : CharacterSlot Q) (N n : ℕ) (b : ℝ) : ℂ :=
  (1 - (powerWeight b n : ℂ) * e.2.val (n : ZMod e.1.val)) *
    (1 - (powerWeight b (N - n) : ℂ) *
      e.2.val ((N - n : ℕ) : ZMod e.1.val))

/-- Pointwise exact reduced-pair normal form, including the zero branch. -/
theorem localizedLocalizedKernel_canonical_eq_ite
    {Q : ℕ} (hQ : 1 ≤ Q) (e : CharacterSlot Q)
    (N n : ℕ) (b R : ℝ) (hR : 1 < R)
    (hactiveR : (e.1.val : ℝ) ≤ R) :
    localizedLocalizedKernel hQ e N n b
        (logWeight R canonicalLogBump) =
      if Nat.Coprime n e.1.val ∧ Nat.Coprime (N - n) e.1.val then
        localizedTotientScale e.1 * localizedTotientScale e.1 *
          localizedReducedPairShape e N n b
      else 0 := by
  by_cases hpair :
      Nat.Coprime n e.1.val ∧ Nat.Coprime (N - n) e.1.val
  · rw [if_pos hpair]
    unfold localizedLocalizedKernel localizedTotientScale
      localizedReducedPairShape
    rw [divisorLocalizedAdjustedFactor_canonical_eq_of_coprime
      hQ e.1 e.2 n hpair.1 b R hR hactiveR]
    rw [divisorLocalizedAdjustedFactor_canonical_eq_of_coprime
      hQ e.1 e.2 (N - n) hpair.2 b R hR hactiveR]
    ring
  · rw [if_neg hpair]
    exact localizedLocalizedKernel_canonical_eq_zero_of_not_pair_coprime
      hQ e N n hpair b R hR hactiveR

/-- The finite reduced-residue shape sum on the literal pair carrier. -/
noncomputable def localizedReducedPairShapeSum {Q : ℕ}
    (J : Finset ℕ) (e : CharacterSlot Q) (N : ℕ) (b : ℝ) : ℂ :=
  ∑ n ∈ (pairFirstCarrier J N).filter
      (fun n => Nat.Coprime n e.1.val ∧ Nat.Coprime (N - n) e.1.val),
    localizedReducedPairShape e N n b

/-- Exact factorization of the full localized-localized pair channel. -/
theorem localizedLocalizedPairSum_canonical_eq_scale_mul_reducedShapeSum
    {Q : ℕ} (hQ : 1 ≤ Q) (J : Finset ℕ) (e : CharacterSlot Q)
    (N : ℕ) (b R : ℝ) (hR : 1 < R)
    (hactiveR : (e.1.val : ℝ) ≤ R) :
    localizedLocalizedPairSum hQ J e N b
        (logWeight R canonicalLogBump) =
      localizedTotientScale e.1 * localizedTotientScale e.1 *
        localizedReducedPairShapeSum J e N b := by
  rw [localizedLocalizedPairSum_canonical_eq_reducedPairs
    hQ J e N b R hR hactiveR]
  unfold localizedReducedPairShapeSum
  calc
    _ = ∑ n ∈ (pairFirstCarrier J N).filter
          (fun n => Nat.Coprime n e.1.val ∧
            Nat.Coprime (N - n) e.1.val),
        localizedTotientScale e.1 * localizedTotientScale e.1 *
          localizedReducedPairShape e N n b := by
      apply Finset.sum_congr rfl
      intro n hn
      have hpair := (Finset.mem_filter.mp hn).2
      rw [localizedLocalizedKernel_canonical_eq_ite
        hQ e N n b R hR hactiveR, if_pos hpair]
    _ = localizedTotientScale e.1 * localizedTotientScale e.1 *
        ∑ n ∈ (pairFirstCarrier J N).filter
          (fun n => Nat.Coprime n e.1.val ∧
            Nat.Coprime (N - n) e.1.val),
          localizedReducedPairShape e N n b := by
      rw [Finset.mul_sum]

end GoldbachCircleMethodLocalizedReducedPairExactFactorizationV18308
