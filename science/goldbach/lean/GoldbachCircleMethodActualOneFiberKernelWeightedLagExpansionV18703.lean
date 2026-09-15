import GoldbachCircleMethodOneDimensionalAutocorrelationContractionV18700

/-!
# V1.8.703: actual one-fiber kernel as an exact weighted lag expansion

This append-only module opens the genuine V1.8.700 one-dimensional residue
kernel.  It first identifies the residue contraction with the exact ordered
same-residue collision of the unchanged V1.8.698 half-weights.  It then
decomposes that collision into the diagonal and both orientations of every
strictly positive base-spaced fiber lag.

The two target indices may differ, so the two lag orientations are retained
separately rather than being replaced by a factor of two.  The target gate,
odd--odd carrier, moving notch, `oddOddPairFiberMass`, and both sinc radii
remain inside `selectedPairOneFiberHalfWeight`.

No absolute value, global triangle inequality, global LCM, replacement
weight, smallness estimate, asymptotic claim, moment estimate, or Goldbach
conclusion is introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualOneFiberKernelWeightedLagExpansionV18703

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698
open GoldbachCircleMethodFactorizedSameResidueCollisionExactLagDecompositionV18699
open GoldbachCircleMethodOneDimensionalAutocorrelationContractionV18700

/-- Ordered cross-collision of two real sequences on the same residue class. -/
noncomputable def finiteSameResidueCrossCollision
    (M K : Nat) [NeZero K] (f g : Nat → Real) : Real :=
  ∑ a ∈ Finset.range M.succ,
    ∑ b ∈ Finset.range M.succ,
      if (a : ZMod K) = (b : ZMod K) then f a * g b else 0

/-- Both orientations of every endpoint-safe strictly positive `K`-spaced
lag.  They cannot be merged when `f` and `g` differ. -/
noncomputable def finitePositiveKSpacedCrossLagSum
    (M K : Nat) (f g : Nat → Real) : Real :=
  ∑ ha ∈ positiveKSpacedLagCarrier M K,
    (f ha.2 * g (ha.2 + ha.1 * K) +
      f (ha.2 + ha.1 * K) * g ha.2)

/-- Exact contraction of two residue buckets to an ordered same-residue
cross-collision. -/
theorem sum_residueBuckets_mul_eq_sameResidueCrossCollision
    (M K : Nat) [NeZero K] (f g : Nat → Real) :
    (∑ x : ZMod K,
      (∑ a ∈ Finset.range M.succ,
        if (a : ZMod K) = x then f a else 0) *
      (∑ b ∈ Finset.range M.succ,
        if (b : ZMod K) = x then g b else 0)) =
      finiteSameResidueCrossCollision M K f g := by
  unfold finiteSameResidueCrossCollision
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hab : (a : ZMod K) = (b : ZMod K)
  · rw [if_pos hab]
    rw [← hab]
    simp
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro x _hx
    by_cases hax : (a : ZMod K) = x
    · have hbx : (b : ZMod K) ≠ x := by
        intro h
        exact hab (hax.trans h.symm)
      simp [hax, hbx]
    · simp [hax]

/-- The actual V1.8.700 one-fiber residue kernel is exactly the ordered
same-residue collision of the two literal one-fiber half-weight sequences. -/
theorem selectedPairOneFiberResidueKernel_eq_sameResidueCrossCollision
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n m : Nat) :
    selectedPairOneFiberResidueKernel M q n m =
      finiteSameResidueCrossCollision M q.val.val
        (selectedPairOneFiberHalfWeight M q n)
        (selectedPairOneFiberHalfWeight M q m) := by
  unfold selectedPairOneFiberResidueKernel
    selectedPairOneFiberSignedResidueWeight
  exact sum_residueBuckets_mul_eq_sameResidueCrossCollision M q.val.val
    (selectedPairOneFiberHalfWeight M q n)
    (selectedPairOneFiberHalfWeight M q m)

/-- Exact diagonal plus two-orientation positive-lag decomposition of a
same-residue cross-collision. -/
theorem finiteSameResidueCrossCollision_eq_diagonal_add_positiveCrossLags
    (M K : Nat) [NeZero K] (hK : 0 < K) (f g : Nat → Real) :
    finiteSameResidueCrossCollision M K f g =
      (∑ a ∈ Finset.range M.succ, f a * g a) +
        finitePositiveKSpacedCrossLagSum M K f g := by
  unfold finiteSameResidueCrossCollision finitePositiveKSpacedCrossLagSum
  have hsplit (a b : Nat) :
      (if (a : ZMod K) = (b : ZMod K) then f a * g b else 0) =
        (if a = b then f a * g b else 0) +
        (if a < b ∧ (a : ZMod K) = (b : ZMod K) then f a * g b else 0) +
        (if b < a ∧ (a : ZMod K) = (b : ZMod K) then f a * g b else 0) := by
    by_cases hres : (a : ZMod K) = (b : ZMod K)
    · rcases lt_trichotomy a b with hlt | heq | hgt
      · simp [hres, hlt, ne_of_lt hlt,
          not_lt_of_ge (Nat.le_of_lt hlt)]
      · subst b
        simp
      · simp [hres, hgt, ne_of_gt hgt,
          not_lt_of_ge (Nat.le_of_lt hgt)]
    · have hne : a ≠ b := by
        intro heq
        subst b
        exact hres rfl
      simp [hres, hne]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hdiag :
      (∑ a ∈ Finset.range M.succ,
        ∑ b ∈ Finset.range M.succ,
          if a = b then f a * g b else 0) =
        ∑ a ∈ Finset.range M.succ, f a * g a := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_ite_eq]
    simp [ha]
  rw [hdiag]
  let upperWeight : Nat × Nat → Real := fun ab => f ab.1 * g ab.2
  let lowerWeight : Nat × Nat → Real := fun ab => f ab.2 * g ab.1
  have hupper :
      (∑ a ∈ Finset.range M.succ,
        ∑ b ∈ Finset.range M.succ,
          if a < b ∧ (a : ZMod K) = (b : ZMod K)
          then f a * g b else 0) =
        ∑ ha ∈ positiveKSpacedLagCarrier M K,
          f ha.2 * g (ha.2 + ha.1 * K) := by
    rw [← Finset.sum_product (Finset.range M.succ) (Finset.range M.succ)
      (fun ab => if ab.1 < ab.2 ∧
        (ab.1 : ZMod K) = (ab.2 : ZMod K)
        then f ab.1 * g ab.2 else 0)]
    rw [← Finset.sum_filter]
    change (∑ ab ∈ strictUpperSameResiduePairCarrier M K,
      upperWeight ab) = _
    apply Finset.sum_bij' (fun ab _ => upperPairToLag K ab)
      (fun ha _ => lagToUpperPair K ha)
    · exact upperPairToLag_mem_positiveKSpacedLagCarrier M K hK
    · exact lagToUpperPair_mem_strictUpperSameResiduePairCarrier M K hK
    · exact lagToUpperPair_upperPairToLag M K hK
    · exact upperPairToLag_lagToUpperPair M K hK
    · intro ab hab
      change upperWeight ab =
        f (lagToUpperPair K (upperPairToLag K ab)).1 *
          g (lagToUpperPair K (upperPairToLag K ab)).2
      rw [lagToUpperPair_upperPairToLag M K hK ab hab]
  have hlower :
      (∑ a ∈ Finset.range M.succ,
        ∑ b ∈ Finset.range M.succ,
          if b < a ∧ (a : ZMod K) = (b : ZMod K)
          then f a * g b else 0) =
        ∑ ha ∈ positiveKSpacedLagCarrier M K,
          f (ha.2 + ha.1 * K) * g ha.2 := by
    have hswap :
        (∑ a ∈ Finset.range M.succ,
          ∑ b ∈ Finset.range M.succ,
            if b < a ∧ (a : ZMod K) = (b : ZMod K)
            then f a * g b else 0) =
          ∑ a ∈ Finset.range M.succ,
            ∑ b ∈ Finset.range M.succ,
              if a < b ∧ (a : ZMod K) = (b : ZMod K)
              then f b * g a else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hlt : a < b
      · by_cases hres : (a : ZMod K) = (b : ZMod K)
        · rw [if_pos ⟨hlt, hres.symm⟩, if_pos ⟨hlt, hres⟩]
        · have hres' : (b : ZMod K) ≠ (a : ZMod K) := by
            intro h
            exact hres h.symm
          rw [if_neg (fun h => hres' h.2),
            if_neg (fun h => hres h.2)]
      · rw [if_neg (fun h => hlt h.1), if_neg (fun h => hlt h.1)]
    rw [hswap]
    rw [← Finset.sum_product (Finset.range M.succ) (Finset.range M.succ)
      (fun ab => if ab.1 < ab.2 ∧
        (ab.1 : ZMod K) = (ab.2 : ZMod K)
        then f ab.2 * g ab.1 else 0)]
    rw [← Finset.sum_filter]
    change (∑ ab ∈ strictUpperSameResiduePairCarrier M K,
      lowerWeight ab) = _
    apply Finset.sum_bij' (fun ab _ => upperPairToLag K ab)
      (fun ha _ => lagToUpperPair K ha)
    · exact upperPairToLag_mem_positiveKSpacedLagCarrier M K hK
    · exact lagToUpperPair_mem_strictUpperSameResiduePairCarrier M K hK
    · exact lagToUpperPair_upperPairToLag M K hK
    · exact upperPairToLag_lagToUpperPair M K hK
    · intro ab hab
      change lowerWeight ab =
        f (lagToUpperPair K (upperPairToLag K ab)).2 *
          g (lagToUpperPair K (upperPairToLag K ab)).1
      rw [lagToUpperPair_upperPairToLag M K hK ab hab]
  rw [hupper, hlower]
  ring

/-- Final project specialization.  The opaque one-dimensional kernel is
replaced by the exact diagonal and both orientations of every positive
`q`-spaced fiber lag of the literal half-weights. -/
theorem selectedPairOneFiberResidueKernel_eq_weightedLagExpansion
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n m : Nat) :
    selectedPairOneFiberResidueKernel M q n m =
      (∑ a ∈ Finset.range M.succ,
        selectedPairOneFiberHalfWeight M q n a *
          selectedPairOneFiberHalfWeight M q m a) +
      finitePositiveKSpacedCrossLagSum M q.val.val
        (selectedPairOneFiberHalfWeight M q n)
        (selectedPairOneFiberHalfWeight M q m) := by
  rw [selectedPairOneFiberResidueKernel_eq_sameResidueCrossCollision]
  exact finiteSameResidueCrossCollision_eq_diagonal_add_positiveCrossLags
    M q.val.val (NeZero.pos q.val.val)
    (selectedPairOneFiberHalfWeight M q n)
    (selectedPairOneFiberHalfWeight M q m)

end GoldbachCircleMethodActualOneFiberKernelWeightedLagExpansionV18703
