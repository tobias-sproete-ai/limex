import GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698

/-!
# V1.8.699: exact lag decomposition of the factorized same-residue collision

This append-only module decomposes the exact V1.8.698 same-target-residue
collision into the diagonal and both orientations of strictly positive natural
lags `h*K`, where the pair-local period is `K=q*r`.  An explicit finite lag
carrier proves every endpoint and orientation; no truncated subtraction is
used without an accompanying strict-order and exact-divisibility proof.

The project specialization uses the unchanged product of the two actual
one-dimensional signed residue fibers.  No absolute value, smallness estimate,
asymptotic claim, global triangle inequality, global LCM, replacement weight,
moment estimate, or Goldbach conclusion is introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodFactorizedSameResidueCollisionExactLagDecompositionV18699

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualSignedTargetResidueFiberCenteredEnergyV18696
open GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698

/-- Exact factorized one-dimensional-product sequence from V1.8.698. -/
noncomputable def selectedPairFactorizedResidueSequence
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val)
    (n : Nat) : Real :=
  selectedPairOneFiberSignedResidueWeight M q n x *
    selectedPairOneFiberSignedResidueWeight M r n y

/-- Exact ordered same-residue collision sum in a finite natural target box. -/
noncomputable def finiteSameResidueCollision
    (M K : Nat) [NeZero K] (f : Nat → Real) : Real :=
  ∑ n ∈ Finset.range M.succ,
    ∑ m ∈ Finset.range M.succ,
      if (n : ZMod K) = (m : ZMod K) then f n * f m else 0

/-- Strict upper-triangle same-residue collision. -/
noncomputable def finiteStrictUpperSameResidueCollision
    (M K : Nat) [NeZero K] (f : Nat → Real) : Real :=
  ∑ n ∈ Finset.range M.succ,
    ∑ m ∈ Finset.range M.succ,
      if n < m ∧ (n : ZMod K) = (m : ZMod K) then f n * f m else 0

/-- Explicit carrier `(h,n)` for every strictly positive lag `h*K` whose two
endpoints `n` and `n+h*K` lie in the target box. -/
def positiveKSpacedLagCarrier (M K : Nat) : Finset (Nat × Nat) :=
  ((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun hn => 0 < hn.1 ∧ hn.2 + hn.1 * K ≤ M)

/-- Exact positive-lag sum over the explicit endpoint-safe carrier. -/
noncomputable def finitePositiveKSpacedLagSum
    (M K : Nat) (f : Nat → Real) : Real :=
  ∑ hn ∈ positiveKSpacedLagCarrier M K,
    f hn.2 * f (hn.2 + hn.1 * K)

/-- Equality of natural casts in `ZMod K`, under strict order, is equivalent
to a unique-form positive natural lag multiple. -/
theorem natCast_zmod_eq_iff_exists_positive_lag_of_lt
    (K n m : Nat) (_hK : 0 < K) (hnm : n < m) :
    ((n : ZMod K) = (m : ZMod K)) ↔
      ∃ h : Nat, 0 < h ∧ m = n + h * K := by
  constructor
  · intro hcast
    have hmod : n ≡ m [MOD K] :=
      (ZMod.natCast_eq_natCast_iff n m K).mp hcast
    have hdvd : K ∣ m - n :=
      (Nat.modEq_iff_dvd' (Nat.le_of_lt hnm)).mp hmod
    let h := (m - n) / K
    have hexact : h * K = m - n := Nat.div_mul_cancel hdvd
    have hdiff : 0 < m - n := Nat.sub_pos_of_lt hnm
    have hmul : 0 < h * K := by simpa only [hexact] using hdiff
    have hh : 0 < h := Nat.pos_of_mul_pos_right hmul
    refine ⟨h, hh, ?_⟩
    omega
  · rintro ⟨h, _hh, rfl⟩
    push_cast
    simp

/-- Upper same-residue ordered-pair carrier used for the exact bijection. -/
def strictUpperSameResiduePairCarrier
    (M K : Nat) [NeZero K] : Finset (Nat × Nat) :=
  ((Finset.range M.succ).product (Finset.range M.succ)).filter
    (fun nm => nm.1 < nm.2 ∧ (nm.1 : ZMod K) = (nm.2 : ZMod K))

/-- The upper-pair to positive-lag coordinate map.  Its subtraction is only
used on the strict-upper carrier and is proved exactly divisible by `K`. -/
def upperPairToLag (K : Nat) (nm : Nat × Nat) : Nat × Nat :=
  ((nm.2 - nm.1) / K, nm.1)

/-- The inverse positive-lag endpoint map. -/
def lagToUpperPair (K : Nat) (hn : Nat × Nat) : Nat × Nat :=
  (hn.2, hn.2 + hn.1 * K)

theorem upperPairToLag_mem_positiveKSpacedLagCarrier
    (M K : Nat) [NeZero K] (hK : 0 < K)
    (nm : Nat × Nat) (hnm : nm ∈ strictUpperSameResiduePairCarrier M K) :
    upperPairToLag K nm ∈ positiveKSpacedLagCarrier M K := by
  rcases Finset.mem_filter.mp hnm with ⟨hbox, hlt, hcast⟩
  rcases Finset.mem_product.mp hbox with ⟨hnRange, hmRange⟩
  have hmod : nm.1 ≡ nm.2 [MOD K] :=
    (ZMod.natCast_eq_natCast_iff nm.1 nm.2 K).mp hcast
  have hdvd : K ∣ nm.2 - nm.1 :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hlt)).mp hmod
  have hexact : ((nm.2 - nm.1) / K) * K = nm.2 - nm.1 :=
    Nat.div_mul_cancel hdvd
  have hdiff : 0 < nm.2 - nm.1 := Nat.sub_pos_of_lt hlt
  have hmul : 0 < ((nm.2 - nm.1) / K) * K := by
    simpa only [hexact] using hdiff
  have hlag : 0 < (nm.2 - nm.1) / K := Nat.pos_of_mul_pos_right hmul
  have hlag_mul_le : ((nm.2 - nm.1) / K) * K ≤ M := by
    rw [hexact]
    have hmLe : nm.2 ≤ M :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hmRange)
    exact Nat.le_trans (Nat.sub_le _ _) hmLe
  have hendpoint :
      nm.1 + ((nm.2 - nm.1) / K) * K = nm.2 := by
    rw [hexact]
    exact Nat.add_sub_of_le (Nat.le_of_lt hlt)
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hleMul : (nm.2 - nm.1) / K ≤
          ((nm.2 - nm.1) / K) * K := Nat.le_mul_of_pos_right _ hK
      exact Nat.lt_succ_of_le (Nat.le_trans hleMul hlag_mul_le)
    · exact hnRange
  · dsimp [upperPairToLag]
    constructor
    · exact hlag
    · exact hendpoint.trans_le
        (Nat.le_of_lt_succ (Finset.mem_range.mp hmRange))

theorem lagToUpperPair_mem_strictUpperSameResiduePairCarrier
    (M K : Nat) [NeZero K] (hK : 0 < K)
    (hn : Nat × Nat) (hhn : hn ∈ positiveKSpacedLagCarrier M K) :
    lagToUpperPair K hn ∈ strictUpperSameResiduePairCarrier M K := by
  rcases Finset.mem_filter.mp hhn with ⟨hbox, hh, hend⟩
  rcases Finset.mem_product.mp hbox with ⟨hhRange, hnRange⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · exact hnRange
    · apply Finset.mem_range.mpr
      exact Nat.lt_succ_of_le hend
  · dsimp [lagToUpperPair]
    constructor
    · have hmul : 0 < hn.1 * K := Nat.mul_pos hh hK
      omega
    · push_cast
      simp

theorem lagToUpperPair_upperPairToLag
    (M K : Nat) [NeZero K] (_hK : 0 < K)
    (nm : Nat × Nat) (hnm : nm ∈ strictUpperSameResiduePairCarrier M K) :
    lagToUpperPair K (upperPairToLag K nm) = nm := by
  rcases Finset.mem_filter.mp hnm with ⟨_hbox, hlt, hcast⟩
  have hmod : nm.1 ≡ nm.2 [MOD K] :=
    (ZMod.natCast_eq_natCast_iff nm.1 nm.2 K).mp hcast
  have hdvd : K ∣ nm.2 - nm.1 :=
    (Nat.modEq_iff_dvd' (Nat.le_of_lt hlt)).mp hmod
  have hexact : ((nm.2 - nm.1) / K) * K = nm.2 - nm.1 :=
    Nat.div_mul_cancel hdvd
  ext <;> dsimp [lagToUpperPair, upperPairToLag]
  omega

theorem upperPairToLag_lagToUpperPair
    (M K : Nat) [NeZero K] (hK : 0 < K)
    (hn : Nat × Nat) (hhn : hn ∈ positiveKSpacedLagCarrier M K) :
    upperPairToLag K (lagToUpperPair K hn) = hn := by
  rcases Finset.mem_filter.mp hhn with ⟨_hbox, _hh, _hend⟩
  ext
  · dsimp [upperPairToLag, lagToUpperPair]
    rw [Nat.add_sub_cancel_left]
    exact Nat.mul_div_cancel hn.1 hK
  · rfl

/-- Exact bijective reindexing of the strict upper same-residue collision by
positive natural lags and their left endpoints. -/
theorem finiteStrictUpperSameResidueCollision_eq_positiveLagSum
    (M K : Nat) [NeZero K] (hK : 0 < K) (f : Nat → Real) :
    finiteStrictUpperSameResidueCollision M K f =
      finitePositiveKSpacedLagSum M K f := by
  unfold finiteStrictUpperSameResidueCollision
    finitePositiveKSpacedLagSum
  rw [← Finset.sum_product (Finset.range M.succ) (Finset.range M.succ)
    (fun nm => if nm.1 < nm.2 ∧ (nm.1 : ZMod K) = (nm.2 : ZMod K)
      then f nm.1 * f nm.2 else 0)]
  rw [← Finset.sum_filter]
  change (∑ nm ∈ strictUpperSameResiduePairCarrier M K,
      f nm.1 * f nm.2) = _
  apply Finset.sum_bij' (fun nm _ => upperPairToLag K nm)
    (fun hn _ => lagToUpperPair K hn)
  · exact upperPairToLag_mem_positiveKSpacedLagCarrier M K hK
  · exact lagToUpperPair_mem_strictUpperSameResiduePairCarrier M K hK
  · exact lagToUpperPair_upperPairToLag M K hK
  · exact upperPairToLag_lagToUpperPair M K hK
  · intro nm hnm
    change f nm.1 * f nm.2 =
      f (lagToUpperPair K (upperPairToLag K nm)).1 *
        f (lagToUpperPair K (upperPairToLag K nm)).2
    rw [lagToUpperPair_upperPairToLag M K hK nm hnm]

/-- Exact symmetric decomposition of every ordered same-residue pair into the
diagonal and twice the strict upper triangle. -/
theorem finiteSameResidueCollision_eq_diagonal_add_two_upper
    (M K : Nat) [NeZero K] (f : Nat → Real) :
    finiteSameResidueCollision M K f =
      (∑ n ∈ Finset.range M.succ, f n ^ 2) +
        2 * finiteStrictUpperSameResidueCollision M K f := by
  unfold finiteSameResidueCollision finiteStrictUpperSameResidueCollision
  have hsplit (n m : Nat) :
      (if (n : ZMod K) = (m : ZMod K) then f n * f m else 0) =
        (if n = m then f n * f m else 0) +
          (if n < m ∧ (n : ZMod K) = (m : ZMod K) then f n * f m else 0) +
          (if m < n ∧ (n : ZMod K) = (m : ZMod K) then f n * f m else 0) := by
    by_cases hres : (n : ZMod K) = (m : ZMod K)
    · rcases lt_trichotomy n m with hlt | heq | hgt
      · simp [hres, hlt, ne_of_lt hlt, not_lt_of_ge (Nat.le_of_lt hlt)]
      · subst m
        simp
      · simp [hres, hgt, ne_of_gt hgt, not_lt_of_ge (Nat.le_of_lt hgt)]
    · have hne : n ≠ m := by
        intro heq
        subst m
        exact hres rfl
      simp [hres, hne]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hdiag :
      (∑ n ∈ Finset.range M.succ,
        ∑ m ∈ Finset.range M.succ,
          if n = m then f n * f m else 0) =
        ∑ n ∈ Finset.range M.succ, f n ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.sum_ite_eq]
    simp only [hn, if_true, pow_two]
  have hlower :
      (∑ n ∈ Finset.range M.succ,
        ∑ m ∈ Finset.range M.succ,
          if m < n ∧ (n : ZMod K) = (m : ZMod K) then f n * f m else 0) =
        ∑ n ∈ Finset.range M.succ,
          ∑ m ∈ Finset.range M.succ,
            if n < m ∧ (n : ZMod K) = (m : ZMod K) then f n * f m else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _hn
    apply Finset.sum_congr rfl
    intro m _hm
    by_cases hlt : n < m
    · by_cases hres : (n : ZMod K) = (m : ZMod K)
      · rw [if_pos ⟨hlt, hres.symm⟩, if_pos ⟨hlt, hres⟩]
        ring
      · have hres' : (m : ZMod K) ≠ (n : ZMod K) := by
          intro h
          exact hres h.symm
        rw [if_neg (fun h => hres' h.2), if_neg (fun h => hres h.2)]
    · rw [if_neg (fun h => hlt h.1), if_neg (fun h => hlt h.1)]
  rw [hdiag, hlower]
  ring

/-- Exact finite lag formula: diagonal plus both orientations of every
positive `K`-spaced lag, with all endpoints certified by the lag carrier. -/
theorem finiteSameResidueCollision_eq_diagonal_add_two_positiveLagSum
    (M K : Nat) [NeZero K] (hK : 0 < K) (f : Nat → Real) :
    finiteSameResidueCollision M K f =
      (∑ n ∈ Finset.range M.succ, f n ^ 2) +
        2 * finitePositiveKSpacedLagSum M K f := by
  rw [finiteSameResidueCollision_eq_diagonal_add_two_upper]
  rw [finiteStrictUpperSameResidueCollision_eq_positiveLagSum M K hK f]

/-- Project specialization of the exact lag decomposition for the unchanged
one-dimensional-product sequence. -/
theorem selectedPairCenteredTargetResidueFiberEnergy_eq_diagonal_lags_sub_meanSquare
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    selectedPairCenteredTargetResidueFiberEnergy M q r x y =
      (∑ n ∈ Finset.range M.succ,
          selectedPairFactorizedResidueSequence M q r x y n ^ 2) +
        2 * finitePositiveKSpacedLagSum M (q.val.val * r.val.val)
          (selectedPairFactorizedResidueSequence M q r x y) -
        (∑ n ∈ Finset.range M.succ,
          selectedPairFactorizedResidueSequence M q r x y n) ^ 2 /
            (q.val.val * r.val.val : Real) := by
  rw [selectedPairCenteredTargetResidueFiberEnergy_eq_factorizedCollision_sub_meanSquare]
  change finiteSameResidueCollision M (q.val.val * r.val.val)
      (selectedPairFactorizedResidueSequence M q r x y) -
        (∑ n ∈ Finset.range M.succ,
          selectedPairFactorizedResidueSequence M q r x y n) ^ 2 /
            (q.val.val * r.val.val : Real) = _
  rw [finiteSameResidueCollision_eq_diagonal_add_two_positiveLagSum]
  exact Nat.mul_pos (NeZero.pos q.val.val) (NeZero.pos r.val.val)

end GoldbachCircleMethodFactorizedSameResidueCollisionExactLagDecompositionV18699
