import GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691

/-!
# V1.8.692: exact even-target step-two reindex for selected pairs

The V1.8.690 selected-pair correlation is reindexed without changing its
literal target or fiber carriers.  Every even target is written as `2*n` and
every even odd--odd fiber as `2*a` or `2*b`.  The resulting weight retains the
target-block indicator, both original odd--odd carrier indicators, both moving
off-diagonal notches, both `oddOddPairFiberMass` factors, and all four distinct
sinc radii contained in the two exact selected-pair weights.

For fixed distinct selected denominators, the local atom is sampled along
`x = 2 * (n-b)` in `ZMod (q*r)`.  Since the pair-local product period is odd,
this step-two affine map permutes the complete residue system.  The exact
complete-period cancellation and the corresponding incomplete-prefix ceiling
therefore survive the true even-target parametrization.  Finite Abel summation
then exposes the literal terminal-weight and total-variation obligations.  No
smallness of either obligation is asserted.

No global LCM, coprimality of `q,r`, model weight, cardinality estimate,
minor-arc estimate, exceptional-set result, or Goldbach conclusion is added.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSelectedPairEvenTargetReindexV18692

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodFullChannelPartitionedGramV18689
open GoldbachCircleMethodSelectedPairCrossCorrelationExpansionV18690
open GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691
open GoldbachCircleMethodActualCompanionIntervalTransferV18205

/-- Exact half-index carrier for the literal even target block. -/
def halfEvenTargetCarrier (M : Nat) : Finset Nat :=
  (Finset.range M.succ).filter (fun n => 2 * n ∈ evenTargetBlock M)

/-- Exact half-index carrier for one literal even odd--odd fiber carrier. -/
def halfOddOddOffDiagonalFiberCarrier (M N : Nat) : Finset Nat :=
  (Finset.range M.succ).filter
    (fun a => 2 * a ∈ oddOddOffDiagonalSumCarrier M N)

/-- Doubling the half target carrier gives exactly the original target block. -/
theorem image_two_halfEvenTargetCarrier (M : Nat) :
    (halfEvenTargetCarrier M).image (fun n => 2 * n) = evenTargetBlock M := by
  ext N
  constructor
  · intro hN
    rcases Finset.mem_image.mp hN with ⟨n, hn, rfl⟩
    exact (Finset.mem_filter.mp hn).2
  · intro hN
    have hdata := (mem_evenTargetBlock_iff M N).mp hN
    rcases hdata.2.2.1 with ⟨n, hn⟩
    have hNtwo : N = 2 * n := by omega
    apply Finset.mem_image.mpr
    refine ⟨n, ?_, hNtwo.symm⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      omega
    · simpa only [hNtwo] using hN

/-- Doubling the half fiber carrier gives exactly the original retained
off-diagonal fiber carrier. -/
theorem image_two_halfOddOddOffDiagonalFiberCarrier (M N : Nat) :
    (halfOddOddOffDiagonalFiberCarrier M N).image (fun a => 2 * a) =
      oddOddOffDiagonalSumCarrier M N := by
  ext t
  constructor
  · intro ht
    rcases Finset.mem_image.mp ht with ⟨a, ha, rfl⟩
    exact (Finset.mem_filter.mp ha).2
  · intro ht
    have hdata := (mem_oddOddOffDiagonalSumCarrier_iff M N t).mp ht
    rcases hdata.2.1 with ⟨a, ha⟩
    have httwo : t = 2 * a := by omega
    apply Finset.mem_image.mpr
    refine ⟨a, ?_, httwo.symm⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      omega
    · simpa only [httwo] using ht

/-- Exact finite target reindexing. -/
theorem sum_evenTargetBlock_eq_half
    {A : Type} [AddCommMonoid A] (M : Nat) (f : Nat → A) :
    (∑ N ∈ evenTargetBlock M, f N) =
      ∑ n ∈ halfEvenTargetCarrier M, f (2 * n) := by
  rw [← image_two_halfEvenTargetCarrier M]
  rw [Finset.sum_image]
  intro a _ha b _hb hab
  change 2 * a = 2 * b at hab
  omega

/-- Exact finite fiber reindexing. -/
theorem sum_oddOddOffDiagonalFiber_eq_half
    {A : Type} [AddCommMonoid A] (M N : Nat) (f : Nat → A) :
    (∑ t ∈ oddOddOffDiagonalSumCarrier M N, f t) =
      ∑ a ∈ halfOddOddOffDiagonalFiberCarrier M N, f (2 * a) := by
  rw [← image_two_halfOddOddOffDiagonalFiberCarrier M N]
  rw [Finset.sum_image]
  intro a _ha b _hb hab
  change 2 * a = 2 * b at hab
  omega

/-- The original off-diagonal carrier is exactly the original even carrier
plus its moving notch. -/
theorem mem_oddOddOffDiagonalSumCarrier_iff_sumCarrier_and_ne
    (M N t : Nat) :
    t ∈ oddOddOffDiagonalSumCarrier M N ↔
      t ∈ oddOddSumCarrier M ∧ t ≠ N := by
  simp [oddOddOffDiagonalSumCarrier]

/-- Literal half-index weight for one fixed selected denominator pair.  Its
single Boolean gate visibly retains the target block, both original fiber
carriers and both moving notches.  The true fiber masses and all four sinc
radii remain inside the two exact weights. -/
noncomputable def selectedPairHalfExactWeight
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n a b : Nat) : Real :=
  if 2 * n ∈ evenTargetBlock M ∧
      2 * a ∈ oddOddSumCarrier M ∧ 2 * a ≠ 2 * n ∧
      2 * b ∈ oddOddSumCarrier M ∧ 2 * b ≠ 2 * n then
    selectedPairExactSincFiberWeight M q (2 * n) (2 * a) *
      selectedPairExactSincFiberWeight M r (2 * n) (2 * b)
  else 0

/-- The exact local atom sampled at the real even-target coordinate
`x = 2*(n-b)` in the pair-local ring.  There is no truncated natural
subtraction. -/
noncomputable def selectedPairEvenStepAtom
    {R : Nat} (q r : PairedOddBase R) (n a b : Nat) : Real :=
  let K := q.val.val * r.val.val
  let hq : q.val.val ∣ K := Nat.dvd_mul_right _ _
  let hr : r.val.val ∣ K := Nat.dvd_mul_left _ _
  localPairMixedRamanujanRealAtom hq hr
    ((2 * a : Nat) : ZMod K) ((2 * b : Nat) : ZMod K)
    ((2 : ZMod K) * ((n : ZMod K) - (b : ZMod K)))

/-- The literal pair of Ramanujan atoms at `N=2n,t=2a,u=2b` is exactly the
step-two local atom. -/
theorem selectedPairRamanujanAtoms_even_eq_evenStepAtom
    {R : Nat} (q r : PairedOddBase R) (n a b : Nat) :
    selectedPairRamanujanAtom q (2 * n) (2 * a) *
        selectedPairRamanujanAtom r (2 * n) (2 * b) =
      selectedPairEvenStepAtom q r n a b := by
  let K := q.val.val * r.val.val
  let _ : NeZero K :=
    ⟨Nat.mul_ne_zero (NeZero.ne q.val.val) (NeZero.ne r.val.val)⟩
  have h :=
    selectedPairRamanujanAtoms_mul_eq_localPairMixedRamanujanRealAtom
      (K := K) q r (Nat.dvd_mul_right _ _) (Nat.dvd_mul_left _ _)
        (2 * n) (2 * a) (2 * b)
  rw [h]
  unfold selectedPairEvenStepAtom
  dsimp only [K]
  congr 2
  push_cast
  ring

/-- The fully literal half-grid summand. -/
noncomputable def selectedPairHalfGridTerm
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n a b : Nat) : Real :=
  selectedPairEvenStepAtom q r n a b *
    selectedPairHalfExactWeight M q r n a b

/-- On the admitted literal carriers, the product of the two original fiber
terms is exactly the half-grid summand. -/
theorem projectPairedBaseFiberTerms_even_eq_halfGridTerm
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (n a b : Nat)
    (hN : 2 * n ∈ evenTargetBlock M)
    (ha : 2 * a ∈ oddOddOffDiagonalSumCarrier M (2 * n))
    (hb : 2 * b ∈ oddOddOffDiagonalSumCarrier M (2 * n)) :
    projectPairedBaseFiberTerm M q (2 * n) (2 * a) *
        projectPairedBaseFiberTerm M r (2 * n) (2 * b) =
      selectedPairHalfGridTerm M q r n a b := by
  have hEven : Even (2 * n) := ⟨n, by omega⟩
  rw [projectPairedBaseFiberTerm_mul_eq_atoms_mul_exactWeights
    M q r (2 * n) (2 * a) (2 * b) hEven ha hb]
  rw [selectedPairRamanujanAtoms_even_eq_evenStepAtom]
  unfold selectedPairHalfGridTerm selectedPairHalfExactWeight
  have ha' := (mem_oddOddOffDiagonalSumCarrier_iff_sumCarrier_and_ne
    M (2 * n) (2 * a)).mp ha
  have hb' := (mem_oddOddOffDiagonalSumCarrier_iff_sumCarrier_and_ne
    M (2 * n) (2 * b)).mp hb
  simp [hN, ha'.1, ha'.2, hb'.1, hb'.2]

/-- Exact full `N,t,u` to `n,a,b` reindex for one ordered selected pair.  The
right side ranges over fixed boxes; every original carrier and moving notch is
retained inside `selectedPairHalfExactWeight`. -/
theorem selectedPairCrossFiberSum_eq_halfGrid
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    (∑ N ∈ evenTargetBlock M,
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        ∑ u ∈ oddOddOffDiagonalSumCarrier M N,
          projectPairedBaseFiberTerm M q N t *
            projectPairedBaseFiberTerm M r N u) =
      ∑ n ∈ Finset.range M.succ,
        ∑ a ∈ Finset.range M.succ,
          ∑ b ∈ Finset.range M.succ,
            selectedPairHalfGridTerm M q r n a b := by
  rw [sum_evenTargetBlock_eq_half]
  rw [halfEvenTargetCarrier, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hnRange
  by_cases hN : 2 * n ∈ evenTargetBlock M
  · simp only [hN, if_true]
    rw [sum_oddOddOffDiagonalFiber_eq_half]
    rw [halfOddOddOffDiagonalFiberCarrier, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _haRange
    by_cases ha : 2 * a ∈ oddOddOffDiagonalSumCarrier M (2 * n)
    · simp only [ha, if_true]
      rw [sum_oddOddOffDiagonalFiber_eq_half]
      rw [halfOddOddOffDiagonalFiberCarrier, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _hbRange
      by_cases hb : 2 * b ∈ oddOddOffDiagonalSumCarrier M (2 * n)
      · simp only [hb, if_true]
        exact projectPairedBaseFiberTerms_even_eq_halfGridTerm
          M q r n a b hN ha hb
      · simp only [hb, if_false]
        unfold selectedPairHalfGridTerm selectedPairHalfExactWeight
        rw [if_neg]
        · simp
        · intro hgate
          apply hb
          exact (mem_oddOddOffDiagonalSumCarrier_iff_sumCarrier_and_ne
            M (2 * n) (2 * b)).mpr ⟨hgate.2.2.2.1, hgate.2.2.2.2⟩
    · simp only [ha, if_false]
      symm
      apply Finset.sum_eq_zero
      intro b _hbRange
      unfold selectedPairHalfGridTerm selectedPairHalfExactWeight
      rw [if_neg]
      · simp
      · intro hgate
        apply ha
        exact (mem_oddOddOffDiagonalSumCarrier_iff_sumCarrier_and_ne
          M (2 * n) (2 * a)).mpr ⟨hgate.2.1, hgate.2.2.1⟩
  · simp only [hN, if_false]
    symm
    apply Finset.sum_eq_zero
    intro a _haRange
    apply Finset.sum_eq_zero
    intro b _hbRange
    simp [selectedPairHalfGridTerm, selectedPairHalfExactWeight, hN]

/-- Exact correlation-level binding to the half-grid.  This is the literal
V1.8.689 finite correlation, not a newly postulated interface. -/
theorem finiteCorrelation_projectPairedBaseContribution_eq_halfGrid
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    finiteCorrelation (evenTargetBlock M)
        (projectPairedBaseContribution M q)
        (projectPairedBaseContribution M r) =
      ∑ n ∈ Finset.range M.succ,
        ∑ a ∈ Finset.range M.succ,
          ∑ b ∈ Finset.range M.succ,
            selectedPairHalfGridTerm M q r n a b := by
  rw [finiteCorrelation_projectPairedBaseContribution_eq_ntu]
  exact selectedPairCrossFiberSum_eq_halfGrid M q r

/-- The complete ordered selected-pair off-diagonal Gram term in exact
step-two target coordinates.  The `erase` witness remains the sole distinctness
condition; no coprimality is introduced. -/
theorem orderedOffDiagonalGram_eq_halfGrid (M : Nat) :
    orderedOffDiagonalGram (evenTargetBlock M)
        (projectPairedBaseContribution M) =
      ∑ q : PairedOddBase (oddProjectRadius M),
        ∑ r ∈ Finset.univ.erase q,
          ∑ n ∈ Finset.range M.succ,
            ∑ a ∈ Finset.range M.succ,
              ∑ b ∈ Finset.range M.succ,
                selectedPairHalfGridTerm M q r n a b := by
  unfold orderedOffDiagonalGram
  simp_rw [finiteCorrelation_projectPairedBaseContribution_eq_halfGrid]

/-- ZMod-indexed form of the step-two local atom, used for exact period
cancellation and prefix decomposition. -/
noncomputable def selectedPairEvenStepResidueAtom
    {R : Nat} (q r : PairedOddBase R)
    (a b n : ZMod (q.val.val * r.val.val)) : Real :=
  let K := q.val.val * r.val.val
  let hq : q.val.val ∣ K := Nat.dvd_mul_right _ _
  let hr : r.val.val ∣ K := Nat.dvd_mul_left _ _
  localPairMixedRamanujanRealAtom hq hr
    ((2 : ZMod K) * a) ((2 : ZMod K) * b)
    ((2 : ZMod K) * (n - b))

/-- Complete step-two target periods cancel because the local period is odd,
so multiplication by two and translation by `-b` form a permutation. -/
theorem selectedPairEvenStepResidueAtom_complete_period_eq_zero
    {R : Nat} (q r : PairedOddBase R)
    (hrErase : r ∈ Finset.univ.erase q)
    (a b : ZMod (q.val.val * r.val.val)) :
    ∑ n : ZMod (q.val.val * r.val.val),
        selectedPairEvenStepResidueAtom q r a b n = 0 := by
  let K := q.val.val * r.val.val
  let _ : NeZero K :=
    ⟨Nat.mul_ne_zero (NeZero.ne q.val.val) (NeZero.ne r.val.val)⟩
  have hodd : Odd K := pairedOddBase_product_odd q r
  have h2 : Nat.Coprime 2 K := by
    rw [Nat.coprime_comm]
    exact (Nat.coprime_two_right).mpr hodd
  let u : (ZMod K)ˣ := ZMod.unitOfCoprime 2 h2
  have hbij : Function.Bijective
      (fun n : ZMod K => (2 : ZMod K) * (n - b)) := by
    have h := u.mulLeft_bijective.comp (Equiv.addLeft (-b)).bijective
    constructor
    · intro x y hxy
      apply h.1
      change (2 : ZMod K) * ((-b) + x) =
        (2 : ZMod K) * ((-b) + y)
      calc
        (2 : ZMod K) * ((-b) + x) = 2 * (x - b) := by ring
        _ = 2 * (y - b) := hxy
        _ = (2 : ZMod K) * ((-b) + y) := by ring
    · intro y
      rcases h.2 y with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      change (2 : ZMod K) * ((-b) + x) = y at hx
      calc
        (2 : ZMod K) * (x - b) = 2 * ((-b) + x) := by ring
        _ = y := hx
  let hq : q.val.val ∣ K := Nat.dvd_mul_right _ _
  let hr : r.val.val ∣ K := Nat.dvd_mul_left _ _
  calc
    (∑ n : ZMod K, selectedPairEvenStepResidueAtom q r a b n) =
        ∑ x : ZMod K,
          localPairMixedRamanujanRealAtom hq hr
            ((2 : ZMod K) * a) ((2 : ZMod K) * b) x := by
      exact Fintype.sum_bijective
        (fun n : ZMod K => (2 : ZMod K) * (n - b)) hbij _ _
          (fun n => by rfl)
    _ = 0 := localPairMixedRamanujanRealAtom_complete_period_eq_zero
      hq hr (val_ne_of_mem_univ_erase hrErase).symm
        ((2 : ZMod K) * a) ((2 : ZMod K) * b)

/-- Exact natural-index bridge into the residue-sequence atom. -/
theorem selectedPairEvenStepAtom_eq_residueAtom
    {R : Nat} (q r : PairedOddBase R) (n a b : Nat) :
    selectedPairEvenStepAtom q r n a b =
      selectedPairEvenStepResidueAtom q r
        (a : ZMod (q.val.val * r.val.val))
        (b : ZMod (q.val.val * r.val.val))
        (n : ZMod (q.val.val * r.val.val)) := by
  unfold selectedPairEvenStepAtom selectedPairEvenStepResidueAtom
  push_cast
  rfl

/-- Every incomplete step-two prefix is bounded by one pair-local residual
period.  This is a ceiling only, not a smallness claim. -/
theorem selectedPairEvenStepAtom_prefix_norm_le
    {R : Nat} (q r : PairedOddBase R)
    (hrErase : r ∈ Finset.univ.erase q)
    (a b T : Nat) :
    ‖∑ n ∈ Finset.range T, selectedPairEvenStepAtom q r n a b‖ ≤
      ((q.val.val * r.val.val : Nat) : Real) *
        ((q.val.val.totient : Real) * (r.val.val.totient : Real)) := by
  let K := q.val.val * r.val.val
  let _ : NeZero K :=
    ⟨Nat.mul_ne_zero (NeZero.ne q.val.val) (NeZero.ne r.val.val)⟩
  let g : ZMod K → Real := fun n =>
    selectedPairEvenStepResidueAtom q r a b n
  have hfull : (∑ n : ZMod K, g n) = 0 := by
    simpa only [g] using
      selectedPairEvenStepResidueAtom_complete_period_eq_zero q r hrErase
        (a : ZMod K) (b : ZMod K)
  let gC : ZMod K → Complex := fun n => (g n : Complex)
  have hfullC : (∑ n : ZMod K, gC n) = 0 := by
    have h := congrArg (fun x : Real => (x : Complex)) hfull
    simpa only [Complex.ofReal_sum, Complex.ofReal_zero, gC] using h
  have hdecomp := residue_interval_decomposition gC 0 T
  have hremC :
      (∑ n ∈ Finset.range T, gC (n : ZMod K)) =
        ∑ n ∈ Finset.range (T % K), gC (n : ZMod K) := by
    simpa [hfullC] using hdecomp
  have hrem :
      (∑ n ∈ Finset.range T, g (n : ZMod K)) =
        ∑ n ∈ Finset.range (T % K), g (n : ZMod K) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_sum, gC] using hremC
  simp_rw [selectedPairEvenStepAtom_eq_residueAtom]
  change ‖∑ n ∈ Finset.range T, g (n : ZMod K)‖ ≤ _
  rw [hrem]
  calc
    ‖∑ n ∈ Finset.range (T % K), g (n : ZMod K)‖ ≤
        ∑ n ∈ Finset.range (T % K), ‖g (n : ZMod K)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range (T % K),
        ((q.val.val.totient : Real) * (r.val.val.totient : Real)) := by
      apply Finset.sum_le_sum
      intro n _hn
      unfold g selectedPairEvenStepResidueAtom
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans
        (localPairMixedRamanujanAtom_norm_le
          (Nat.dvd_mul_right q.val.val r.val.val)
          (Nat.dvd_mul_left r.val.val q.val.val) _ _ _)
    _ = ((T % K : Nat) : Real) *
        ((q.val.val.totient : Real) * (r.val.val.totient : Real)) := by simp
    _ ≤ (K : Real) *
        ((q.val.val.totient : Real) * (r.val.val.totient : Real)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.le_of_lt
          (Nat.mod_lt T (Nat.pos_of_ne_zero (NeZero.ne K)))
      · positivity

/-- Literal total variation of the actual half-index weight along the target
coordinate.  No monotonicity or asymptotic smallness is built into it. -/
noncomputable def selectedPairHalfWeightVariation
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (a b T : Nat) : Real :=
  ∑ n ∈ Finset.range (T - 1),
    |selectedPairHalfExactWeight M q r (n + 1) a b -
      selectedPairHalfExactWeight M q r n a b|

/-- Abel reduction for the actual half-index weight.  The right side retains
the literal terminal norm and literal total variation; neither is declared
small. -/
theorem selectedPairEvenStep_actualWeight_abel
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (hrErase : r ∈ Finset.univ.erase q)
    (a b T : Nat) (_hT : 1 ≤ T) :
    |∑ n ∈ Finset.range T,
        selectedPairHalfExactWeight M q r n a b *
          selectedPairEvenStepAtom q r n a b| ≤
      (((q.val.val * r.val.val : Nat) : Real) *
        ((q.val.val.totient : Real) * (r.val.val.totient : Real))) *
      (|selectedPairHalfExactWeight M q r (T - 1) a b| +
        selectedPairHalfWeightVariation M q r a b T) := by
  let w : Nat → Real := fun n => selectedPairHalfExactWeight M q r n a b
  let g : Nat → Real := fun n => selectedPairEvenStepAtom q r n a b
  have habel := Finset.sum_range_by_parts w g T
  simp only [smul_eq_mul] at habel
  change |∑ n ∈ Finset.range T, w n * g n| ≤ _
  rw [habel]
  calc
    _ ≤ |w (T - 1) * ∑ n ∈ Finset.range T, g n| +
        |∑ n ∈ Finset.range (T - 1),
          (w (n + 1) - w n) * ∑ j ∈ Finset.range (n + 1), g j| :=
      abs_sub _ _
    _ ≤ |w (T - 1)| *
          (((q.val.val * r.val.val : Nat) : Real) *
            ((q.val.val.totient : Real) * (r.val.val.totient : Real))) +
        ∑ n ∈ Finset.range (T - 1),
          |w (n + 1) - w n| *
            (((q.val.val * r.val.val : Nat) : Real) *
              ((q.val.val.totient : Real) * (r.val.val.totient : Real))) := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (selectedPairEvenStepAtom_prefix_norm_le q r hrErase a b T)
          (abs_nonneg _)
      · calc
          _ ≤ ∑ n ∈ Finset.range (T - 1),
              |(w (n + 1) - w n) *
                ∑ j ∈ Finset.range (n + 1), g j| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro n hn
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              (selectedPairEvenStepAtom_prefix_norm_le q r hrErase
                a b (n + 1)) (abs_nonneg _)
    _ = (((q.val.val * r.val.val : Nat) : Real) *
          ((q.val.val.totient : Real) * (r.val.val.totient : Real))) *
        (|w (T - 1)| + ∑ n ∈ Finset.range (T - 1),
          |w (n + 1) - w n|) := by
      rw [← Finset.sum_mul]
      ring
    _ = _ := by
      rfl

end GoldbachCircleMethodSelectedPairEvenTargetReindexV18692
