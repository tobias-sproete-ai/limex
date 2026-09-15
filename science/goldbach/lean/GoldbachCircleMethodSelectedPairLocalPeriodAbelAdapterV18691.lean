import GoldbachCircleMethodSelectedPairCrossCorrelationExpansionV18690
import GoldbachCircleMethodMixedRamanujanOrthogonalityV18203
import GoldbachCircleMethodActualCompanionIntervalTransferV18205
import GoldbachCircleMethodExactPrincipalBoundaryCostV18126

/-!
# V1.8.691: local-period and Abel interface for selected-pair cross terms

V1.8.690 exposes the selected odd/double off-diagonal Gram term in the exact
`q,r,N,t,u` coordinates.  This append-only module establishes the next
strictly local interfaces:

* membership in `univ.erase q` really supplies `r != q`;
* even targets and even pair-sum fibers have an exact halved integer shift;
* for fixed distinct base denominators and fixed fibers, the actual V66
  Ramanujan atoms have zero mixed convolution on the pair-local product
  period `q*r`, without a coprimality hypothesis;
* finite Abel summation exposes the terminal weight and every first-difference
  variation term instead of replacing the actual sinc radii, fiber mass, or
  off-diagonal notch by a model.

The complete-period identity supplies a pair-local prefix bound through exact
residue-interval decomposition.  It is not yet a bound for the actual
`N`-dependent V1.8.690 weight: that weight contains both distinct sinc radii,
`oddOddPairFiberMass`, changing fiber carriers, and the deleted `t=N` / `u=N`
notches.  Its terminal and total-variation budgets therefore remain explicit
hypotheses.

No global LCM, q-versus-2q orthogonality, absolute-value/Cauchy estimate,
cardinality loss, moment estimate, exceptional-set result, or Goldbach
conclusion is introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodFiniteRamanujanEnergyV18131
open GoldbachCircleMethodActualCompanionIntervalTransferV18205
open GoldbachCircleMethodExactPrincipalBoundaryCostV18126
open GoldbachCircleMethodMixedRamanujanOrthogonalityV18203
open GoldbachCircleMethodOddKernelL1V18655
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddDoubleSincPairV18678
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodSelectedPairCrossCorrelationExpansionV18690

/-- The `erase q` carrier in V1.8.689--690 supplies the exact off-diagonal
condition and nothing stronger. -/
theorem ne_of_mem_univ_erase
    {R : Nat} {q r : PairedOddBase R}
    (hr : r ∈ (Finset.univ.erase q)) : r ≠ q :=
  (Finset.mem_erase.mp hr).1

/-- Distinct selected subtypes have distinct underlying natural moduli. -/
theorem val_ne_of_mem_univ_erase
    {R : Nat} {q r : PairedOddBase R}
    (hr : r ∈ (Finset.univ.erase q)) : r.val.val ≠ q.val.val := by
  intro hv
  apply ne_of_mem_univ_erase hr
  apply Subtype.ext
  apply Subtype.ext
  exact hv

/-- Selected bases are odd, as required by the even-target local-period
reindexing. -/
theorem pairedOddBase_odd {R : Nat} (q : PairedOddBase R) : Odd q.val.val :=
  (mem_pairedOddBaseClass_iff.mp q.property).2.1

/-- The product of two selected base moduli is odd. -/
theorem pairedOddBase_product_odd
    {R : Nat} (q r : PairedOddBase R) : Odd (q.val.val * r.val.val) :=
  (pairedOddBase_odd q).mul (pairedOddBase_odd r)

/-- Exact halving of an even target and an even retained pair-sum fiber.  The
signed shift remains an integer, so no truncated natural subtraction enters. -/
theorem even_target_fiber_half_reindex
    {M N t : Nat} (hN : Even N)
    (ht : t ∈ oddOddOffDiagonalSumCarrier M N) :
    ∃ n s : Nat,
      N = 2 * n ∧ t = 2 * s ∧
        (N : Int) - (t : Int) = 2 * ((n : Int) - (s : Int)) := by
  rcases hN with ⟨n, hn⟩
  have htEven := (mem_oddOddOffDiagonalSumCarrier_iff M N t).mp ht |>.2.1
  rcases htEven with ⟨s, hs⟩
  refine ⟨n, s, ?_, ?_, ?_⟩
  · omega
  · omega
  · norm_num [hn, hs]
    ring

/-- Ramanujan sums at an integer residue are even under sign reversal.  This
uses the exact integer-frequency bridge, not a real-valued surrogate. -/
theorem unitCharacterSum_intCast_neg_eq
    (q : Nat) [NeZero q] (k : Int) :
    unitCharacterSum q ((-k : Int) : ZMod q) =
      unitCharacterSum q (k : ZMod q) := by
  calc
    unitCharacterSum q ((-k : Int) : ZMod q) =
        integerFourierRamanujan q (-k) (NeZero.ne q) :=
      (integerFourierRamanujan_eq_unitCharacterSum q (-k)).symm
    _ = integerFourierRamanujan q k (NeZero.ne q) :=
      integerFourierRamanujan_neg q k (NeZero.ne q)
    _ = unitCharacterSum q (k : ZMod q) :=
      integerFourierRamanujan_eq_unitCharacterSum q k

/-- The actual finite Ramanujan atom is real.  Conjugation changes its
frequency sign termwise, and the preceding exact sign symmetry closes the
reflection. -/
theorem unitCharacterSum_im_eq_zero
    (q : Nat) [NeZero q] (a : ZMod q) :
    (unitCharacterSum q a).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  calc
    star (unitCharacterSum q a) = unitCharacterSum q (-a) := by
      unfold unitCharacterSum
      change (starRingEnd Complex)
        (∑ r : ZMod q,
          if IsUnit r then ZMod.stdAddChar (a * r) else 0) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : IsUnit x
      · simp only [hx, if_true]
        change star (ZMod.stdAddChar (a * x)) = _
        rw [standard_character_conjugate]
        congr 1
        ring
      · simp [hx]
    _ = unitCharacterSum q a := by
      have h := unitCharacterSum_intCast_neg_eq q (a.val : Int)
      rw [← ZMod.natCast_zmod_val a]
      simpa only [Int.cast_neg, Int.cast_natCast] using h

/-- The exact real Ramanujan atom of one selected base at one actual V1.8.690
target/fiber shift. -/
noncomputable def selectedPairRamanujanAtom
    {R : Nat} (q : PairedOddBase R) (N t : Nat) : Real :=
  (integerFourierRamanujan q.val.val
    (-((N : Int) - (t : Int))) (NeZero.ne q.val.val)).re

/-- The exact remaining V1.8.690 weight after factoring only the Ramanujan
atom.  It retains `oddOddPairFiberMass` and both distinct sinc radii. -/
noncomputable def selectedPairExactSincFiberWeight
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (N t : Nat) : Real :=
  oddOddPairFiberMass M t *
    (explicitSincRadiusFactor M
      (oddProjectWidth M) (oddProjectRadius M)
      ((N : Int) - (t : Int)) q.val +
      explicitSincRadiusFactor M
        (oddProjectWidth M) (oddProjectRadius M)
        ((N : Int) - (t : Int)) (pairedDoubleDenominator q)).re

/-- Exact factorization of the literal V1.8.690 one-pair fiber term on its
retained even target carrier.  No radius or fiber mass is replaced. -/
theorem projectPairedBaseFiberTerm_eq_atom_mul_exactWeight
    (M : Nat) (q : PairedOddBase (oddProjectRadius M))
    (N t : Nat) (hN : Even N)
    (ht : t ∈ oddOddOffDiagonalSumCarrier M N) :
    projectPairedBaseFiberTerm M q N t =
      selectedPairRamanujanAtom q N t *
        selectedPairExactSincFiberWeight M q N t := by
  unfold projectPairedBaseFiberTerm selectedPairRamanujanAtom
    selectedPairExactSincFiberWeight
  rw [explicitDenominatorSincTerm_odd_double_pair M
    (oddProjectWidth M) (oddProjectRadius M)
    ((N : Int) - (t : Int)) q.val (pairedDoubleDenominator q)
    (pairedOddBase_odd q) (pairedDoubleDenominator_val q)
    (retained_oddOdd_shift_even hN ht)]
  have hRadiusIm :
      (explicitSincRadiusFactor M
        (oddProjectWidth M) (oddProjectRadius M)
        ((N : Int) - (t : Int)) q.val +
        explicitSincRadiusFactor M
          (oddProjectWidth M) (oddProjectRadius M)
          ((N : Int) - (t : Int)) (pairedDoubleDenominator q)).im = 0 := by
    unfold explicitSincRadiusFactor
    rw [Complex.add_im]
    simp only [Complex.ofReal_im, zero_add]
  rw [Complex.mul_re, hRadiusIm, mul_zero, sub_zero]
  ring

/-- Exact two-fiber cross factorization for one ordered selected pair.  Both
actual weights remain distinct and depend on the common target `N`. -/
theorem projectPairedBaseFiberTerm_mul_eq_atoms_mul_exactWeights
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (N t u : Nat) (hN : Even N)
    (ht : t ∈ oddOddOffDiagonalSumCarrier M N)
    (hu : u ∈ oddOddOffDiagonalSumCarrier M N) :
    projectPairedBaseFiberTerm M q N t *
        projectPairedBaseFiberTerm M r N u =
      (selectedPairRamanujanAtom q N t *
          selectedPairRamanujanAtom r N u) *
        (selectedPairExactSincFiberWeight M q N t *
          selectedPairExactSincFiberWeight M r N u) := by
  rw [projectPairedBaseFiberTerm_eq_atom_mul_exactWeight M q N t hN ht,
    projectPairedBaseFiberTerm_eq_atom_mul_exactWeight M r N u hN hu]
  ring

/-- The exact moving-notch weight used when fixed fibers `t,u` are extended
across a consecutive target parametrization.  A missing V1.8.690 carrier
membership contributes zero, so both `t=N` and `u=N` jumps remain explicit. -/
noncomputable def selectedPairMovingNotchWeight
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (t u N : Nat) : Real :=
  if t ∈ oddOddOffDiagonalSumCarrier M N ∧
      u ∈ oddOddOffDiagonalSumCarrier M N then
    selectedPairExactSincFiberWeight M q N t *
      selectedPairExactSincFiberWeight M r N u
  else 0

/-- The actual pair-local mixed Ramanujan atom.  The common carrier is only
the product period of this one ordered pair; it is not a global LCM. -/
noncomputable def localPairMixedRamanujanAtom
    {K q r : Nat} [NeZero K] [NeZero q] [NeZero r]
    (hq : q ∣ K) (hr : r ∣ K)
    (t u x : ZMod K) : Complex :=
  unitCharacterSum q
      (ZMod.castHom hq (ZMod q) ((t - u) - x)) *
    unitCharacterSum r (ZMod.castHom hr (ZMod r) x)

/-- Real projection of the pair-local atom.  This is the scalar type used by
the literal V1.8.690 cross term. -/
noncomputable def localPairMixedRamanujanRealAtom
    {K q r : Nat} [NeZero K] [NeZero q] [NeZero r]
    (hq : q ∣ K) (hr : r ∣ K)
    (t u x : ZMod K) : Real :=
  (localPairMixedRamanujanAtom hq hr t u x).re

/-- Exact bridge from the two literal integer-frequency coefficients occurring
in V1.8.690 to the pair-local convolution coordinate `x = N-u`.  The second
Ramanujan value is already at `x`; the first is reflected using its proved
evenness to expose `(t-u)-x`.  No coefficient is
replaced. -/
theorem integerRamanujanProduct_eq_localPairMixedAtom
    {K q r : Nat} [NeZero K] [NeZero q] [NeZero r]
    (hq : q ∣ K) (hr : r ∣ K)
    (N t u : Nat) :
    integerFourierRamanujan q
          (-((N : Int) - (t : Int))) (NeZero.ne q) *
        integerFourierRamanujan r
          (-((N : Int) - (u : Int))) (NeZero.ne r) =
      localPairMixedRamanujanAtom hq hr
        (t : ZMod K) (u : ZMod K) ((N : ZMod K) - (u : ZMod K)) := by
  rw [integerFourierRamanujan_neg_eq_unitCharacterSum,
    integerFourierRamanujan_neg_eq_unitCharacterSum]
  have hreflect :
      unitCharacterSum q
          (((N : Int) - (t : Int) : Int) : ZMod q) =
        unitCharacterSum q
          (((t : Int) - (N : Int) : Int) : ZMod q) := by
    have h := unitCharacterSum_intCast_neg_eq q
      ((N : Int) - (t : Int))
    simpa only [neg_sub] using h.symm
  unfold localPairMixedRamanujanAtom
  simp only [map_sub, map_natCast]
  rw [show (t : ZMod q) - (u : ZMod q) -
      ((N : ZMod q) - (u : ZMod q)) =
        (t : ZMod q) - (N : ZMod q) by ring]
  simpa only [Int.cast_sub, Int.cast_natCast] using
    congrArg (fun z => z *
      unitCharacterSum r
        (((N : Int) - (u : Int) : Int) : ZMod r)) hreflect

/-- Exact real-carrier bridge for the two Ramanujan factors appearing in the
literal V1.8.690 fiber cross term. -/
theorem selectedPairRamanujanAtoms_mul_eq_localPairMixedRamanujanRealAtom
    {K R : Nat} [NeZero K]
    (q r : PairedOddBase R)
    (hq : q.val.val ∣ K) (hr : r.val.val ∣ K)
    (N t u : Nat) :
    selectedPairRamanujanAtom q N t *
        selectedPairRamanujanAtom r N u =
      localPairMixedRamanujanRealAtom hq hr
        (t : ZMod K) (u : ZMod K) ((N : ZMod K) - (u : ZMod K)) := by
  have hqim :
      (integerFourierRamanujan q.val.val
        (-((N : Int) - (t : Int))) (NeZero.ne q.val.val)).im = 0 := by
    rw [integerFourierRamanujan_neg_eq_unitCharacterSum]
    exact unitCharacterSum_im_eq_zero q.val.val _
  have hrim :
      (integerFourierRamanujan r.val.val
        (-((N : Int) - (u : Int))) (NeZero.ne r.val.val)).im = 0 := by
    rw [integerFourierRamanujan_neg_eq_unitCharacterSum]
    exact unitCharacterSum_im_eq_zero r.val.val _
  unfold selectedPairRamanujanAtom localPairMixedRamanujanRealAtom
  rw [← integerRamanujanProduct_eq_localPairMixedAtom hq hr N t u,
    Complex.mul_re, hqim, hrim]
  ring

/-- V1.8.203 gives exact cancellation of the actual V66 atoms on one local
pair period.  No coprimality of `q,r` is required. -/
theorem localPairMixedRamanujanAtom_complete_period_eq_zero
    {K q r : Nat} [NeZero K] [NeZero q] [NeZero r]
    (hq : q ∣ K) (hr : r ∣ K) (hqr : q ≠ r)
    (t u : ZMod K) :
    (∑ x : ZMod K, localPairMixedRamanujanAtom hq hr t u x) = 0 := by
  unfold localPairMixedRamanujanAtom
  exact actual_unitCharacterSum_mixed_convolution_zero
    hq hr hqr (t - u)

/-- Real projection of the same complete-period cancellation, matching the
scalar Ramanujan factors in V1.8.690. -/
theorem localPairMixedRamanujanRealAtom_complete_period_eq_zero
    {K q r : Nat} [NeZero K] [NeZero q] [NeZero r]
    (hq : q ∣ K) (hr : r ∣ K) (hqr : q ≠ r)
    (t u : ZMod K) :
    (∑ x : ZMod K,
      localPairMixedRamanujanRealAtom hq hr t u x) = 0 := by
  have h := congrArg Complex.re
    (localPairMixedRamanujanAtom_complete_period_eq_zero
      hq hr hqr t u)
  simpa [localPairMixedRamanujanRealAtom] using h

/-- Specialization to the selected bases and their pair-local product period.
The `erase` witness supplies the required denominator inequality. -/
theorem selectedPairMixedRamanujanAtom_complete_period_eq_zero
    {R : Nat} (q r : PairedOddBase R)
    (hrErase : r ∈ (Finset.univ.erase q))
    (t u : ZMod (q.val.val * r.val.val)) :
    let hq : q.val.val ∣ q.val.val * r.val.val := Nat.dvd_mul_right _ _
    let hr : r.val.val ∣ q.val.val * r.val.val := Nat.dvd_mul_left _ _
    (∑ x : ZMod (q.val.val * r.val.val),
      localPairMixedRamanujanAtom hq hr t u x) = 0 := by
  let _ : NeZero (q.val.val * r.val.val) :=
    ⟨Nat.mul_ne_zero (NeZero.ne q.val.val) (NeZero.ne r.val.val)⟩
  dsimp only
  exact localPairMixedRamanujanAtom_complete_period_eq_zero
    (Nat.dvd_mul_right q.val.val r.val.val)
    (Nat.dvd_mul_left r.val.val q.val.val)
    (val_ne_of_mem_univ_erase hrErase).symm t u

/-- Pointwise norm of the actual local atom.  This retains the two individual
Euler-totient costs and makes no coprimality assumption. -/
theorem localPairMixedRamanujanAtom_norm_le
    {K q r : Nat} [NeZero K] [NeZero q] [NeZero r]
    (hq : q ∣ K) (hr : r ∣ K)
    (t u x : ZMod K) :
    ‖localPairMixedRamanujanAtom hq hr t u x‖ ≤
      (q.totient : Real) * (r.totient : Real) := by
  unfold localPairMixedRamanujanAtom
  rw [norm_mul]
  exact mul_le_mul
    (unit_character_norm_le_totient q
      (ZMod.castHom hq (ZMod q) ((t - u) - x)))
    (unit_character_norm_le_totient r
      (ZMod.castHom hr (ZMod r) x))
    (norm_nonneg _) (Nat.cast_nonneg _)

/-- Every incomplete prefix of the local-period atom sequence is bounded by
one strict pair-local boundary.  `T=0` is included: no positive-length
hypothesis is used. -/
theorem localPairMixedRamanujanAtom_prefix_norm_le
    {K q r : Nat} [NeZero K] [NeZero q] [NeZero r]
    (hq : q ∣ K) (hr : r ∣ K) (hqr : q ≠ r)
    (t u : ZMod K) (T : Nat) :
    ‖∑ i ∈ Finset.range T,
        localPairMixedRamanujanAtom hq hr t u (i : ZMod K)‖ ≤
      (K : Real) * ((q.totient : Real) * (r.totient : Real)) := by
  let g : ZMod K → Complex := fun x =>
    localPairMixedRamanujanAtom hq hr t u x
  have hfull : (∑ x : ZMod K, g x) = 0 := by
    simpa only [g] using
      localPairMixedRamanujanAtom_complete_period_eq_zero hq hr hqr t u
  have hdecomp := residue_interval_decomposition g 0 T
  have hrem :
      (∑ i ∈ Finset.range T, g (i : ZMod K)) =
        ∑ i ∈ Finset.range (T % K), g (i : ZMod K) := by
    simpa [hfull] using hdecomp
  rw [show (∑ i ∈ Finset.range T,
      localPairMixedRamanujanAtom hq hr t u (i : ZMod K)) =
      ∑ i ∈ Finset.range T, g (i : ZMod K) by rfl, hrem]
  calc
    ‖∑ i ∈ Finset.range (T % K), g (i : ZMod K)‖ ≤
        ∑ i ∈ Finset.range (T % K), ‖g (i : ZMod K)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (T % K),
        ((q.totient : Real) * (r.totient : Real)) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact localPairMixedRamanujanAtom_norm_le hq hr t u (i : ZMod K)
    _ = ((T % K : Nat) : Real) *
        ((q.totient : Real) * (r.totient : Real)) := by simp
    _ ≤ (K : Real) *
        ((q.totient : Real) * (r.totient : Real)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Nat.le_of_lt
          (Nat.mod_lt T (Nat.pos_of_ne_zero (NeZero.ne K)))
      · positivity

/-- An explicit pair-local Abel envelope.  `u` is the actual complex weight
sequence supplied by the downstream V1.8.690 carrier.  Its terminal norm and
the sum of every first-difference jump are retained verbatim. -/
theorem localPair_weighted_abel_envelope
    {K q r : Nat} [NeZero K] [NeZero q] [NeZero r]
    (hq : q ∣ K) (hr : r ∣ K)
    (t uShift : ZMod K)
    (w : Nat → Complex) (T : Nat) (C H V : Real)
    (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hprefix : ∀ k : Nat, k ≤ T →
      ‖∑ i ∈ Finset.range k,
        localPairMixedRamanujanAtom hq hr t uShift (i : ZMod K)‖ ≤ C)
    (hlast : ‖w (T - 1)‖ ≤ H)
    (hvariation :
      ∑ i ∈ Finset.range (T - 1), ‖w (i + 1) - w i‖ ≤ V) :
    ‖∑ i ∈ Finset.range T,
        w i • localPairMixedRamanujanAtom hq hr t uShift (i : ZMod K)‖ ≤
      C * (H + V) := by
  have habel := Finset.sum_range_by_parts w
    (fun i : Nat =>
      localPairMixedRamanujanAtom hq hr t uShift (i : ZMod K)) T
  rw [habel]
  calc
    _ ≤ ‖w (T - 1) •
          ∑ i ∈ Finset.range T,
            localPairMixedRamanujanAtom hq hr t uShift (i : ZMod K)‖ +
        ‖∑ i ∈ Finset.range (T - 1),
          (w (i + 1) - w i) •
            ∑ j ∈ Finset.range (i + 1),
              localPairMixedRamanujanAtom hq hr t uShift (j : ZMod K)‖ :=
      norm_sub_le _ _
    _ ≤ ‖w (T - 1)‖ * C +
        ∑ i ∈ Finset.range (T - 1),
          ‖w (i + 1) - w i‖ * C := by
      apply add_le_add
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hprefix T le_rfl) (norm_nonneg _)
      · calc
          _ ≤ ∑ i ∈ Finset.range (T - 1),
              ‖(w (i + 1) - w i) •
                ∑ j ∈ Finset.range (i + 1),
                  localPairMixedRamanujanAtom hq hr t uShift (j : ZMod K)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.range (T - 1),
              ‖w (i + 1) - w i‖ * C := by
            apply Finset.sum_le_sum
            intro i hi
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left
              (hprefix (i + 1) (by
                have hi' := Finset.mem_range.mp hi
                omega)) (norm_nonneg _)
    _ = C * (‖w (T - 1)‖ +
        ∑ i ∈ Finset.range (T - 1), ‖w (i + 1) - w i‖) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ C * (H + V) := by gcongr

/-- Closed pair-local prefix-to-Abel bridge.  The only remaining hypotheses
are the actual terminal and total-variation budgets of the downstream weight.
The prefix constant is derived from V1.8.203 rather than postulated. -/
theorem localPair_weighted_abel_of_distinct
    {K q r : Nat} [NeZero K] [NeZero q] [NeZero r]
    (hq : q ∣ K) (hr : r ∣ K) (hqr : q ≠ r)
    (t uShift : ZMod K)
    (w : Nat → Complex) (T : Nat) (H V : Real)
    (hT : 1 ≤ T)
    (hlast : ‖w (T - 1)‖ ≤ H)
    (hvariation :
      ∑ i ∈ Finset.range (T - 1), ‖w (i + 1) - w i‖ ≤ V) :
    ‖∑ i ∈ Finset.range T,
        w i • localPairMixedRamanujanAtom hq hr t uShift (i : ZMod K)‖ ≤
      ((K : Real) *
        ((q.totient : Real) * (r.totient : Real))) * (H + V) := by
  apply localPair_weighted_abel_envelope hq hr t uShift w T
    ((K : Real) * ((q.totient : Real) * (r.totient : Real))) H V
  · positivity
  · exact hT
  · intro k _hk
    exact localPairMixedRamanujanAtom_prefix_norm_le hq hr hqr t uShift k
  · exact hlast
  · exact hvariation

end GoldbachCircleMethodSelectedPairLocalPeriodAbelAdapterV18691
