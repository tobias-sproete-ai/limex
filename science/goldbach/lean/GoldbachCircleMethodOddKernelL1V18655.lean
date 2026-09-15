import GoldbachCircleMethodOddPairFiberAdapterV18653
import GoldbachCircleMethodFiniteRamanujanEnergyV18131

/-!
# V1.8.655: conservative L1 bound for the odd kernel channel

This append-only module binds the integer-frequency Ramanujan sum occurring in
the unchanged V1.8.649 explicit Major-mask sinc kernel to the finite-residue
Ramanujan sum controlled in V1.8.131.  The bridge is definitional up to the
commutative order of multiplication in `ZMod q`; no replacement coefficient is
introduced.

For nonzero frequency, `|sin x| <= |x|` bounds the existing sinc factor.  The
V1.8.131 finite-window L1 estimate then gives a deliberately conservative
bound on the full unchanged carrier `shiftCarrier (2*M)`, and hence on its odd
subcarrier.  No endpoint, denominator, shift, or weight is changed.

This is only a finite kernel norm estimate.  It does not combine the kernel
bound with the V1.8.653 odd pair-fiber estimate, does not control the even
channel, and proves no Goldbach statement.

`proof_status = NO_PROOF`.
-/
set_option autoImplicit false

open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodExplicitOffDiagonalKernelLeakageV18649
open GoldbachCircleMethodSignedWindowFourierAdapterV18130
open GoldbachCircleMethodFiniteRamanujanEnergyV18131

namespace GoldbachCircleMethodOddKernelL1V18655

/-- Exact bridge between the integer-frequency sum used by V1.8.649 and the
V1.8.131 finite-residue Ramanujan sum. -/
theorem integerFourierRamanujan_eq_unitCharacterSum
    (q : Nat) [NeZero q] (k : Int) :
    integerFourierRamanujan q k (NeZero.ne q) =
      unitCharacterSum q (k : ZMod q) := by
  simp [integerFourierRamanujan, unitCharacterSum, mul_comm]

/-- The sign used literally by `explicitMajorMaskSincKernel` also binds to the
same Ramanujan sum, using the already-kernelized evenness theorem of V1.8.50. -/
theorem integerFourierRamanujan_neg_eq_unitCharacterSum
    (q : Nat) [NeZero q] (k : Int) :
    integerFourierRamanujan q (-k) (NeZero.ne q) =
      unitCharacterSum q (k : ZMod q) := by
  rw [integerFourierRamanujan_neg]
  exact integerFourierRamanujan_eq_unitCharacterSum q k

/-- Pointwise sinc estimate for the literal V1.8.649 factor.  The denominator
modulus is retained, while the displayed upper bound only discards `q >= 1`. -/
theorem explicit_sinc_factor_norm_le
    {M P R : Nat} (hM : 0 < M) (q : Denominator R)
    (k : Int) (hk : k ≠ 0) :
    ‖((Real.sin
        (2 * Real.pi * (k : Real) *
          ((P : Real) / ((q.val : Real) * (M : Real)))) /
        (Real.pi * (k : Real)) : Real) : Complex)‖ <=
      2 * (P : Real) / (M : Real) := by
  have hqNat : 1 <= q.val := (Finset.mem_Icc.mp q.property).1
  have hq : 0 < (q.val : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqNat)
  have hMReal : 0 < (M : Real) := by exact_mod_cast hM
  have hkReal : (k : Real) ≠ 0 := by exact_mod_cast hk
  have hpi : 0 < Real.pi := Real.pi_pos
  have hP : 0 <= (P : Real) := Nat.cast_nonneg P
  rw [Complex.norm_real]
  rw [Real.norm_eq_abs, abs_div]
  calc
    |Real.sin
        (2 * Real.pi * (k : Real) *
          ((P : Real) / ((q.val : Real) * (M : Real))))| /
        |Real.pi * (k : Real)| <=
      |2 * Real.pi * (k : Real) *
        ((P : Real) / ((q.val : Real) * (M : Real)))| /
        |Real.pi * (k : Real)| := by
          exact div_le_div_of_nonneg_right
            Real.abs_sin_le_abs (abs_nonneg _)
    _ = 2 * (P : Real) / ((q.val : Real) * (M : Real)) := by
      simp only [abs_mul, abs_div,
        abs_of_nonneg (by norm_num : (0 : Real) <= 2),
        abs_of_pos hpi, abs_of_pos hq, abs_of_pos hMReal,
        abs_of_nonneg hP]
      field_simp
    _ <= 2 * (P : Real) / (M : Real) := by
      apply (div_le_div_iff₀ (mul_pos hq hMReal) hMReal).2
      have hqOne : (1 : Real) <= q.val := by exact_mod_cast hqNat
      have hQM : (M : Real) <= (q.val : Real) * (M : Real) := by
        nlinarith
      exact mul_le_mul_of_nonneg_left hQM (by positivity)

/-- Pointwise bound for the unchanged explicit finite Major-mask sinc kernel.
Only triangle inequality and the preceding literal sinc estimate are used. -/
theorem explicitMajorMaskSincKernel_norm_le
    {M P R : Nat} (hM : 0 < M) (k : Int) (hk : k ≠ 0) :
    ‖explicitMajorMaskSincKernel M P R k‖ <=
      (2 * (P : Real) / (M : Real)) *
        ∑ q : Denominator R, ‖unitCharacterSum q.val (k : ZMod q.val)‖ := by
  unfold explicitMajorMaskSincKernel
  refine (norm_sum_le _ _).trans ?_
  calc
    _ <= ∑ q : Denominator R,
        ‖unitCharacterSum q.val (k : ZMod q.val)‖ *
          (2 * (P : Real) / (M : Real)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [norm_mul, integerFourierRamanujan_neg_eq_unitCharacterSum]
      exact mul_le_mul_of_nonneg_left
        (explicit_sinc_factor_norm_le hM q k hk) (norm_nonneg _)
    _ = _ := by simp [Finset.mul_sum, mul_comm]

/-- At zero, the literal V1.8.649 sinc expression is zero because Lean's
division has `0 / 0 = 0`.  No continuous extension is substituted. -/
theorem explicitMajorMaskSincKernel_zero (M P R : Nat) :
    explicitMajorMaskSincKernel M P R 0 = 0 := by
  simp [explicitMajorMaskSincKernel]

/-- Full-carrier conservative L1 estimate.  The carrier is exactly the
existing `shiftCarrier (2*M)`; no endpoint is removed or enlarged. -/
theorem explicitMajorMaskSincKernel_window_l1_le
    {M P R : Nat} (hM : 0 < M) (hR : R <= 2 * M) :
    (∑ k ∈ shiftCarrier (2 * (M : Real)),
      ‖explicitMajorMaskSincKernel M P R k‖) <=
      16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) := by
  have hScale : 0 <= 2 * (P : Real) / (M : Real) := by positivity
  have hPoint (k : Int) (hkCarrier : k ∈ shiftCarrier (2 * (M : Real))) :
      ‖explicitMajorMaskSincKernel M P R k‖ <=
        (2 * (P : Real) / (M : Real)) *
          ∑ q : Denominator R, ‖unitCharacterSum q.val (k : ZMod q.val)‖ := by
    by_cases hk : k = 0
    · subst k
      simp only [explicitMajorMaskSincKernel_zero, norm_zero]
      exact mul_nonneg hScale
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    · exact explicitMajorMaskSincKernel_norm_le hM k hk
  calc
    (∑ k ∈ shiftCarrier (2 * (M : Real)),
        ‖explicitMajorMaskSincKernel M P R k‖) <=
      ∑ k ∈ shiftCarrier (2 * (M : Real)),
        (2 * (P : Real) / (M : Real)) *
          ∑ q : Denominator R,
            ‖unitCharacterSum q.val (k : ZMod q.val)‖ :=
      Finset.sum_le_sum hPoint
    _ = (2 * (P : Real) / (M : Real)) *
        ∑ q : Denominator R,
          ∑ k ∈ shiftCarrier (2 * (M : Real)),
            ‖unitCharacterSum q.val (k : ZMod q.val)‖ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ <= (2 * (P : Real) / (M : Real)) *
        ∑ _q : Denominator R,
          8 * (M : Real) * Real.sqrt (R : Real) := by
      apply mul_le_mul_of_nonneg_left _ hScale
      apply Finset.sum_le_sum
      intro q _hq
      have hqR : q.val <= R := (Finset.mem_Icc.mp q.property).2
      have hqWindow : (q.val : Real) <= 2 * (M : Real) := by
        exact_mod_cast hqR.trans hR
      have hOneWindow : (1 : Real) <= 2 * (M : Real) := by
        exact_mod_cast (show 1 <= 2 * M by omega)
      refine (ramanujan_window_l1_le q.val (2 * (M : Real))
        hOneWindow hqWindow).trans ?_
      have hsqrt : Real.sqrt (q.val : Real) <= Real.sqrt (R : Real) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hqR)
      nlinarith [show (0 : Real) <= M by positivity]
    _ = 16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) := by
      simp [Denominator]
      field_simp
      ring

/-- Odd-channel corollary on the parity filter of the same `shiftCarrier
(2*M)`.  It follows by nonnegativity from the stronger full-carrier bound. -/
theorem explicitMajorMaskSincKernel_odd_window_l1_le
    {M P R : Nat} (hM : 0 < M) (hR : R <= 2 * M) :
    (∑ k ∈ (shiftCarrier (2 * (M : Real))).filter (fun k => Odd k),
      ‖explicitMajorMaskSincKernel M P R k‖) <=
      16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    ?_).trans (explicitMajorMaskSincKernel_window_l1_le hM hR)
  intro k _hk _hkNotOdd
  exact norm_nonneg _

/-- V1.8.649-scale form of the full-window estimate.  Positivity of `P` is
spelled out because the scale inequality alone would not control `R` at
`P = 0`. -/
theorem explicitMajorMaskSincKernel_window_l1_le_of_scale
    {M P R : Nat} (hP : 0 < P) (hscale : 2 * P * R < M) :
    (∑ k ∈ shiftCarrier (2 * (M : Real)),
      ‖explicitMajorMaskSincKernel M P R k‖) <=
      16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) := by
  have hM : 0 < M := by omega
  have hR : R <= 2 * M := by nlinarith
  exact explicitMajorMaskSincKernel_window_l1_le hM hR

/-- Odd-channel V1.8.649-scale corollary on the unchanged window. -/
theorem explicitMajorMaskSincKernel_odd_window_l1_le_of_scale
    {M P R : Nat} (hP : 0 < P) (hscale : 2 * P * R < M) :
    (∑ k ∈ (shiftCarrier (2 * (M : Real))).filter (fun k => Odd k),
      ‖explicitMajorMaskSincKernel M P R k‖) <=
      16 * (P : Real) * (R : Real) * Real.sqrt (R : Real) := by
  have hM : 0 < M := by omega
  have hR : R <= 2 * M := by nlinarith
  exact explicitMajorMaskSincKernel_odd_window_l1_le hM hR

end GoldbachCircleMethodOddKernelL1V18655
