import GoldbachCircleMethodOddDoubleSincPairV18678

/-!
# V1.8.679: pointwise amplitude gain for an odd/double denominator pair

V1.8.678 factors the common Ramanujan coefficient of the literal `q`/`2*q`
pair at an even signed frequency while retaining the two different sinc radii.
This append-only module adds an explicit rational ceiling for that two-radius
sum.  The ceiling is deliberately not advertised as optimal.

The proof uses a sum-of-squares certificate in the half-angle cosine.  It then
transports the scalar estimate to the exact `explicitDenominatorSincTerm`
pair at every nonzero even integer frequency.

No sign, monotonicity, target-block moment, exceptional-set, or Goldbach
conclusion is asserted.  `proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped Classical

namespace GoldbachCircleMethodOddDoublePairAmplitudeV18679

open GoldbachCircleMethodOddDoubleSincPairV18678
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodOriginalMaskModelBindingV1859

/-- A strict SOS certificate for the polynomial that controls the half-angle
form of `sin x + sin (x/2)`. -/
theorem halfAngle_sos_certificate_pos (c : Real) :
    0 <
      (81 / 25 : Real) - (1 - c ^ 2) * (2 * c + 1) ^ 2 := by
  have hIdentity :
      (81 / 25 : Real) - (1 - c ^ 2) * (2 * c + 1) ^ 2 =
        (2 * c ^ 2 + c - 7 / 5) ^ 2 +
          (8 / 5 : Real) * (c - 3 / 8) ^ 2 + 11 / 200 := by
    ring_nf
  rw [hIdentity]
  positivity

/-- Rational pointwise ceiling for the two nested sine phases.  The constant
`9/5` is certified by SOS and is not claimed to be optimal. -/
theorem abs_sin_add_sin_half_le_nine_fifths (x : Real) :
    |Real.sin x + Real.sin (x / 2)| ≤ (9 / 5 : Real) := by
  let c : Real := Real.cos (x / 2)
  let s : Real := Real.sin (x / 2)
  have hCircle : s ^ 2 + c ^ 2 = 1 := by
    dsimp only [s, c]
    exact Real.sin_sq_add_cos_sq (x / 2)
  have hSin : Real.sin x + Real.sin (x / 2) = s * (2 * c + 1) := by
    rw [show x = 2 * (x / 2) by ring_nf, Real.sin_two_mul]
    simp only [s, c]
    ring_nf
  have hPoly :
      (1 - c ^ 2) * (2 * c + 1) ^ 2 < (9 / 5 : Real) ^ 2 := by
    have h := halfAngle_sos_certificate_pos c
    norm_num at h ⊢
    nlinarith
  have hSq :
      (s * (2 * c + 1)) ^ 2 < (9 / 5 : Real) ^ 2 := by
    calc
      (s * (2 * c + 1)) ^ 2 = s ^ 2 * (2 * c + 1) ^ 2 := by ring_nf
      _ = (1 - c ^ 2) * (2 * c + 1) ^ 2 := by
        have hs : s ^ 2 = 1 - c ^ 2 := by linarith
        rw [hs]
      _ < (9 / 5 : Real) ^ 2 := hPoly
  rw [hSin]
  have hAbs : |s * (2 * c + 1)| < |(9 / 5 : Real)| := sq_lt_sq.mp hSq
  norm_num at hAbs ⊢
  exact hAbs.le

/-- Division by the nonzero Fourier frequency turns the scalar two-sine
ceiling into the exact harmonic `1/|k|` ceiling. -/
theorem norm_real_sin_pair_div_le
    (x k : Real) (_hk : k ≠ 0) :
    ‖((((Real.sin x + Real.sin (x / 2)) /
        (Real.pi * k) : Real) : Complex))‖ ≤
      (9 / 5 : Real) / (Real.pi * |k|) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_right
    (abs_sin_add_sin_half_le_nine_fifths x)
    (mul_nonneg Real.pi_pos.le (abs_nonneg k))

/-- Algebraic identification of the two retained radii with the nested sine
pair.  The `q₂ = 2*q` hypothesis changes only the phase radius. -/
theorem explicitSincRadiusFactor_odd_double_sum_eq
    (M P R : Nat) (k : Int) (q q₂ : Denominator R)
    (hq₂ : q₂.val = 2 * q.val) :
    explicitSincRadiusFactor M P R k q +
        explicitSincRadiusFactor M P R k q₂ =
      ((
        (Real.sin
            (2 * Real.pi * (k : Real) *
              ((P : Real) / ((q.val : Real) * (M : Real)))) +
          Real.sin
            ((2 * Real.pi * (k : Real) *
              ((P : Real) / ((q.val : Real) * (M : Real)))) / 2)) /
        (Real.pi * (k : Real)) : Real) : Complex) := by
  simp only [explicitSincRadiusFactor, hq₂, Nat.cast_mul, Nat.cast_ofNat,
    Complex.ofReal_add, Complex.ofReal_div]
  rw [show
    2 * Real.pi * (k : Real) *
        ((P : Real) / (2 * (q.val : Real) * (M : Real))) =
      (2 * Real.pi * (k : Real) *
        ((P : Real) / ((q.val : Real) * (M : Real)))) / 2 by ring_nf]
  ring_nf

/-- Norm ceiling for the exact two-radius sum at a nonzero signed frequency. -/
theorem norm_explicitSincRadiusFactor_odd_double_sum_le
    (M P R : Nat) (k : Int) (hk : k ≠ 0)
    (q q₂ : Denominator R) (hq₂ : q₂.val = 2 * q.val) :
    ‖explicitSincRadiusFactor M P R k q +
        explicitSincRadiusFactor M P R k q₂‖ ≤
      (9 / 5 : Real) / (Real.pi * |(k : Real)|) := by
  rw [explicitSincRadiusFactor_odd_double_sum_eq M P R k q q₂ hq₂]
  apply norm_real_sin_pair_div_le
  exact_mod_cast hk

/-- The actual `q`/`2*q` denominator pair has a strictly better elementary
pointwise amplitude ceiling than the separate triangle bound `2/(pi*|k|)`.
No optimality, sign, or moment conclusion is attached to this estimate. -/
theorem norm_explicitDenominatorSincTerm_odd_double_pair_le
    (M P R : Nat) (k : Int) (hk : k ≠ 0)
    (q q₂ : Denominator R) (hqOdd : Odd q.val)
    (hq₂ : q₂.val = 2 * q.val) (hkEven : Even k) :
    ‖explicitDenominatorSincTerm M P R k q +
        explicitDenominatorSincTerm M P R k q₂‖ ≤
      ‖integerFourierRamanujan q.val (-k) (NeZero.ne q.val)‖ *
        (9 / (5 * Real.pi * |(k : Real)|) : Real) := by
  rw [explicitDenominatorSincTerm_odd_double_pair M P R k q q₂
    hqOdd hq₂ hkEven, Complex.norm_mul]
  have hRadius :=
    norm_explicitSincRadiusFactor_odd_double_sum_le M P R k hk q q₂ hq₂
  have hkReal : (k : Real) ≠ 0 := by exact_mod_cast hk
  have hAbs : |(k : Real)| ≠ 0 := abs_ne_zero.mpr hkReal
  have hNormalize :
      (9 / 5 : Real) / (Real.pi * |(k : Real)|) =
        9 / (5 * Real.pi * |(k : Real)|) := by
    field_simp
  rw [← hNormalize]
  exact mul_le_mul_of_nonneg_left hRadius (norm_nonneg _)

end GoldbachCircleMethodOddDoublePairAmplitudeV18679
