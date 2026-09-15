import GoldbachCircleMethodCanonicalCentralSourceRecombinationV18407
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Goldbach V1.8.408: eventual central active scale absorption

The sole numerical power budget left explicit by V1.8.406 is discharged for
every fixed positive `rho` and fixed nonnegative moment constant `Crho` at a
sufficiently large central block scale.  The proof is elementary asymptotic
algebra: `log(B)^2 / B^(5*rho/8) -> 0`.

This module supplies no Vaughan estimate and no value of the external moment
constant.  It only proves that any already obtained finite constant is
eventually absorbed.
-/

set_option autoImplicit false

open scoped BigOperators Classical
open Filter Topology

namespace GoldbachCircleMethodCanonicalCentralActiveScaleAbsorptionV18408

open GoldbachCircleMethodCanonicalCentralSourceTransferV18404

theorem central_active_normalized_decay_identity
    (m : ℕ) (hm : 1 ≤ m) (rho Crho : ℝ) :
    Crho * (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
        (Real.log ((8 * m : ℕ) : ℝ)) ^ 2 =
      Crho * (Real.log ((8 * m : ℕ) : ℝ)) ^ 2 /
        (((8 * m : ℕ) : ℝ) ^ (rho * ((5 : ℝ) / 8))) := by
  have hB : (0 : ℝ) < ((8 * m : ℕ) : ℝ) := by
    push_cast
    positivity
  have hneg : (-(5 : ℝ) / 8) = -((5 : ℝ) / 8) := by ring
  rw [hneg, Real.rpow_neg (Real.rpow_nonneg hB.le rho)]
  rw [← Real.rpow_mul hB.le]
  ring

theorem central_active_normalized_decay_tendsto_zero
    (rho Crho : ℝ) (hrho : 0 < rho) :
    Tendsto (fun m : ℕ =>
      Crho * (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
        (Real.log ((8 * m : ℕ) : ℝ)) ^ 2) atTop (nhds 0) := by
  have hexp : 0 < rho * ((5 : ℝ) / 8) := mul_pos hrho (by norm_num)
  have harg : Tendsto (fun m : ℕ => ((8 * m : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 8 by norm_num)
  have hbase :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hexp).tendsto_div_nhds_zero
  have hcomp := hbase.comp harg
  have hscaled : Tendsto (fun m : ℕ =>
      Crho * ((Real.log ((8 * m : ℕ) : ℝ)) ^ 2 /
        (((8 * m : ℕ) : ℝ) ^ (rho * ((5 : ℝ) / 8)))))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_two, mul_zero] using
      (tendsto_const_nhds (x := Crho)).mul hcomp
  apply Filter.Tendsto.congr' _ hscaled
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  rw [central_active_normalized_decay_identity m hm rho Crho]
  ring

/-- A normalized decay below `1/65536` implies the exact V1.8.406 square
budget.  The factor `2m+1` is absorbed by `2m+1 <= 8m = B`. -/
theorem central_active_power_budget_of_normalized_decay
    (m : ℕ) (hm : 1 ≤ m) (rho Crho : ℝ)
    (hCrho : 0 ≤ Crho)
    (hdecay :
      Crho * (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
          (Real.log ((8 * m : ℕ) : ℝ)) ^ 2 <
        (1 : ℝ) / 65536) :
    (2 * m + 1 : ℝ) *
          (Crho * ((8 * m : ℕ) : ℝ) ^ 3 *
            (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
            (Real.log ((8 * m : ℕ) : ℝ)) ^ 2) <
      (((8 * m : ℕ) : ℝ) ^ 2 / 256) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hcount : (2 * m + 1 : ℝ) ≤ ((8 * m : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * m + 1 ≤ 8 * m by omega)
  have hfactor : 0 ≤
      Crho * ((8 * m : ℕ) : ℝ) ^ 3 *
        (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
        (Real.log ((8 * m : ℕ) : ℝ)) ^ 2 := by positivity
  calc
    (2 * m + 1 : ℝ) *
          (Crho * ((8 * m : ℕ) : ℝ) ^ 3 *
            (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
            (Real.log ((8 * m : ℕ) : ℝ)) ^ 2) ≤
      ((8 * m : ℕ) : ℝ) *
          (Crho * ((8 * m : ℕ) : ℝ) ^ 3 *
            (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
            (Real.log ((8 * m : ℕ) : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_right hcount hfactor
    _ < ((8 * m : ℕ) : ℝ) ^ 4 / 65536 := by
      have hBpos : (0 : ℝ) < ((8 * m : ℕ) : ℝ) := by
        push_cast
        positivity
      have hmul := mul_lt_mul_of_pos_left hdecay (pow_pos hBpos 4)
      calc
        ((8 * m : ℕ) : ℝ) *
            (Crho * ((8 * m : ℕ) : ℝ) ^ 3 *
              (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
              (Real.log ((8 * m : ℕ) : ℝ)) ^ 2) =
          ((8 * m : ℕ) : ℝ) ^ 4 *
            (Crho * (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
              (Real.log ((8 * m : ℕ) : ℝ)) ^ 2) := by ring
        _ < ((8 * m : ℕ) : ℝ) ^ 4 * ((1 : ℝ) / 65536) := hmul
        _ = ((8 * m : ℕ) : ℝ) ^ 4 / 65536 := by ring
    _ = (((8 * m : ℕ) : ℝ) ^ 2 / 256) ^ 2 := by ring

/-- For fixed `rho > 0` and a fixed nonnegative moment constant, all
sufficiently large central blocks satisfy the V1.8.406 numerical budget. -/
theorem eventual_central_active_power_budget
    (rho Crho : ℝ) (hrho : 0 < rho) (hCrho : 0 ≤ Crho) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
      (2 * m + 1 : ℝ) *
          (Crho * ((8 * m : ℕ) : ℝ) ^ 3 *
            (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
            (Real.log ((8 * m : ℕ) : ℝ)) ^ 2) <
        (((8 * m : ℕ) : ℝ) ^ 2 / 256) ^ 2 := by
  have hsmall :=
    (central_active_normalized_decay_tendsto_zero rho Crho hrho).eventually_lt_const
      (show (0 : ℝ) < 1 / 65536 by norm_num)
  have hev : ∀ᶠ m : ℕ in atTop,
      (2 * m + 1 : ℝ) *
          (Crho * ((8 * m : ℕ) : ℝ) ^ 3 *
            (((8 * m : ℕ) : ℝ) ^ rho) ^ (-(5 : ℝ) / 8) *
            (Real.log ((8 * m : ℕ) : ℝ)) ^ 2) <
        (((8 * m : ℕ) : ℝ) ^ 2 / 256) ^ 2 := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with m hdecay hm
    exact central_active_power_budget_of_normalized_decay
      m hm rho Crho hCrho hdecay
  exact eventually_atTop.mp hev

end GoldbachCircleMethodCanonicalCentralActiveScaleAbsorptionV18408
