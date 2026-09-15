import GoldbachCircleMethodCentralL2CorrectionWitnessTransferV18453
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Goldbach V1.8.454: subcritical L2 exponent absorption

The new factored correction budget does not require either finite energy to
decay.  If their polynomial exponents sum to strictly less than three, the
extra central-target cardinality still leaves a strict power saving against
the squared quadratic reserve.

This module proves that scalar threshold and substitutes actual energy bounds.
It does not prove those analytic energy bounds.
-/

set_option autoImplicit false

open scoped BigOperators Classical Topology
open Filter

namespace GoldbachCircleMethodCentralL2SubcriticalAbsorptionV18454

open GoldbachCircleMethodAdjustedCorrectionL2CompositionV18451
open GoldbachCircleMethodCentralAdjustedCorrectionL2MomentV18452
open GoldbachCircleMethodStructurallyAdmissibleActiveSlotV18258

/-- The canonical block scale tends to infinity. -/
theorem tendsto_eight_mul_natCast_atTop :
    Tendsto (fun m : ℕ => ((8 * m : ℕ) : ℝ)) atTop atTop := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    tendsto_natCast_atTop_atTop.const_mul_atTop (show (0 : ℝ) < 8 by norm_num)

/-- Pure scalar form of the subcritical threshold. -/
theorem subcritical_energy_powers_fit_squared_quadratic_reserve
    (Cs Cp s p : ℝ) (hCs : 0 ≤ Cs) (hCp : 0 ≤ Cp)
    (hgap : s + p < 3) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ((8 * m : ℕ) : ℝ) *
          (Cs * ((8 * m : ℕ) : ℝ) ^ s) *
          (Cp * ((8 * m : ℕ) : ℝ) ^ p) <
        (((8 * m : ℕ) : ℝ) ^ 2 / 2048) ^ 2 := by
  let d : ℝ := 3 - s - p
  let K : ℝ := (2048 : ℝ) ^ 2 * Cs * Cp
  have hd : 0 < d := by dsimp [d]; linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hdecay : Tendsto
      (fun m : ℕ => ((8 * m : ℕ) : ℝ) ^ (-d)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hd).comp tendsto_eight_mul_natCast_atTop
  have hlim : Tendsto
      (fun m : ℕ => K * ((8 * m : ℕ) : ℝ) ^ (-d)) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  have hsmall : ∀ᶠ m : ℕ in atTop,
      K * ((8 * m : ℕ) : ℝ) ^ (-d) < 1 :=
    (tendsto_order.1 hlim).2 1 zero_lt_one
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (1 : ℕ), hsmall] with m hm hlt
  let x : ℝ := ((8 * m : ℕ) : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast (show 0 < 8 * m by omega)
  have hpow : x ^ (1 + s + p) = x ^ (4 : ℝ) * x ^ (-d) := by
    rw [show (1 : ℝ) + s + p = 4 + (-d) by dsimp [d]; ring]
    rw [Real.rpow_add hx]
  have hidentity :
      x * (Cs * x ^ s) * (Cp * x ^ p) =
        (x ^ 2 / 2048) ^ 2 * (K * x ^ (-d)) := by
    calc
      x * (Cs * x ^ s) * (Cp * x ^ p) =
          Cs * Cp * (x ^ (1 : ℝ) * x ^ s * x ^ p) := by
            rw [Real.rpow_one]
            ring
      _ = Cs * Cp * x ^ (1 + s + p) := by
            rw [← Real.rpow_add hx, ← Real.rpow_add hx]
      _ = Cs * Cp * (x ^ (4 : ℝ) * x ^ (-d)) := by rw [hpow]
      _ = Cs * Cp * (x ^ (4 : ℕ) * x ^ (-d)) := by
            exact congrArg (fun z : ℝ => Cs * Cp * (z * x ^ (-d)))
              (Real.rpow_natCast x 4)
      _ = (x ^ 2 / 2048) ^ 2 * (K * x ^ (-d)) := by
            dsimp [K]
            ring
  rw [hidentity]
  exact mul_lt_of_lt_one_right (by positivity) hlt

/-- Actual central factored energies satisfy the V1.8.453 reserve whenever
they admit polynomial majorants whose exponents have subcritical sum. -/
theorem eventual_central_factored_energy_budget_of_subcritical_bounds
    (Cs Cp s p : ℝ) (hCs : 0 ≤ Cs) (hCp : 0 ≤ Cp)
    (hgap : s + p < 3) :
    ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m →
      ∀ (rho b : ℝ),
      ∀ (e : StructurallyAdmissibleActiveSlot
        ⌊(((8 * m : ℕ) : ℝ)^rho)^2⌋₊),
      adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val ≤
          Cs * ((8 * m : ℕ) : ℝ) ^ s →
      centralAdjustedPartnerEnergy m rho b e ≤
          Cp * ((8 * m : ℕ) : ℝ) ^ p →
      (2 * m + 1 : ℕ) *
          (adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
            centralAdjustedPartnerEnergy m rho b e) <
        (((8 * m : ℕ) : ℝ) ^ 2 / 2048) ^ 2 := by
  obtain ⟨m₀, hscalar⟩ :=
    subcritical_energy_powers_fit_squared_quadratic_reserve
      Cs Cp s p hCs hCp hgap
  refine ⟨max m₀ 1, ?_⟩
  intro m hm rho b e hsource hpartner
  have hm₀ : m₀ ≤ m := (le_max_left m₀ 1).trans hm
  have hmOne : 1 ≤ m := (le_max_right m₀ 1).trans hm
  have hcard : ((2 * m + 1 : ℕ) : ℝ) ≤ ((8 * m : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * m + 1 ≤ 8 * m by omega)
  have hsourceNonneg :
      0 ≤ adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val := by
    unfold adjustedSlotEnergyProductSourceSum
    exact Finset.sum_nonneg (fun n _hn =>
      mul_nonneg
        (by unfold GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449.adjustedCoefficientEnergy
            exact Finset.sum_nonneg (fun t _ht => sq_nonneg _))
        (by unfold GoldbachCircleMethodAdjustedCharacterSlotL2AdapterV18449.adjustedSourceEnergy
            exact Finset.sum_nonneg (fun t _ht => sq_nonneg _)))
  have hpartnerNonneg : 0 ≤ centralAdjustedPartnerEnergy m rho b e := by
    unfold centralAdjustedPartnerEnergy adjustedCorrectionPartnerEnergy
    positivity
  have hproductNonneg :
      0 ≤ adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
        centralAdjustedPartnerEnergy m rho b e :=
    mul_nonneg hsourceNonneg hpartnerNonneg
  calc
    (2 * m + 1 : ℕ) *
        (adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
          centralAdjustedPartnerEnergy m rho b e) ≤
      ((8 * m : ℕ) : ℝ) *
        (adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
          centralAdjustedPartnerEnergy m rho b e) :=
        mul_le_mul_of_nonneg_right hcard hproductNonneg
    _ ≤ ((8 * m : ℕ) : ℝ) *
        ((Cs * ((8 * m : ℕ) : ℝ) ^ s) *
          (Cp * ((8 * m : ℕ) : ℝ) ^ p)) := by
      have hCpPow : 0 ≤ Cp * ((8 * m : ℕ) : ℝ) ^ p :=
        by positivity
      have hInnerOne :
          adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
              centralAdjustedPartnerEnergy m rho b e ≤
            adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
              (Cp * ((8 * m : ℕ) : ℝ) ^ p) :=
        mul_le_mul_of_nonneg_left hpartner hsourceNonneg
      have hInnerTwo :
          adjustedSlotEnergyProductSourceSum (8 * m) rho b e.val *
              (Cp * ((8 * m : ℕ) : ℝ) ^ p) ≤
            (Cs * ((8 * m : ℕ) : ℝ) ^ s) *
              (Cp * ((8 * m : ℕ) : ℝ) ^ p) :=
        mul_le_mul_of_nonneg_right hsource hCpPow
      have hInner := hInnerOne.trans hInnerTwo
      have hscaleNonneg : 0 ≤ ((8 * m : ℕ) : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hInner hscaleNonneg
    _ = ((8 * m : ℕ) : ℝ) *
          (Cs * ((8 * m : ℕ) : ℝ) ^ s) *
          (Cp * ((8 * m : ℕ) : ℝ) ^ p) := by ring
    _ < (((8 * m : ℕ) : ℝ) ^ 2 / 2048) ^ 2 :=
      hscalar m hm₀

end GoldbachCircleMethodCentralL2SubcriticalAbsorptionV18454
