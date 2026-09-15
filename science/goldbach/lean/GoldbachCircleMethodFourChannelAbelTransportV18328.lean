import GoldbachCircleMethodPairwiseAbelVariationV18327

/-!
# Goldbach V1.8.328: four-channel Abel transport

This module assembles four independently centered complex channels with two
real spatial weights.  Uniform prefix bounds are transported by finite Abel
summation, and the mixed channel uses the product-variation estimate from
V1.8.327.  No periodic common multiple and no analytic source estimate enter.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodFourChannelAbelTransportV18328

open GoldbachCircleMethodPairwiseAbelVariationV18327

/-- Four centered channels with weights `1`, `v`, `u`, and `u*v` retain a
quartic-size prefix budget.  The only spatial loss is the total variation of
the two scalar weights, not the interval length times a pointwise error. -/
theorem four_channel_abel_norm_le
    (aPP aPA aAP aAA : ℕ → ℂ) (u v : ℕ → ℝ)
    (T : ℕ) (C U V : ℝ)
    (hC : 0 ≤ C) (hT : 1 ≤ T)
    (hPP : ∀ k : ℕ, k ≤ T →
      ‖∑ i ∈ Finset.range k, aPP i‖ ≤ C)
    (hPA : ∀ k : ℕ, k ≤ T →
      ‖∑ i ∈ Finset.range k, aPA i‖ ≤ C)
    (hAP : ∀ k : ℕ, k ≤ T →
      ‖∑ i ∈ Finset.range k, aAP i‖ ≤ C)
    (hAA : ∀ k : ℕ, k ≤ T →
      ‖∑ i ∈ Finset.range k, aAA i‖ ≤ C)
    (hu : ∀ i : ℕ, i < T → |u i| ≤ 1)
    (hv : ∀ i : ℕ, i < T → |v i| ≤ 1)
    (hU : ∑ i ∈ Finset.range (T - 1), |u (i + 1) - u i| ≤ U)
    (hV : ∑ i ∈ Finset.range (T - 1), |v (i + 1) - v i| ≤ V) :
    ‖∑ i ∈ Finset.range T,
        (aPP i - v i • aPA i - u i • aAP i +
          (u i * v i) • aAA i)‖ ≤
      C * (4 + 2 * (U + V)) := by
  have hlast_u : |u (T - 1)| ≤ 1 := hu (T - 1) (by omega)
  have hlast_v : |v (T - 1)| ≤ 1 := hv (T - 1) (by omega)
  have hprod_var :
      ∑ i ∈ Finset.range (T - 1),
          |u (i + 1) * v (i + 1) - u i * v i| ≤ U + V :=
    product_weight_total_variation_le u v T U V hu hv hU hV
  have hlast_prod : |u (T - 1) * v (T - 1)| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (u (T - 1)), abs_nonneg (v (T - 1))]
  have hPP' : ‖∑ i ∈ Finset.range T, aPP i‖ ≤ C := hPP T le_rfl
  have hPA' : ‖∑ i ∈ Finset.range T, v i • aPA i‖ ≤ C * (1 + V) :=
    weighted_complex_sum_norm_le_of_prefix_bound
      aPA v T C V hC hT hPA hlast_v hV
  have hAP' : ‖∑ i ∈ Finset.range T, u i • aAP i‖ ≤ C * (1 + U) :=
    weighted_complex_sum_norm_le_of_prefix_bound
      aAP u T C U hC hT hAP hlast_u hU
  have hAA' :
      ‖∑ i ∈ Finset.range T, (u i * v i) • aAA i‖ ≤
        C * (1 + (U + V)) :=
    weighted_complex_sum_norm_le_of_prefix_bound
      aAA (fun i => u i * v i) T C (U + V) hC hT hAA
        hlast_prod hprod_var
  rw [show
    (∑ i ∈ Finset.range T,
      (aPP i - v i • aPA i - u i • aAP i +
        (u i * v i) • aAA i)) =
      (∑ i ∈ Finset.range T, aPP i) -
      (∑ i ∈ Finset.range T, v i • aPA i) -
      (∑ i ∈ Finset.range T, u i • aAP i) +
      (∑ i ∈ Finset.range T, (u i * v i) • aAA i) by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]]
  calc
    _ ≤ ‖∑ i ∈ Finset.range T, aPP i‖ +
          ‖∑ i ∈ Finset.range T, v i • aPA i‖ +
          ‖∑ i ∈ Finset.range T, u i • aAP i‖ +
          ‖∑ i ∈ Finset.range T, (u i * v i) • aAA i‖ := by
      calc
        _ ≤ ‖(∑ i ∈ Finset.range T, aPP i) -
              (∑ i ∈ Finset.range T, v i • aPA i) -
              (∑ i ∈ Finset.range T, u i • aAP i)‖ +
              ‖∑ i ∈ Finset.range T, (u i * v i) • aAA i‖ :=
          norm_add_le _ _
        _ ≤ (‖(∑ i ∈ Finset.range T, aPP i) -
              (∑ i ∈ Finset.range T, v i • aPA i)‖ +
              ‖∑ i ∈ Finset.range T, u i • aAP i‖) +
              ‖∑ i ∈ Finset.range T, (u i * v i) • aAA i‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ((‖∑ i ∈ Finset.range T, aPP i‖ +
              ‖∑ i ∈ Finset.range T, v i • aPA i‖) +
              ‖∑ i ∈ Finset.range T, u i • aAP i‖) +
              ‖∑ i ∈ Finset.range T, (u i * v i) • aAA i‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = _ := by ring
    _ ≤ C + C * (1 + V) + C * (1 + U) + C * (1 + (U + V)) := by
      gcongr
    _ = C * (4 + 2 * (U + V)) := by ring

end GoldbachCircleMethodFourChannelAbelTransportV18328
