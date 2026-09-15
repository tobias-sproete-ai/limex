import GoldbachCircleMethodActualDiscrepancyScaleAbsorptionV18125

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodRemovedConvolutionNormV18123

namespace GoldbachCircleMethodExactPrincipalBoundaryCostV18126

/-- The unit count bounds the actual character sum, including modulus one. -/
theorem unit_character_norm_le_totient (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖unitCharacterSum q a‖ ≤ (q.totient : ℝ) := by
  have hu : Fintype.card {x : ZMod q // IsUnit x} = q.totient := by
    rw [← ZMod.card_units_eq_totient q]
    apply Fintype.card_congr
    exact (Equiv.ofBijective
      (fun u : (ZMod q)ˣ => (⟨(u : ZMod q), u.isUnit⟩ :
        {x : ZMod q // IsUnit x}))
      ⟨fun u v h => Units.ext (congrArg Subtype.val h),
        fun ⟨x, hx⟩ => by
          obtain ⟨u, rfl⟩ := hx
          exact ⟨u, rfl⟩⟩).symm
  have hcard : (Finset.univ.filter (fun x : ZMod q => IsUnit x)).card =
      q.totient := by simpa only [Fintype.card_subtype] using hu
  unfold unitCharacterSum
  calc
    _ ≤ ∑ r : ZMod q, ‖if IsUnit r then ZMod.stdAddChar (a*r) else 0‖ :=
      norm_sum_le _ _
    _ = ∑ r : ZMod q, if IsUnit r then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      split_ifs <;> simp only [standard_character_norm, norm_zero]
    _ = (q.totient : ℝ) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hcard]

theorem moebius_character_quotient_norm_le_one (q : ℕ) [NeZero q] (a : ZMod q) :
    ‖((ArithmeticFunction.moebius q : ℤ) : ℂ) *
      unitCharacterSum q a / (q.totient : ℂ)‖ ≤ 1 := by
  have ht : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hm : ‖((ArithmeticFunction.moebius q : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q))
  rw [norm_div, norm_mul, Complex.norm_natCast]
  apply (div_le_one ht).mpr
  exact (mul_le_mul hm (unit_character_norm_le_totient q a)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- No change to the product cutoff or to the weight is made. -/
theorem finite_companion_norm_le_linear (Q N : ℕ) (r : PositiveLevel Q)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ n, ‖w n‖ ≤ M) :
    ‖finiteCompanion r N w‖ ≤ M*(Q : ℝ) := by
  unfold finiteCompanion
  calc
    _ ≤ ∑ l : PositiveLevel Q, ‖if r.val*l.val ≤ Q ∧ Nat.Coprime r.val l.val
        then ((ArithmeticFunction.moebius l.val : ℤ) : ℂ) *
          unitCharacterSum l.val (N : ZMod l.val) / (l.val.totient : ℂ) *
            w (r.val*l.val) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _l : PositiveLevel Q, M := by
      apply Finset.sum_le_sum
      intro l _
      split_ifs
      · rw [norm_mul]
        exact (mul_le_mul (moebius_character_quotient_norm_le_one l.val _)
          (hw _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      · simpa only [norm_zero] using hM
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.card_univ, positive_level_card]
      ring

/-- Real-radius membership is exactly an integer-radius condition, not an approximation. -/
theorem abs_sub_le_iff_floor (N U : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    |(N : ℝ)-(U : ℝ)| ≤ H ↔ N ≤ U+⌊H⌋₊ ∧ U ≤ N+⌊H⌋₊ := by
  by_cases hNU : N ≤ U
  · have hcast : (N : ℝ) ≤ U := Nat.cast_le.mpr hNU
    rw [abs_of_nonpos (sub_nonpos.mpr hcast), neg_sub, ← Nat.cast_sub hNU,
      ← Nat.le_floor_iff hH]
    omega
  · have hUN : U ≤ N := by omega
    have hcast : (U : ℝ) ≤ N := Nat.cast_le.mpr hUN
    rw [abs_of_nonneg (sub_nonneg.mpr hcast), ← Nat.cast_sub hUN,
      ← Nat.le_floor_iff hH]
    omega

theorem centered_window_card_le (B N : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (centeredWindow (blockCarrier B) N H).card ≤ 2*⌊H⌋₊+1 := by
  have hs : centeredWindow (blockCarrier B) N H ⊆ Finset.Icc (N-⌊H⌋₊) (N+⌊H⌋₊) := by
    intro U hU
    have hd := (abs_sub_le_iff_floor N U H hH).mp (Finset.mem_filter.mp hU).2
    exact Finset.mem_Icc.mpr (by omega)
  have hc := Finset.card_le_card hs
  rw [Nat.card_Icc] at hc
  omega

theorem centered_window_eq_interior (B N : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hleft : B/2+⌊H⌋₊ < N) (hright : N+⌊H⌋₊ ≤ B) :
    centeredWindow (blockCarrier B) N H = Finset.Icc (N-⌊H⌋₊) (N+⌊H⌋₊) := by
  ext U
  simp only [mem_centeredWindow, blockCarrier, Finset.mem_Ioc, Finset.mem_Icc,
    abs_sub_le_iff_floor N U H hH]
  omega

theorem centered_window_card_interior (B N : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (hleft : B/2+⌊H⌋₊ < N) (hright : N+⌊H⌋₊ ≤ B) :
    (centeredWindow (blockCarrier B) N H).card = 2*⌊H⌋₊+1 := by
  rw [centered_window_eq_interior B N H hH hleft hright, Nat.card_Icc]
  omega


/-- Only the two clipped strips are marked; the middle interval is not changed. -/
def boundaryPoints (B h : ℕ) : Finset ℕ :=
  (blockCarrier B).filter (fun N => N ≤ B/2+h ∨ B < N+h)

theorem boundary_points_card_le (B h : ℕ) :
    (boundaryPoints B h).card ≤ 2*h := by
  have hs : boundaryPoints B h ⊆ Finset.Ioc (B/2) (B/2+h) ∪ Finset.Ioc (B-h) B := by
    intro N hN
    rcases Finset.mem_filter.mp hN with ⟨hJ, hbad⟩
    have hJ' := Finset.mem_Ioc.mp hJ
    rcases hbad with hl | hr
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_Ioc.mpr ⟨hJ'.1, hl⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_Ioc.mpr (by omega)))
  have hc := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
  simp only [Nat.card_Ioc] at hc
  omega

noncomputable def boundaryFactor (B N : ℕ) (H : ℝ) : ℝ :=
  ((centeredWindow (blockCarrier B) N H).card : ℝ)/(2*H)-1

theorem boundary_factor_abs_le_one (B N : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    |boundaryFactor B N H| ≤ 1 := by
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hc : ((centeredWindow (blockCarrier B) N H).card : ℝ) ≤ 2*H+1 := by
    have hh : ((centeredWindow (blockCarrier B) N H).card : ℝ) ≤
        2*(⌊H⌋₊ : ℝ)+1 := by
      exact_mod_cast centered_window_card_le B N H hH0.le
    linarith [Nat.floor_le hH0.le]
  have hratio : ((centeredWindow (blockCarrier B) N H).card : ℝ)/(2*H) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*H)).mpr
    linarith
  have hnonneg : 0 ≤ ((centeredWindow (blockCarrier B) N H).card : ℝ)/(2*H) := by
    positivity
  exact abs_le.mpr (by dsimp only [boundaryFactor]; constructor <;> linarith)

theorem boundary_factor_abs_le_interior (B N : ℕ) (H : ℝ) (hH : 0 < H)
    (hleft : B/2+⌊H⌋₊ < N) (hright : N+⌊H⌋₊ ≤ B) :
    |boundaryFactor B N H| ≤ (2*H)⁻¹ := by
  have hnum : |(2*(⌊H⌋₊ : ℝ)+1)-2*H| ≤ 1 := by
    have hl := Nat.floor_le hH.le
    have hu := Nat.lt_floor_add_one H
    exact abs_le.mpr (by constructor <;> linarith)
  have heq : boundaryFactor B N H = ((2*(⌊H⌋₊ : ℝ)+1)-2*H)/(2*H) := by
    unfold boundaryFactor
    rw [centered_window_card_interior B N H hH.le hleft hright]
    push_cast
    field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : 0 < 2*H)]
  simpa only [one_div] using div_le_div_of_nonneg_right hnum (by positivity : 0 ≤ 2*H)

/-- Includes both endpoint strips and the interior lattice normalization error. -/
theorem boundary_factor_mass_le (B : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    (∑ N ∈ blockCarrier B, |boundaryFactor B N H|) ≤ 2*H+(B : ℝ)/(2*H) := by
  have hH0 : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hp (N : ℕ) (hN : N ∈ blockCarrier B) :
      |boundaryFactor B N H| ≤
        (if N ∈ boundaryPoints B ⌊H⌋₊ then (1 : ℝ) else 0)+(2*H)⁻¹ := by
    by_cases hb : N ∈ boundaryPoints B ⌊H⌋₊
    · simp only [hb, if_true]
      exact (boundary_factor_abs_le_one B N H hH).trans
        (le_add_of_nonneg_right (by positivity))
    · have hn : ¬(N ≤ B/2+⌊H⌋₊ ∨ B < N+⌊H⌋₊) := by
        intro hx
        exact hb (Finset.mem_filter.mpr ⟨hN, hx⟩)
      simp only [hb, if_false, zero_add]
      exact boundary_factor_abs_le_interior B N H hH0 (by omega) (by omega)
  have hcount :
      (∑ N ∈ blockCarrier B, if N ∈ boundaryPoints B ⌊H⌋₊ then (1 : ℝ) else 0) =
        ((boundaryPoints B ⌊H⌋₊).card : ℝ) := by
    rw [← Finset.sum_filter]
    have hf : (blockCarrier B).filter (fun N => N ∈ boundaryPoints B ⌊H⌋₊) =
        boundaryPoints B ⌊H⌋₊ := by
      exact Finset.filter_mem_eq_inter |>.trans
        (Finset.inter_eq_right.mpr (Finset.filter_subset _ _))
    rw [hf]
    simp
  calc
    _ ≤ ∑ N ∈ blockCarrier B,
        ((if N ∈ boundaryPoints B ⌊H⌋₊ then (1 : ℝ) else 0)+(2*H)⁻¹) :=
      Finset.sum_le_sum hp
    _ = ((boundaryPoints B ⌊H⌋₊).card : ℝ) +
        ((blockCarrier B).card : ℝ)*(2*H)⁻¹ := by
      rw [Finset.sum_add_distrib, hcount, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2*(⌊H⌋₊ : ℝ)+(B : ℝ)*(2*H)⁻¹ := by
      apply add_le_add
      · exact_mod_cast boundary_points_card_le B ⌊H⌋₊
      · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (block_carrier_card_le B))
          (by positivity)
    _ ≤ 2*H+(B : ℝ)/(2*H) := by
      rw [div_eq_mul_inv]
      exact add_le_add (by linarith [Nat.floor_le hH0.le]) le_rfl

/-- Exactly the principal boundary correction from V121, not an estimated surrogate. -/
noncomputable def principalBoundary (Q B N : ℕ) (hQ : 1 ≤ Q) (H : ℝ)
    (w : ℕ → ℂ) : ℂ :=
  finiteCompanion (oneLevel hQ) N w *
    (((centeredWindow (blockCarrier B) N H).card : ℂ)/(2*(H : ℂ))-1)

theorem principal_boundary_mass_le (Q B : ℕ) (hQ : 1 ≤ Q) (H : ℝ) (hH : 1 ≤ H)
    (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hw : ∀ n, ‖w n‖ ≤ M) :
    (∑ N ∈ blockCarrier B, ‖principalBoundary Q B N hQ H w‖) ≤
      M*(Q : ℝ)*(2*H+(B : ℝ)/(2*H)) := by
  have hf (N : ℕ) :
      (((centeredWindow (blockCarrier B) N H).card : ℂ)/(2*(H : ℂ))-1) =
        (boundaryFactor B N H : ℂ) := by
    simp [boundaryFactor]
  calc
    _ ≤ ∑ N ∈ blockCarrier B, M*(Q : ℝ)*|boundaryFactor B N H| := by
      apply Finset.sum_le_sum
      intro N _
      unfold principalBoundary
      rw [norm_mul, hf, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (finite_companion_norm_le_linear Q N (oneLevel hQ) w M hM hw) (abs_nonneg _)
    _ = M*(Q : ℝ)*(∑ N ∈ blockCarrier B, |boundaryFactor B N H|) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (boundary_factor_mass_le B H hH) (by positivity)


/-- Specialization to the unchanged logarithmic cutoff and original block window. -/
noncomputable def actualPrincipalBoundary (B N : ℕ) (R : ℝ) (hR : 1 < R)
    (G : ℝ → ℝ) : ℂ :=
  principalBoundary ⌊R^2⌋₊ B N (log_cutoff_contains_one R hR)
    ((B : ℝ)/R^4) (logWeight R G)

theorem actual_principal_boundary_mass_le (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M) (hH : 1 ≤ (B : ℝ)/R^4) :
    (∑ N ∈ blockCarrier B, ‖actualPrincipalBoundary B N R hR G‖) ≤
      M*(2*(B : ℝ)/R^2+R^6/2) := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hw : ∀ n, ‖logWeight R G n‖ ≤ M := by
    intro n
    simpa only [logWeight, Complex.norm_real, Real.norm_eq_abs] using
      hG (Real.log (n : ℝ)/Real.log R)
  have hc := principal_boundary_mass_le ⌊R^2⌋₊ B (log_cutoff_contains_one R hR)
    ((B : ℝ)/R^4) hH (logWeight R G) M hM hw
  calc
    _ ≤ M*(⌊R^2⌋₊ : ℝ)*(2*((B : ℝ)/R^4)+(B : ℝ)/(2*((B : ℝ)/R^4))) := hc
    _ ≤ M*R^2*(2*((B : ℝ)/R^4)+(B : ℝ)/(2*((B : ℝ)/R^4))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Nat.floor_le (sq_nonneg R)) hM) (by positivity)
    _ = _ := by
      field_simp [ne_of_gt hRpos, ne_of_gt hBpos]

theorem actual_principal_boundary_mass_le_under_scale (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M) (hscale : R^7 ≤ (B : ℝ)) :
    (∑ N ∈ blockCarrier B, ‖actualPrincipalBoundary B N R hR G‖) ≤
      (5/2)*M*(B : ℝ)/R := by
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have h4 : R^4 ≤ (B : ℝ) :=
    (pow_le_pow_right₀ hR.le (by decide : 4 ≤ 7)).trans hscale
  have hH : 1 ≤ (B : ℝ)/R^4 := (one_le_div (by positivity)).mpr h4
  have h6 : R^6 ≤ (B : ℝ)/R := by
    apply (le_div_iff₀ hRpos).mpr
    simpa only [← pow_succ] using hscale
  have hBR : (B : ℝ)/R^2 ≤ (B : ℝ)/R :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg B) hRpos (by nlinarith)
  calc
    _ ≤ M*(2*(B : ℝ)/R^2+R^6/2) :=
      actual_principal_boundary_mass_le B hB R hR G M hM hG hH
    _ ≤ M*(2*((B : ℝ)/R)+((B : ℝ)/R)/2) := by
      apply mul_le_mul_of_nonneg_left _ hM
      rw [mul_div_assoc]
      linarith
    _ = _ := by ring

/-- The established upper range is more than sufficient for the explicit cost bound. -/
theorem actual_principal_boundary_mass_le_existing_range (B : ℕ) (hB : 2 ≤ B)
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hG : ∀ x : ℝ, |G x| ≤ M)
    (hupper : R ≤ (B : ℝ)^((1 : ℝ)/10000)) :
    (∑ N ∈ blockCarrier B, ‖actualPrincipalBoundary B N R hR G‖) ≤
      (5/2)*M*(B : ℝ)/R := by
  apply actual_principal_boundary_mass_le_under_scale B hB R hR G M hM hG
  exact (pow_le_pow_right₀ hR.le (by decide : 7 ≤ 34)).trans
    (GoldbachCircleMethodActualDiscrepancyScaleAbsorptionV18125.existing_upper_range_implies_scale
      (B : ℝ) R (by exact_mod_cast (by omega : 1 ≤ B))
      (le_of_lt (lt_trans zero_lt_one hR)) hupper)

end GoldbachCircleMethodExactPrincipalBoundaryCostV18126
