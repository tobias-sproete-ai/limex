import GoldbachCircleMethodSignedWindowFourierAdapterV18130

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866

namespace GoldbachCircleMethodFiniteRamanujanEnergyV18131

/-- Full additive orthogonality for every positive modulus, not just primes. -/
theorem standard_character_orthogonality (q : ℕ) [NeZero q] (t : ZMod q) :
    (∑ a : ZMod q, ZMod.stdAddChar (t*a)) = if t=0 then (q : ℂ) else 0 := by
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q h)

theorem standard_character_conjugate (q : ℕ) [NeZero q] (t : ZMod q) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  apply mul_left_cancel₀ (show ZMod.stdAddChar t ≠ 0 by
    have h := standard_character_norm q t
    intro hz
    rw [hz, norm_zero] at h
    norm_num at h)
  rw [Complex.star_def, Complex.mul_conj', standard_character_norm]
  norm_num
  rw [← AddChar.map_add_eq_mul]
  simp

/-- Exact energy of an arbitrary finite residue carrier. -/
theorem residue_carrier_energy (q : ℕ) [NeZero q] (S : Finset (ZMod q)) :
    (∑ a : ZMod q, ‖∑ r ∈ S, ZMod.stdAddChar (a*r)‖^2) =
      (q : ℝ)*(S.card : ℝ) := by
  have hc : (∑ a : ZMod q,
      (∑ r ∈ S, ZMod.stdAddChar (a*r)) *
        star (∑ s ∈ S, ZMod.stdAddChar (a*s))) = (q : ℂ)*(S.card : ℂ) := by
    simp only [star_sum, Finset.mul_sum, Finset.sum_mul, standard_character_conjugate]
    simp_rw [← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub]
    rw [Finset.sum_comm]
    calc
      (∑ r ∈ S, ∑ a : ZMod q, ∑ s ∈ S, ZMod.stdAddChar (a*(s-r))) =
        ∑ r ∈ S, ∑ s ∈ S, ∑ a : ZMod q, ZMod.stdAddChar ((s-r)*a) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
          simp only [mul_comm]
      _ = ∑ r ∈ S, ∑ s ∈ S, if s=r then (q : ℂ) else 0 := by
          simp only [standard_character_orthogonality, sub_eq_zero]
      _ = (q : ℂ)*(S.card : ℂ) := by simp [mul_comm]
  simp only [Complex.star_def, Complex.mul_conj'] at hc
  exact_mod_cast hc

theorem unit_residue_card (q : ℕ) [NeZero q] :
    (Finset.univ.filter (fun x : ZMod q => IsUnit x)).card = q.totient := by
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
  simpa only [Fintype.card_subtype] using hu

/-- Genuine Ramanujan energy: no assumption on squarefreeness or coprimality
of the frequency, and modulus one is included. -/
theorem ramanujan_period_energy (q : ℕ) [NeZero q] :
    (∑ a : ZMod q, ‖unitCharacterSum q a‖^2) =
      (q : ℝ)*(q.totient : ℝ) := by
  have h := residue_carrier_energy q (Finset.univ.filter (fun x => IsUnit x))
  simpa only [Finset.sum_filter, unitCharacterSum, unit_residue_card] using h

/-- A complete residue block, with no incomplete-endpoint loss. -/
theorem sum_range_residues (q : ℕ) [NeZero q] (g : ZMod q → ℝ) :
    (∑ n ∈ Finset.range q, g (n : ZMod q)) = ∑ a : ZMod q, g a := by
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ZMod q))
  · intro n _
    exact Finset.mem_univ _
  · intro n hn m hm h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hn),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hm)] using hv
  · intro a _
    exact ⟨a.val, Finset.mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
  · intro n _
    rfl

theorem shifted_residue_period (q : ℕ) [NeZero q] (g : ZMod q → ℝ)
    (c : ZMod q) :
    (∑ n ∈ Finset.range q, g ((n : ZMod q)+c)) = ∑ a : ZMod q, g a := by
  rw [sum_range_residues q (fun a => g (a+c))]
  exact Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)

theorem repeated_residue_periods (q m : ℕ) [NeZero q] (g : ZMod q → ℝ)
    (c : ZMod q) :
    (∑ n ∈ Finset.range (m*q), g ((n : ZMod q)+c)) =
      (m : ℝ)*∑ a : ZMod q, g a := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
    rw [shifted_residue_period]
    push_cast
    ring

/-- A nonnegative incomplete block is bounded by full periods. -/
theorem incomplete_residue_sum_le (q L : ℕ) [NeZero q] (g : ZMod q → ℝ)
    (hg : ∀ a, 0 ≤ g a) (c : ZMod q) :
    (∑ n ∈ Finset.range L, g ((n : ZMod q)+c)) ≤
      ((L/q+1 : ℕ) : ℝ)*∑ a : ZMod q, g a := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hL : L ≤ (L/q+1)*q := by
    have hd := Nat.mod_add_div L q
    have hr := Nat.mod_lt L hq
    nlinarith
  calc
    _ ≤ ∑ n ∈ Finset.range ((L/q+1)*q), g ((n : ZMod q)+c) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hL)
        (fun n _ _ => hg _)
    _ = _ := repeated_residue_periods q (L/q+1) g c

theorem symmetric_window_reindex (q h : ℕ) [NeZero q] (g : ZMod q → ℝ) :
    (∑ k ∈ Finset.Icc (-(h : ℤ)) (h : ℤ), g (k : ZMod q)) =
      ∑ n ∈ Finset.range (2*h+1), g ((n : ZMod q)-(h : ZMod q)) := by
  apply Finset.sum_bij (fun k _ => (k+(h : ℤ)).toNat)
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    apply Finset.mem_range.mpr
    omega
  · intro k hk l hl hkl
    have hk' := Finset.mem_Icc.mp hk
    have hl' := Finset.mem_Icc.mp hl
    omega
  · intro n hn
    have hn' := Finset.mem_range.mp hn
    refine ⟨(n : ℤ)-(h : ℤ), Finset.mem_Icc.mpr (by omega), ?_⟩
    simp
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have he : (((k+(h : ℤ)).toNat : ℕ) : ℤ) = k+(h : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    have hz := congrArg (fun t : ℤ => (t : ZMod q)) he
    simp only [Int.cast_natCast, Int.cast_add] at hz
    rw [hz]
    ring_nf

/-- Explicit finite window energy; there is no prime-distribution hypothesis. -/
theorem ramanujan_window_energy_le (q : ℕ) [NeZero q] (H : ℝ)
    (hH : 1 ≤ H) (hqH : (q : ℝ) ≤ H) :
    (∑ k ∈ GoldbachCircleMethodSignedWindowFourierAdapterV18130.shiftCarrier H,
      ‖unitCharacterSum q (k : ZMod q)‖^2) ≤ 4*H*(q : ℝ) := by
  let L := 2*⌊H⌋₊+1
  have h := incomplete_residue_sum_le q L
    (fun a => ‖unitCharacterSum q a‖^2) (fun _ => sq_nonneg _)
    (-(⌊H⌋₊ : ZMod q))
  rw [ramanujan_period_energy] at h
  have hh : (⌊H⌋₊ : ℝ) ≤ H := Nat.floor_le (by linarith)
  have hd : ((L/q : ℕ) : ℝ)*(q : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self L q
  have ht : (q.totient : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.totient_le q
  have hcoeff : (((L/q+1 : ℕ) : ℝ)*(q : ℝ)) ≤ 4*H := by
    have he : (L : ℝ) = 2*(⌊H⌋₊ : ℝ)+1 := by dsimp [L]; push_cast; ring
    push_cast
    nlinarith
  unfold GoldbachCircleMethodSignedWindowFourierAdapterV18130.shiftCarrier
  rw [symmetric_window_reindex q ⌊H⌋₊ (fun a => ‖unitCharacterSum q a‖^2)]
  simp only [sub_eq_add_neg] 
  calc
    _ ≤ ((L/q+1 : ℕ) : ℝ)*((q : ℝ)*(q.totient : ℝ)) := h
    _ = (((L/q+1 : ℕ) : ℝ)*(q : ℝ))*(q.totient : ℝ) := by ring
    _ ≤ (4*H)*(q : ℝ) :=
      mul_le_mul hcoeff ht (Nat.cast_nonneg _) (by positivity)

open GoldbachCircleMethodSignedWindowFourierAdapterV18130
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodRemovedConvolutionNormV18123

theorem signed_shift_card (H : ℝ) :
    (shiftCarrier H).card = 2*⌊H⌋₊+1 := by
  unfold shiftCarrier
  rw [Int.card_Icc]
  omega

/-- A deliberately nonoptimal explicit mean bound sufficient for the scale gate. -/
theorem ramanujan_window_l1_le (q : ℕ) [NeZero q] (H : ℝ)
    (hH : 1 ≤ H) (hqH : (q : ℝ) ≤ H) :
    (∑ k ∈ shiftCarrier H, ‖unitCharacterSum q (k : ZMod q)‖) ≤
      4*H*Real.sqrt (q : ℝ) := by
  have he := ramanujan_window_energy_le q H hH hqH
  have hc : ((shiftCarrier H).card : ℝ) ≤ 3*H := by
    rw [signed_shift_card]
    have hh := Nat.floor_le (show 0 ≤ H by linarith)
    push_cast
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (shiftCarrier H)
    (fun _ : ℤ => (1 : ℝ)) (fun k => ‖unitCharacterSum q (k : ZMod q)‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hs : 0 ≤ ∑ k ∈ shiftCarrier H, ‖unitCharacterSum q (k : ZMod q)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have he0 : 0 ≤ ∑ k ∈ shiftCarrier H, ‖unitCharacterSum q (k : ZMod q)‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb := (hcs.trans (mul_le_mul hc he he0 (by positivity)))
  have hr : (4*H*Real.sqrt (q : ℝ))^2 = 16*H^2*(q : ℝ) := by
    calc
      _ = 16*H^2*(Real.sqrt (q : ℝ))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg q)]
  apply (sq_le_sq₀ hs (by positivity : 0 ≤ 4*H*Real.sqrt (q : ℝ))).mp
  rw [hr]
  nlinarith [mul_nonneg (sq_nonneg H) (Nat.cast_nonneg q)]

/-- Genuine signed window kernel L1 bound, retaining all moduli and the
original real-radius normalization 1/(2H). -/
theorem signed_kernel_l1_le (Q : ℕ) (H : ℝ) (hH : 1 ≤ H)
    (hQH : (Q : ℝ) ≤ H) (w : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ q : PositiveLevel Q, ‖w q.val‖ ≤ M) :
    (∑ k ∈ shiftCarrier H, ‖signedWindowKernel Q H w k‖) ≤
      2*M*(Q : ℝ)*Real.sqrt (Q : ℝ) := by
  have hHpos : 0 < H := by linarith
  have hinv : 0 ≤ (2*H)⁻¹ := by positivity
  have hn : ‖(2*(H : ℂ))⁻¹‖ = (2*H)⁻¹ := by
    simp [norm_inv, Complex.norm_real, abs_of_pos hHpos]
  have hp (k : ℤ) (hk : k ∈ shiftCarrier H) :
      ‖signedWindowKernel Q H w k‖ ≤
        (2*H)⁻¹*∑ q : PositiveLevel Q, M*‖unitCharacterSum q.val (k : ZMod q.val)‖ := by
    rw [signedWindowKernel, if_pos ((mem_shift_carrier H hHpos.le k).mp hk),
      norm_mul, hn]
    apply mul_le_mul_of_nonneg_left _ hinv
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hw q) (norm_nonneg _)
  calc
    _ ≤ ∑ k ∈ shiftCarrier H, (2*H)⁻¹ *
        ∑ q : PositiveLevel Q, M*‖unitCharacterSum q.val (k : ZMod q.val)‖ :=
      Finset.sum_le_sum hp
    _ = (2*H)⁻¹*∑ q : PositiveLevel Q,
        M*∑ k ∈ shiftCarrier H, ‖unitCharacterSum q.val (k : ZMod q.val)‖ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ (2*H)⁻¹*∑ _q : PositiveLevel Q, M*(4*H*Real.sqrt (Q : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hinv
      apply Finset.sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ hM
      have hqQ : (q.val : ℝ) ≤ (Q : ℝ) :=
        Nat.cast_le.mpr (Finset.mem_Icc.mp q.property).2
      apply (ramanujan_window_l1_le q.val H hH (hqQ.trans hQH)).trans
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqQ) (by positivity)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, positive_level_card]
      field_simp
      ring

end GoldbachCircleMethodFiniteRamanujanEnergyV18131
