import GoldbachCircleMethodActiveExceptionalCenteringV18129

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

namespace GoldbachCircleMethodSignedWindowFourierAdapterV18130

/-- Symmetric signed-integer shifts; negative displacements are not truncated. -/
noncomputable def shiftCarrier (H : ℝ) : Finset ℤ :=
  Finset.Icc (-(⌊H⌋₊ : ℤ)) (⌊H⌋₊ : ℤ)

theorem mem_shift_carrier (H : ℝ) (hH : 0 ≤ H) (k : ℤ) :
    k ∈ shiftCarrier H ↔ |(k : ℝ)| ≤ H := by
  have ha : |(k : ℝ)| = (k.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [ha, ← Nat.le_floor_iff hH]
  unfold shiftCarrier
  rw [Finset.mem_Icc, ← abs_le, ← Int.natCast_natAbs]
  exact_mod_cast (Iff.rfl : k.natAbs ≤ ⌊H⌋₊ ↔ k.natAbs ≤ ⌊H⌋₊)

noncomputable def signedWindowKernel (Q : ℕ) (H : ℝ) (w : ℕ → ℂ) (k : ℤ) : ℂ :=
  if |(k : ℝ)| ≤ H then
    (2*(H : ℂ))⁻¹ * ∑ q : PositiveLevel Q, w q.val * unitCharacterSum q.val (k : ZMod q.val)
  else 0

theorem signed_kernel_eq_zero_outside (Q : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (w : ℕ → ℂ) (k : ℤ) (hk : k ∉ shiftCarrier H) :
    signedWindowKernel Q H w k = 0 := by
  simp only [signedWindowKernel, (mem_shift_carrier H hH k).not.mp hk, if_false]

noncomputable def signedWindowConvolution (Q B : ℕ) (H : ℝ)
    (f w : ℕ → ℂ) (n : ℤ) : ℂ :=
  ∑ U ∈ blockCarrier B, f U * signedWindowKernel Q H w (n-(U : ℤ))

/-- Pointwise binding to the unchanged V119 natural-index operator. -/
theorem signed_convolution_at_nat (Q B N : ℕ) (H : ℝ) (f w : ℕ → ℂ) :
    signedWindowConvolution Q B H f w (N : ℤ) =
      normalizedWindowConvolution Q N H (blockCarrier B) f w := by
  unfold signedWindowConvolution signedWindowKernel normalizedWindowConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U _
  simp only [Int.cast_sub, Int.cast_natCast]
  split_ifs <;> ring

/-- Full output support, including the two outside strips. -/
noncomputable def outputCarrier (B : ℕ) (H : ℝ) : Finset ℤ :=
  Finset.Ioc (((B/2 : ℕ) : ℤ)-(⌊H⌋₊ : ℤ)) ((B : ℤ)+(⌊H⌋₊ : ℤ))

theorem shifted_kernel_support (B U : ℕ) (hU : U ∈ blockCarrier B)
    (H : ℝ) (k : ℤ) (hk : k ∈ shiftCarrier H) :
    (U : ℤ)+k ∈ outputCarrier B H := by
  have hu := Finset.mem_Ioc.mp hU
  have hkr := Finset.mem_Icc.mp hk
  apply Finset.mem_Ioc.mpr
  constructor <;> omega

theorem signed_convolution_eq_zero_outside (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (f w : ℕ → ℂ) (n : ℤ) (hn : n ∉ outputCarrier B H) :
    signedWindowConvolution Q B H f w n = 0 := by
  unfold signedWindowConvolution
  apply Finset.sum_eq_zero
  intro U hU
  have hk : n-(U : ℤ) ∉ shiftCarrier H := by
    intro hm
    have hh := shifted_kernel_support B U hU H (n-(U : ℤ)) hm
    have heq : (U : ℤ)+(n-(U : ℤ))=n := by ring
    exact hn (heq ▸ hh)
  rw [signed_kernel_eq_zero_outside Q H hH w _ hk, mul_zero]

theorem shifted_kernel_fourier_sum (Q B U : ℕ) (hU : U ∈ blockCarrier B)
    (H : ℝ) (hH : 0 ≤ H) (w : ℕ → ℂ) (x : UnitAddCircle) :
    (∑ n ∈ outputCarrier B H,
      signedWindowKernel Q H w (n-(U : ℤ)) * fourier n x) =
    ∑ k ∈ shiftCarrier H, signedWindowKernel Q H w k * fourier ((U : ℤ)+k) x := by
  let S : Finset ℤ := (shiftCarrier H).image (fun k => (U : ℤ)+k)
  have hs : S ⊆ outputCarrier B H := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨k, hk, rfl⟩
    exact shifted_kernel_support B U hU H k hk
  have hz : ∀ n ∈ outputCarrier B H, n ∉ S →
      signedWindowKernel Q H w (n-(U : ℤ))*fourier n x = 0 := by
    intro n _ hn
    have hk : n-(U : ℤ) ∉ shiftCarrier H := by
      intro hm
      apply hn
      exact Finset.mem_image.mpr ⟨n-(U : ℤ), hm, by ring⟩
    rw [signed_kernel_eq_zero_outside Q H hH w _ hk, zero_mul]
  rw [← Finset.sum_subset hs hz]
  dsimp only [S]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro k _
    simp only [add_sub_cancel_left]
  · intro k _ l _ h
    exact add_left_cancel h

/-- Fourier product for the full, genuinely supported signed convolution. -/
theorem full_convolution_fourier_product (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (f w : ℕ → ℂ) (x : UnitAddCircle) :
    (∑ n ∈ outputCarrier B H, signedWindowConvolution Q B H f w n * fourier n x) =
    (∑ U ∈ blockCarrier B, f U * fourier (U : ℤ) x) *
    (∑ k ∈ shiftCarrier H, signedWindowKernel Q H w k * fourier k x) := by
  unfold signedWindowConvolution
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro U hU
  have hs := shifted_kernel_fourier_sum Q B U hU H hH w x
  calc
    (∑ n ∈ outputCarrier B H,
      (f U*signedWindowKernel Q H w (n-(U : ℤ)))*fourier n x) =
        f U * (∑ n ∈ outputCarrier B H,
          signedWindowKernel Q H w (n-(U : ℤ))*fourier n x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = f U*(∑ k ∈ shiftCarrier H,
        signedWindowKernel Q H w k * fourier ((U : ℤ)+k) x) := by rw [hs]
    _ = _ := by
      simp only [fourier_add, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring


noncomputable def integerBlock (B : ℕ) : Finset ℤ :=
  (blockCarrier B).image (fun N : ℕ => (N : ℤ))

theorem integer_block_subset_output (B : ℕ) (H : ℝ) :
    integerBlock B ⊆ outputCarrier B H := by
  intro n hn
  rcases Finset.mem_image.mp hn with ⟨N, hN, rfl⟩
  have hh := shifted_kernel_support B N hN H 0 (Finset.mem_Icc.mpr (by omega))
  simpa only [add_zero] using hh

theorem output_carrier_card (B : ℕ) (H : ℝ) :
    (outputCarrier B H).card = B-B/2+2*⌊H⌋₊ := by
  unfold outputCarrier
  rw [Int.card_Ioc]
  have hB := Nat.div_le_self B 2
  omega

theorem integer_block_card (B : ℕ) : (integerBlock B).card = B-B/2 := by
  unfold integerBlock
  rw [Finset.card_image_of_injective _ Nat.cast_injective]
  simp only [blockCarrier, Nat.card_Ioc]

/-- Exact outside-strip count; these terms are not silently discarded. -/
theorem outside_output_card (B : ℕ) (H : ℝ) :
    (outputCarrier B H \ integerBlock B).card = 2*⌊H⌋₊ := by
  rw [Finset.card_sdiff_of_subset (integer_block_subset_output B H),
    output_carrier_card, integer_block_card]
  omega

theorem restricted_convolution_fourier_identity (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (f w : ℕ → ℂ) (x : UnitAddCircle) :
    (∑ N ∈ blockCarrier B, normalizedWindowConvolution Q N H (blockCarrier B) f w *
      fourier (N : ℤ) x) =
    (∑ U ∈ blockCarrier B, f U * fourier (U : ℤ) x) *
      (∑ k ∈ shiftCarrier H, signedWindowKernel Q H w k * fourier k x) -
    (∑ n ∈ outputCarrier B H \ integerBlock B,
      signedWindowConvolution Q B H f w n * fourier n x) := by
  have he :
      (∑ n ∈ integerBlock B, signedWindowConvolution Q B H f w n * fourier n x) =
      (∑ N ∈ blockCarrier B, normalizedWindowConvolution Q N H (blockCarrier B) f w *
        fourier (N : ℤ) x) := by
    unfold integerBlock
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro N _
      rw [signed_convolution_at_nat]
    · intro N _ U _ h
      exact Nat.cast_injective h
  have hs := Finset.sum_sdiff
    (f := fun n => signedWindowConvolution Q B H f w n * fourier n x)
    (integer_block_subset_output B H)
  rw [he, full_convolution_fourier_product Q B H hH f w x] at hs
  exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using hs)

theorem input_minus_restricted_fourier_identity (Q B : ℕ) (H : ℝ) (hH : 0 ≤ H)
    (f w : ℕ → ℂ) (x : UnitAddCircle) :
    (∑ N ∈ blockCarrier B, f N * fourier (N : ℤ) x) -
      (∑ N ∈ blockCarrier B, normalizedWindowConvolution Q N H (blockCarrier B) f w *
        fourier (N : ℤ) x) =
    (∑ N ∈ blockCarrier B, f N * fourier (N : ℤ) x) *
      (1 - ∑ k ∈ shiftCarrier H, signedWindowKernel Q H w k * fourier k x) +
    (∑ n ∈ outputCarrier B H \ integerBlock B,
      signedWindowConvolution Q B H f w n * fourier n x) := by
  rw [restricted_convolution_fourier_identity Q B H hH f w x]
  ring

theorem outside_output_fourier_norm_le (Q B : ℕ) (H : ℝ) (f w : ℕ → ℂ)
    (x : UnitAddCircle) :
    ‖∑ n ∈ outputCarrier B H \ integerBlock B,
      signedWindowConvolution Q B H f w n * fourier n x‖ ≤
    ∑ n ∈ outputCarrier B H \ integerBlock B, ‖signedWindowConvolution Q B H f w n‖ := by
  calc
    _ ≤ ∑ n ∈ outputCarrier B H \ integerBlock B,
        ‖signedWindowConvolution Q B H f w n * fourier n x‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _
      simp [fourier_apply, Circle.norm_coe]

end GoldbachCircleMethodSignedWindowFourierAdapterV18130
