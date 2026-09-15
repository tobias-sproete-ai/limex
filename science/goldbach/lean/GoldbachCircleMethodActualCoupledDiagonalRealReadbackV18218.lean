import GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
import GoldbachCircleMethodConditionalWeightedBindingPreflightV18217
import GoldbachCircleMethodSignedFullPrefixV1850

/-!
# V1.8.218: actual coupled-diagonal real readback

This module binds the real part of the already frozen V1.8.213
`coupledDiagonal` to the exact finite conductor-threshold sum used by the
V1.8.217 Abel preflight.  The target is a natural residue `(N : ZMod K)` and
the real weight is embedded in `ℂ` without changing its product-level
argument `r*l`.

No positivity or monotonicity of an analytic mask is inferred.  The final
lower bound remains conditional on the explicit V1.8.217 weight hypotheses.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualCoupledDiagonalRealReadbackV18218

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodFullSquarefreePrefixFloorV1848
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodConditionalWeightedBindingPreflightV18217

/-- The exact real threshold sum to which the actual complex coupled
diagonal will be bound. -/
noncomputable def actualRealWeightedCoupledPrefix
    (N Q r : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 (Q / r),
    w (r * l) * restrictedRealFourierCoefficient N r l

/-- Reducing a natural residue from `ZMod K` to a divisor modulus retains
the same natural target. -/
theorem castHom_natCast {K q : ℕ} [NeZero K]
    (hq : q ∣ K) (N : ℕ) :
    ZMod.castHom hq (ZMod q) (N : ZMod K) = (N : ZMod q) := by
  simp

/-- Pointwise real readback of the genuine V1.8.213 summand.  The
`mu^2` normalization is exactly the V1.8.50 signed coefficient. -/
theorem actual_coupled_summand_re
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r l : PositiveLevel Q) (N : ℕ) (w : ℕ → ℝ) :
    (if r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val then
        (((ArithmeticFunction.moebius l.val : ℤ) : ℂ) ^ 2) /
            (l.val.totient : ℂ) ^ 2 *
          unitCharacterSum l.val
            (ZMod.castHom (hK l) (ZMod l.val) (N : ZMod K)) *
          (w (r.val * l.val) : ℂ) * 1
      else 0).re =
      if r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val then
        w (r.val * l.val) * signedMajorCoefficient N l.val
      else 0 := by
  by_cases hcut : r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · rw [if_pos hcut, if_pos hcut]
    simp only [mul_one]
    rw [castHom_natCast (hK l) N,
      ← finiteFourierRamanujan_eq_unitCharacterSum l.val N (NeZero.ne l.val),
      signedMajorCoefficient_eq_muSquared]
    simp only [realFourierCoefficient, dif_neg (NeZero.ne l.val)]
    have hscalar :
        (((ArithmeticFunction.moebius l.val : ℤ) : ℂ) ^ 2 /
          (l.val.totient : ℂ) ^ 2) =
        (((((ArithmeticFunction.moebius l.val : ℤ) : ℝ) ^ 2 /
          (l.val.totient : ℝ) ^ 2) : ℝ) : ℂ) := by
      norm_cast
    rw [hscalar]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero]
    push_cast
    ring
  · simp [hcut]

/-- The real part of the actual frozen coupled diagonal is the corresponding
finite signed-major-coefficient sum on its original positive-level carrier. -/
theorem coupledDiagonal_re_eq_positiveLevel_signed
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℝ) :
    (coupledDiagonal hK r (fun q => (w q : ℂ)) (fun _ => 1)
      (N : ZMod K)).re =
      ∑ l : PositiveLevel Q,
        if r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val then
          w (r.val * l.val) * signedMajorCoefficient N l.val
        else 0 := by
  unfold coupledDiagonal
  change Complex.reCLM
      (∑ l : PositiveLevel Q, if r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val then
        (((ArithmeticFunction.moebius l.val : ℤ) : ℂ) ^ 2) /
            (l.val.totient : ℂ) ^ 2 *
          unitCharacterSum l.val
            (ZMod.castHom (hK l) (ZMod l.val) (N : ZMod K)) *
          (w (r.val * l.val) : ℂ) * 1
        else 0) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  exact actual_coupled_summand_re hK r l N w

/-- The positive-level signed sum has exactly the quotient cutoff `Q/r`.
Nonsquarefree terms vanish by the Moebius square in V1.8.50; no term is
silently deleted. -/
theorem positiveLevel_signed_eq_actualRealWeightedCoupledPrefix
    {Q : ℕ} (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℝ) :
    (∑ l : PositiveLevel Q,
        if r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val then
          w (r.val * l.val) * signedMajorCoefficient N l.val
        else 0) =
      actualRealWeightedCoupledPrefix N Q r.val w := by
  rw [← Finset.sum_subtype (Finset.Icc 1 Q) (by intro l; rfl)
    (fun l => if r.val * l ≤ Q ∧ Nat.Coprime r.val l then
      w (r.val * l) * signedMajorCoefficient N l else 0)]
  unfold actualRealWeightedCoupledPrefix
  have hr : 0 < r.val := Nat.pos_of_ne_zero (NeZero.ne r.val)
  symm
  apply Finset.sum_subset_zero_on_sdiff
  · intro l hl
    obtain ⟨hl1, hlcut⟩ := Finset.mem_Icc.mp hl
    exact Finset.mem_Icc.mpr ⟨hl1,
      hlcut.trans (Nat.div_le_self Q r.val)⟩
  · intro l hlDiff
    obtain ⟨hlQ, hlcut⟩ := Finset.mem_sdiff.mp hlDiff
    have hnot : ¬ r.val * l ≤ Q := by
      intro hprod
      exact hlcut (Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hlQ).1, (Nat.le_div_iff_mul_le hr).mpr
          (by simpa [Nat.mul_comm] using hprod)⟩)
    simp [hnot]
  · intro l hl
    have hprod : r.val * l ≤ Q :=
      by simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hr).mp (Finset.mem_Icc.mp hl).2
    by_cases hcop : Nat.Coprime r.val l
    · by_cases hsq : Squarefree l
      · rw [if_pos ⟨hprod, hcop⟩, signedMajorCoefficient_eq_muSquared,
          ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq]
        simp [restrictedRealFourierCoefficient, hsq, hcop.symm]
      · rw [if_pos ⟨hprod, hcop⟩,
          signedMajorCoefficient_eq_zero_of_not_squarefree hsq]
        simp [restrictedRealFourierCoefficient, hsq]
    · have hcop' : ¬ Nat.Coprime l r.val := by
        intro h
        exact hcop h.symm
      simp [hprod, hcop, hcop', restrictedRealFourierCoefficient]

/-- Exact real readback at the conductor quotient threshold. -/
theorem coupledDiagonal_re_eq_actualRealWeightedCoupledPrefix
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℝ) :
    (coupledDiagonal hK r (fun q => (w q : ℂ)) (fun _ => 1)
      (N : ZMod K)).re = actualRealWeightedCoupledPrefix N Q r.val w := by
  rw [coupledDiagonal_re_eq_positiveLevel_signed hK r N w,
    positiveLevel_signed_eq_actualRealWeightedCoupledPrefix r N w]

/-- The exact readback written in the shifted range consumed by V1.8.217. -/
theorem actualRealWeightedCoupledPrefix_eq_shifted
    (N Q r : ℕ) (w : ℕ → ℝ) :
    actualRealWeightedCoupledPrefix N Q r w =
      ∑ i ∈ Finset.range (Q / r),
        w (r * (i + 1)) * restrictedRealFourierCoefficient N r (i + 1) := by
  unfold actualRealWeightedCoupledPrefix
  rw [← shifted_sum]

/-- Conditional lower floor for the real part of the actual V1.8.213
`coupledDiagonal`.  The only analytic weight facts used are the displayed
nonnegativity and monotonicity hypotheses. -/
theorem conditional_actual_coupledDiagonal_real_floor
    {Q K N : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (hEven : Even N)
    (w : ℕ → ℝ) (hlast : 0 ≤ w (r.val * (Q / r.val)))
    (hmono : ∀ l, 1 ≤ l → l < Q / r.val →
      w (r.val * (l + 1)) ≤ w (r.val * l)) :
    (2 - Real.exp (Real.pi ^ 2 / 24)) * w r.val ≤
      (coupledDiagonal hK r (fun q => (w q : ℂ)) (fun _ => 1)
        (N : ZMod K)).re := by
  rw [coupledDiagonal_re_eq_actualRealWeightedCoupledPrefix hK r N w,
    actualRealWeightedCoupledPrefix_eq_shifted]
  exact conditional_weighted_conductor_threshold_floor hEven
    (Nat.pos_of_ne_zero (NeZero.ne r.val))
    (Finset.mem_Icc.mp r.property).2 w hlast hmono

end GoldbachCircleMethodActualCoupledDiagonalRealReadbackV18218
