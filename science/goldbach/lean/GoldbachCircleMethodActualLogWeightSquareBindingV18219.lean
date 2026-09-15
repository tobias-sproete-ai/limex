import GoldbachCircleMethodActualCoupledDiagonalRealReadbackV18218
import GoldbachCircleMethodLogCutoffPresieveBindingV18120

/-!
# V1.8.219: actual log-weight square binding

The actual frozen diagonal contains two denominator weights.  When both are
the V1.8.120 `logWeight R G`, their product is the real square
`G (log q / log R)^2`.  This module binds that product exactly and discharges
the V1.8.218 finite Abel hypotheses from an explicit nonnegative-antitone
contract for `G` on the only interval used by the cutoff, `[0,2]`.

Smoothness and compact support do not appear in the proof and are not claimed
to imply this order contract.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualLogWeightSquareBindingV18219

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodActualFrozenModelCompleteDiagonalV18213
open GoldbachCircleMethodActualCoupledDiagonalRealReadbackV18218
open GoldbachCircleMethodLogCutoffPresieveBindingV18120

/-- The literal real product of the two identical V1.8.120 log weights. -/
noncomputable def squaredLogWeightReal
    (R : ℝ) (G : ℝ → ℝ) (q : ℕ) : ℝ :=
  (G (Real.log (q : ℝ) / Real.log R)) ^ 2

/-- Two actual complex log weights equal the complex embedding of their
real square, pointwise and without a phase approximation. -/
theorem logWeight_mul_self
    (R : ℝ) (G : ℝ → ℝ) (q : ℕ) :
    logWeight R G q * logWeight R G q =
      (squaredLogWeightReal R G q : ℂ) := by
  simp [logWeight, squaredLogWeightReal, pow_two]

/-- Exact specialization of the unchanged V1.8.213 coupled diagonal to the
single real square consumed by V1.8.218. -/
theorem coupledDiagonal_logWeight_square_eq
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (N : ℕ) (R : ℝ) (G : ℝ → ℝ) :
    coupledDiagonal hK r (logWeight R G) (logWeight R G)
        (N : ZMod K) =
      coupledDiagonal hK r
        (fun q => (squaredLogWeightReal R G q : ℂ))
        (fun _ => 1) (N : ZMod K) := by
  unfold coupledDiagonal
  apply Finset.sum_congr rfl
  intro l _
  by_cases hcut : r.val * l.val ≤ Q ∧ Nat.Coprime r.val l.val
  · rw [if_pos hcut, if_pos hcut]
    simp only [logWeight, squaredLogWeightReal, Complex.ofReal_pow]
    ring
  · simp [hcut]

/-- Real readback of the actual two-log-weight diagonal at its exact quotient
cutoff. -/
theorem coupledDiagonal_logWeight_square_re
    {Q K : ℕ} [NeZero K]
    (hK : ∀ q : PositiveLevel Q, q.val ∣ K)
    (r : PositiveLevel Q) (N : ℕ) (R : ℝ) (G : ℝ → ℝ) :
    (coupledDiagonal hK r (logWeight R G) (logWeight R G)
        (N : ZMod K)).re =
      actualRealWeightedCoupledPrefix N Q r.val
        (squaredLogWeightReal R G) := by
  rw [coupledDiagonal_logWeight_square_eq hK r N R G]
  exact coupledDiagonal_re_eq_actualRealWeightedCoupledPrefix
    hK r N (squaredLogWeightReal R G)

/-- Every admitted positive natural level maps into the exact logarithmic
support interval `[0,2]`. -/
theorem log_ratio_mem_Icc
    (R : ℝ) (hR : 1 < R) (q : ℕ) (hq : 1 ≤ q)
    (hcut : q ≤ ⌊R ^ 2⌋₊) :
    Real.log (q : ℝ) / Real.log R ∈ Set.Icc (0 : ℝ) 2 := by
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one hq
  constructor
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hq)) hlogR.le
  · exact (log_cutoff_iff R hR q hqpos).2 hcut

/-- The squared actual log weight is nonincreasing on every positive
conductor ray inside the exact cutoff, provided `G` is nonnegative and
antitone on `[0,2]`. -/
theorem squaredLogWeightReal_conductor_antitone
    (R : ℝ) (hR : 1 < R) (G : ℝ → ℝ)
    (hGnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 2, 0 ≤ G x)
    (hGanti : AntitoneOn G (Set.Icc (0 : ℝ) 2))
    {Q r : ℕ} (hQ : Q = ⌊R ^ 2⌋₊) (hr : 0 < r)
    (l : ℕ) (hl : 1 ≤ l) (hlt : l < Q / r) :
    squaredLogWeightReal R G (r * (l + 1)) ≤
      squaredLogWeightReal R G (r * l) := by
  have hl1 : l + 1 ≤ Q / r := by omega
  have hq1pos : 1 ≤ r * l := by nlinarith
  have hq2pos : 1 ≤ r * (l + 1) := by nlinarith
  have hq1cut : r * l ≤ Q := by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hr).mp
      ((le_trans (Nat.le_add_right l 1) hl1))
  have hq2cut : r * (l + 1) ≤ Q := by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hr).mp hl1
  let x₁ : ℝ := Real.log ((r * l : ℕ) : ℝ) / Real.log R
  let x₂ : ℝ := Real.log ((r * (l + 1) : ℕ) : ℝ) / Real.log R
  have hx1 : x₁ ∈ Set.Icc (0 : ℝ) 2 := by
    dsimp [x₁]
    exact log_ratio_mem_Icc R hR (r * l) hq1pos (hQ ▸ hq1cut)
  have hx2 : x₂ ∈ Set.Icc (0 : ℝ) 2 := by
    dsimp [x₂]
    exact log_ratio_mem_Icc R hR (r * (l + 1)) hq2pos (hQ ▸ hq2cut)
  have hnat : r * l ≤ r * (l + 1) := Nat.mul_le_mul_left r (by omega)
  have hcast : (((r * l : ℕ) : ℝ)) ≤ (((r * (l + 1) : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  have hx12 : x₁ ≤ x₂ := by
    dsimp [x₁, x₂]
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hq1pos) hcast)
      (Real.log_pos hR).le
  have hGle : G x₂ ≤ G x₁ := hGanti hx1 hx2 hx12
  have hG1 : 0 ≤ G x₁ := hGnonneg x₁ hx1
  have hG2 : 0 ≤ G x₂ := hGnonneg x₂ hx2
  dsimp [squaredLogWeightReal, x₁, x₂] at *
  nlinarith

/-- Conditional lower floor for the real part of the actual two-log-weight
coupled diagonal.  The remaining order assumptions are explicit properties
of `G`, not consequences of smoothness or compact support. -/
theorem conditional_actual_logWeight_square_floor
    {K N : ℕ} [NeZero K]
    (R : ℝ) (hR : 1 < R)
    (hK : ∀ q : PositiveLevel ⌊R ^ 2⌋₊, q.val ∣ K)
    (r : PositiveLevel ⌊R ^ 2⌋₊) (hEven : Even N)
    (G : ℝ → ℝ)
    (hGnonneg : ∀ x ∈ Set.Icc (0 : ℝ) 2, 0 ≤ G x)
    (hGanti : AntitoneOn G (Set.Icc (0 : ℝ) 2)) :
    (2 - Real.exp (Real.pi ^ 2 / 24)) *
        (G (Real.log (r.val : ℝ) / Real.log R)) ^ 2 ≤
      (coupledDiagonal hK r (logWeight R G) (logWeight R G)
        (N : ZMod K)).re := by
  rw [coupledDiagonal_logWeight_square_eq hK r N R G]
  have hlast :
      0 ≤ squaredLogWeightReal R G
        (r.val * (⌊R ^ 2⌋₊ / r.val)) := sq_nonneg _
  have hmono : ∀ l, 1 ≤ l → l < ⌊R ^ 2⌋₊ / r.val →
      squaredLogWeightReal R G (r.val * (l + 1)) ≤
        squaredLogWeightReal R G (r.val * l) := by
    intro l hl hlt
    exact squaredLogWeightReal_conductor_antitone R hR G hGnonneg hGanti
      rfl (Nat.pos_of_ne_zero (NeZero.ne r.val)) l hl hlt
  simpa [squaredLogWeightReal] using
    (conditional_actual_coupledDiagonal_real_floor hK r hEven
      (squaredLogWeightReal R G) hlast hmono)

end GoldbachCircleMethodActualLogWeightSquareBindingV18219
