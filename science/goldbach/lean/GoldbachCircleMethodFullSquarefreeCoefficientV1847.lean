import GoldbachCircleMethodFullSquarefreeCarrierV1846

/-!
# V1.8.47: pointwise full squarefree Fourier coefficient split
No sum positivity, analytic operator estimate or Goldbach claim is made.
-/
open scoped BigOperators
namespace GoldbachCircleMethodFullSquarefreeCoefficientV1847
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodRamanujanCharacterProductV1843
open GoldbachCircleMethodSquarefreeFourierBindingV1844
open GoldbachCircleMethodFullSquarefreeCarrierV1846

/-- Exact unit count: if the modulus divides N, every character value is one. -/
theorem finiteFourierRamanujan_eq_totient_of_dvd
    {a N : ℕ} (ha : a ≠ 0) (haN : a ∣ N) :
    finiteFourierRamanujan a N ha = (Nat.totient a : ℂ) := by
  have : NeZero a := ⟨ha⟩
  classical
  have hNzero : (N : ZMod a) = 0 := by
    obtain ⟨k, rfl⟩ := haN
    simp
  have hu : Fintype.card {x : ZMod a // IsUnit x} = Nat.totient a := by
    rw [← ZMod.card_units_eq_totient a]
    apply Fintype.card_congr
    exact (Equiv.ofBijective
      (fun u : (ZMod a)ˣ => (⟨(u : ZMod a), u.isUnit⟩ : {x : ZMod a // IsUnit x}))
      ⟨fun u v h => Units.ext (congrArg Subtype.val h),
        fun ⟨x, hx⟩ => by
          obtain ⟨u, rfl⟩ := hx
          exact ⟨u, rfl⟩⟩).symm
  simp only [finiteFourierRamanujan, hNzero, mul_zero, AddChar.map_zero_eq_one]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun x : ZMod a => IsUnit x)).card =
      Nat.totient a := by
    simpa only [Fintype.card_subtype] using hu
  exact_mod_cast hcard

/-- The q=a*b split evaluated on the existing, genuinely Fourier-defined coefficient. -/
theorem finiteFourierRamanujan_pair_eq_totient_mul_moebius
    {a b N R H : ℕ} (h : (a, b) ∈ coupledSquarefreePairs N H) (hHR : H ≤ R) :
    finiteFourierRamanujan (a * b) N
        (mem_fullSquarefreePrefix.mp (pair_product_mem h)).2.ne_zero =
      (Nat.totient a : ℂ) * ((ArithmeticFunction.moebius b : ℤ) : ℂ) := by
  obtain ⟨ha, hb, haN, _, _⟩ := mem_coupledSquarefreePairs.mp h
  rw [finiteFourierRamanujan_mul_of_coprime ha.ne_zero hb.ne_zero
    (pair_factors_coprime h) N, finiteFourierRamanujan_eq_totient_of_dvd ha.ne_zero haN,
    finiteFourierRamanujan_eq_moebius_of_mem (complement_mem_existing_carrier h hHR)]

/-- Real coefficient factorization retains both coupled factors. -/
theorem pair_real_coefficient_split
    {a b N R H : ℕ} (h : (a, b) ∈ coupledSquarefreePairs N H) (hHR : H ≤ R) :
    (finiteFourierRamanujan (a * b) N
      (mem_fullSquarefreePrefix.mp (pair_product_mem h)).2.ne_zero).re /
        ((Nat.totient (a * b) : ℝ) ^ 2) =
      (1 / (Nat.totient a : ℝ)) *
        (((ArithmeticFunction.moebius b : ℤ) : ℝ) / (Nat.totient b : ℝ) ^ 2) := by
  have ha := (mem_coupledSquarefreePairs.mp h).1
  have hphi : (Nat.totient a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr ha.ne_zero.bot_lt).ne'
  rw [finiteFourierRamanujan_pair_eq_totient_mul_moebius h hHR,
    Nat.totient_mul (pair_factors_coprime h)]
  push_cast
  simp only [Complex.mul_re, Complex.natCast_re, Complex.intCast_re,
    Complex.natCast_im, Complex.intCast_im, mul_zero, sub_zero]
  field_simp

end GoldbachCircleMethodFullSquarefreeCoefficientV1847
