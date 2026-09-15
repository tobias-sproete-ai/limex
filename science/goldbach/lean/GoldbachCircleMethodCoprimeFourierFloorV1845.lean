import GoldbachCircleMethodSquarefreeFourierBindingV1844

/-! # V1.8.45: exact same-carrier Fourier floor composition -/

open scoped BigOperators

namespace GoldbachCircleMethodCoprimeFourierFloorV1845

open GoldbachCircleMethodFinitePrimeProductFloorV1838
open GoldbachCircleMethodSquarefreeCoefficientBindingV1839
open GoldbachCircleMethodSquarefreeFourierBindingV1844

/-- The `μ² c_d(N) / φ(d)²` Fourier sum is exactly the V1.8.38 signed subset sum,
without enlarging the V1.8.39 carrier. -/
theorem boundedMuSquaredFourierCoefficientSum_eq_boundedSignedPrimeSum
    (N R H : ℕ) :
    boundedMuSquaredFourierCoefficientSum N R H = boundedSignedPrimeSum N R H := by
  rw [boundedMuSquaredFourierCoefficientSum_eq_moebius_totient,
    boundedSignedPrimeSum_eq_moebius_totient_sum]
  conv_rhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]

/-- The already kernel-checked finite product floor transfers to the genuine Fourier sum on
the same bounded squarefree carrier. -/
theorem boundedMuSquaredFourierCoefficientSum_ge_two_sub_exp
    {N R H : ℕ} (hEven : Even N) (hH : 1 ≤ H) :
    2 - Real.exp (Real.pi ^ 2 / 24) ≤ boundedMuSquaredFourierCoefficientSum N R H := by
  rw [boundedMuSquaredFourierCoefficientSum_eq_boundedSignedPrimeSum]
  exact boundedSignedPrimeSum_ge_two_sub_exp hEven hH

end GoldbachCircleMethodCoprimeFourierFloorV1845
