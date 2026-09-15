import GoldbachCircleMethodDiscreteArcTailV1854

/-! # V1.8.55: instantiate the finite adapter with the actual discrete integrals.
This is the arithmetic discrete arc MODEL, not the von-Mangoldt major integral.
The latter still requires its geometric/approximation bridge.
-/
open scoped BigOperators
open GoldbachCircleMethodSignedFullPrefixV1850
open GoldbachCircleMethodFiniteRemainderBudgetV1851
open GoldbachCircleMethodDiscreteArcTailV1854

namespace GoldbachCircleMethodDiscreteArcModelReserveV1855

noncomputable def discreteArcMainModel (M N R : ℕ) (P : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 R, signedMajorCoefficient N q *
    (localDiscreteMainIntegral M N (P / ((q : ℝ)*(M : ℝ)))).re

theorem discrete_arc_pointwise_remainder (M N q : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (hq : 1 ≤ q) (P : ℝ) (hP : 0 < P) (hcap : 2*P ≤ (M : ℝ)) :
    |(localDiscreteMainIntegral M N (P/((q : ℝ)*(M : ℝ)))).re - ((N : ℝ)-1)| ≤
      ((M : ℝ)/(2*P))*(q : ℝ) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have ht : 0 < P/((q : ℝ)*(M : ℝ)) := by positivity
  have htop : P/((q : ℝ)*(M : ℝ)) ≤ 1/2 := by
    apply (div_le_iff₀ (mul_pos hq0 hM)).mpr
    nlinarith
  have h := localDiscreteMainIntegral_real_tail_bound M N hN hNM
    (P/((q : ℝ)*(M : ℝ))) ht htop
  convert h using 1
  field_simp

theorem discreteArcMainModel_remainder (M N R : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (P : ℝ) (hP : 0 < P) (hcap : 2*P ≤ (M : ℝ)) :
    |discreteArcMainModel M N R P - ((N : ℝ)-1) *
      (∑ q ∈ Finset.Icc 1 R, signedMajorCoefficient N q)| ≤
        ((M : ℝ)/(2*P))*(R : ℝ)^2 := by
  apply finite_remainder_bound N R
    (fun q => (localDiscreteMainIntegral M N (P/((q : ℝ)*(M : ℝ)))).re)
    ((N : ℝ)-1) ((M : ℝ)/(2*P)) (by positivity)
  intro q hq
  exact discrete_arc_pointwise_remainder M N q hN hNM (Finset.mem_Icc.mp hq).1 P hP hcap

theorem discreteArcMainModel_lower_bound (M N R : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (hEven : Even N) (hR : 1 ≤ R) (P : ℝ) (hP : 0 < P) (hcap : 2*P ≤ (M : ℝ)) :
    ((N : ℝ)-1)*(2/7 : ℝ) - ((M : ℝ)/(2*P))*(R : ℝ)^2 ≤
      discreteArcMainModel M N R P := by
  apply finite_reserve_from_pointwise_remainder hEven hR
    (fun q => (localDiscreteMainIntegral M N (P/((q : ℝ)*(M : ℝ)))).re)
    ((N : ℝ)-1) ((M : ℝ)/(2*P))
  · have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  · positivity
  · intro q hq
    exact discrete_arc_pointwise_remainder M N q hN hNM (Finset.mem_Icc.mp hq).1 P hP hcap

theorem discreteArcMainModel_ge_one_fourteenth (M N R : ℕ)
    (hN : 2 ≤ N) (hNM : N ≤ M) (hEven : Even N) (hR : 1 ≤ R)
    (hblock : (M : ℝ)/2 ≤ N) (P : ℝ) (hP : 0 < P) (hcap : 2*P ≤ (M : ℝ))
    (hbudget : (2/7 : ℝ) + ((M : ℝ)/(2*P))*(R : ℝ)^2 ≤ (M : ℝ)/14) :
    (M : ℝ)/14 ≤ discreteArcMainModel M N R P := by
  have h := discreteArcMainModel_lower_bound M N R hN hNM hEven hR P hP hcap
  linarith

end GoldbachCircleMethodDiscreteArcModelReserveV1855
