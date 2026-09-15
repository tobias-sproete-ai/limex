import GoldbachCircleMethodCeilScaleEnvelopesV1864

/-! # V1.8.65: the actual eventual major reserve from a full-prefix hypothesis.
The full-prefix hypothesis is NOT instantiated here. No external axiom is added.
-/
open Filter Topology
open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodFiniteAbelAdapterV1863
open GoldbachCircleMethodActualMajorReserveV1862
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831

namespace GoldbachCircleMethodUniformMajorPrefixReductionV1865

noncomputable def prefixEnvelope (M : ℕ) (C c : ℝ) : ℝ :=
  C*(M : ℝ)*Real.exp (-c*Real.sqrt (Real.log (M : ℝ)))

noncomputable def arcEnvelope (K M : ℕ) (C c : ℝ) : ℝ :=
  (1+2*Real.pi*(logWidth K M : ℝ))*prefixEnvelope M C c

def FullPrefixBound (K M : ℕ) (C c : ℝ) : Prop :=
  ∀ i : ReducedRationalIndex (logRadius K M), ∀ k ≤ M,
    ‖exponentialSum k.succ (majorArcCenter i)-
      (((ArithmeticFunction.moebius i.val.1 : ℤ) : ℂ)/(Nat.totient i.val.1 : ℂ)) *
        (k : ℂ)‖ ≤ prefixEnvelope M C c

theorem normalized_budget_identity (K M : ℕ) (C c : ℝ) (hM : 0 < M) :
    (M : ℝ)*normalizedJointBudget K M C c =
      (2/7 : ℝ) + ((M : ℝ)/(2*(logWidth K M : ℝ)))*(logRadius K M : ℝ)^2 +
        (2*(M : ℝ)*arcEnvelope K M C c+(arcEnvelope K M C c)^2)*
          (2*(logWidth K M : ℝ)*(logRadius K M : ℝ)/(M : ℝ)) := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  unfold normalizedJointBudget normalizedAbelError arcEnvelope prefixEnvelope
  field_simp

theorem actual_major_of_prefix_and_budget (K M N : ℕ) (C c : ℝ) (hC : 0 ≤ C)
    (hM : 0 < M) (hR : 1 ≤ logRadius K M) (hP : 0 < logWidth K M)
    (hscale : 2*logWidth K M*logRadius K M < M)
    (hN : 2 ≤ N) (hNM : N ≤ M) (hEven : Even N) (hblock : (M : ℝ)/2 ≤ N)
    (hprefix : FullPrefixBound K M C c)
    (hbudget : normalizedJointBudget K M C c ≤ 1/14) :
    (M : ℝ)/14 ≤ twoScaleMajorIntegralReal M (logWidth K M) (logRadius K M) N := by
  apply actual_major_ge_one_fourteenth M (logWidth K M) (logRadius K M) N
    hN hNM hEven hR hP hscale hblock (arcEnvelope K M C c)
  · unfold arcEnvelope prefixEnvelope
    positivity
  · intro i x hx
    exact original_arc_error_from_prefix M (logWidth K M) (logRadius K M) hM i x
      (prefixEnvelope M C c) (by unfold prefixEnvelope; positivity) hx (hprefix i)
  · rw [← normalized_budget_identity K M C c hM]
    have h := mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    simpa only [mul_one_div] using h

theorem eventually_actual_major_from_prefix (K : ℕ) (hK : 0 < K)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c) :
    ∀ᶠ M : ℕ in atTop, FullPrefixBound K M C c →
      ∀ N : ℕ, 4 ≤ N → N ≤ M → Even N → M ≤ 2*N →
        (M : ℝ)/14 ≤ twoScaleMajorIntegralReal M (logWidth K M) (logRadius K M) N := by
  filter_upwards [eventually_joint_scale_gate K hK C c hC hc] with M hg
  intro hp N hN hNM he hb
  apply actual_major_of_prefix_and_budget K M N C c hC hg.1 hg.2.1 hg.2.2.1
    hg.2.2.2.1 (by omega) hNM he _ hp hg.2.2.2.2
  have h : (M : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hb
  linarith

theorem uniform_major_reserve_of_eventual_prefix (K : ℕ) (hK : 0 < K)
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hprefix : ∀ᶠ M : ℕ in atTop, FullPrefixBound K M C c) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ N : ℕ, 4 ≤ N → N ≤ M → Even N → M ≤ 2*N →
      (M : ℝ)/14 ≤ twoScaleMajorIntegralReal M (logWidth K M) (logRadius K M) N := by
  apply eventually_atTop.mp
  filter_upwards [eventually_actual_major_from_prefix K hK C c hC hc, hprefix]
    with M hM hp
  exact hM hp

end GoldbachCircleMethodUniformMajorPrefixReductionV1865
