import GoldbachCircleMethodFiniteFourierL2MinorMomentV1872
import GoldbachCircleMethodTwoScaleDirichletBindingV1830

/-! # V1.8.73: real approximation to the original fixed minor mask.
The Vaughan-style estimate is an explicit unproved input, not an axiom.
-/
open scoped BigOperators
set_option autoImplicit false
open MeasureTheory AddCircle
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodTwoScaleMaskAdapterV1829
open GoldbachCircleMethodTwoScaleDirichletBindingV1830
open GoldbachCircleMethodTwoScaleIntegralPartitionV1831
open GoldbachCircleMethodTwoScaleBesselBridgeV1834
open GoldbachCircleMethodFiniteFourierL2MinorMomentV1872

namespace GoldbachCircleMethodRealApproximationMinorAdapterV1873

theorem exists_real_lift_near_center (x : UnitAddCircle) (y ε : ℝ)
    (hx : dist x (y : UnitAddCircle) ≤ ε) :
    ∃ β : ℝ, (β : UnitAddCircle)=x ∧ |β-y|≤ε := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hm : α ∈ ((↑) : ℝ → UnitAddCircle) ⁻¹'
      Metric.closedBall (y : UnitAddCircle) ε := hx
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion] at hm
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hm
  refine ⟨α-(z : ℝ), by simp, ?_⟩
  have hab : |α-(y+(z : ℝ))|≤ε := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, zsmul_eq_mul, mul_one] using hz
  convert hab using 1
  congr 1
  ring

noncomputable def vaughanEnvelope (M q : ℕ) (C : ℝ) : ℝ :=
  C * (Real.log (M : ℝ))^4 *
    ((M : ℝ)/Real.sqrt (q : ℝ)+(M : ℝ)^((4 : ℝ)/5)+Real.sqrt ((M : ℝ)*(q : ℝ)))

/-- A source-shaped analytic premise. This module provides no instance. -/
def RealVaughanEstimate (C : ℝ) : Prop :=
  ∀ M : ℕ, 3 ≤ M → ∀ q : ℕ, 0 < q → ∀ a : ℕ, Nat.Coprime a q →
    ∀ β : ℝ, |β-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2 →
      ‖exponentialSum M.succ (β : UnitAddCircle)‖≤vaughanEnvelope M q C

theorem circle_estimate_of_real (C : ℝ) (hV : RealVaughanEstimate C)
    (M Q : ℕ) (hM : 3 ≤ M) (i : ReducedRationalIndex Q) (x : UnitAddCircle)
    (hx : dist x (majorArcCenter i)≤1/(i.1.1 : ℝ)^2) :
    ‖exponentialSum M.succ x‖≤vaughanEnvelope M i.1.1 C := by
  obtain ⟨β, hβ, hb⟩ := exists_real_lift_near_center x
    ((i.1.2 : ℝ)/(i.1.1 : ℝ)) (1/(i.1.1 : ℝ)^2) hx
  have hc := (Finset.mem_filter.mp i.2).2.2
  simpa only [hβ] using hV M hM i.1.1 (index_denominator_pos i) i.1.2 hc β hb

theorem minor_has_admissible_estimate (C : ℝ) (hV : RealVaughanEstimate C)
    (M P Q R₀ : ℕ) (hM : 3 ≤ M) (hP : 0 < P)
    (hQ : Q=⌈(M : ℝ)/(P : ℝ)⌉₊)
    (x : UnitAddCircle) (hx : x ∈ twoScaleMinorMask M P R₀) :
    ∃ i : ReducedRationalIndex Q, R₀ < i.1.1 ∧ i.1.1 ≤ Q ∧
      ‖exponentialSum M.succ x‖≤vaughanEnvelope M i.1.1 C := by
  obtain ⟨i, hlow, hhigh, hdist⟩ := exists_dirichlet_outside_twoScaleMajorMask
    M P Q R₀ (by omega) hP hQ x hx
  refine ⟨i, hlow, hhigh, circle_estimate_of_real C hV M Q hM i x ?_⟩
  have hq : (0 : ℝ)<(i.1.1 : ℝ) := Nat.cast_pos.mpr (index_denominator_pos i)
  have hqQ : (i.1.1 : ℝ)≤(Q : ℝ) := by exact_mod_cast hhigh
  have hden : (i.1.1 : ℝ)^2≤(i.1.1 : ℝ)*(Q : ℝ) := by nlinarith
  exact hdist.trans (one_div_le_one_div_of_le (sq_pos_of_pos hq) hden)

noncomputable def minorEnvelope (M R₀ Q : ℕ) (C : ℝ) : ℝ :=
  C * (Real.log (M : ℝ))^4 *
    ((M : ℝ)/Real.sqrt (R₀ : ℝ)+(M : ℝ)^((4 : ℝ)/5)+Real.sqrt ((M : ℝ)*(Q : ℝ)))

theorem vaughanEnvelope_le_minorEnvelope (M q R₀ Q : ℕ) (C : ℝ)
    (hC : 0≤C) (hR : 0<R₀) (hlow : R₀≤q) (hhigh : q≤Q) :
    vaughanEnvelope M q C ≤ minorEnvelope M R₀ Q C := by
  unfold vaughanEnvelope minorEnvelope
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr (by exact_mod_cast hR))
    exact Real.sqrt_le_sqrt (by exact_mod_cast hlow)
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by exact_mod_cast hhigh) (by positivity))

theorem uniform_minor_bound_of_real_estimate (C : ℝ) (hC : 0≤C)
    (hV : RealVaughanEstimate C) (M P Q R₀ : ℕ) (hM : 3≤M) (hP : 0<P)
    (hR : 0<R₀) (hQ : Q=⌈(M : ℝ)/(P : ℝ)⌉₊) :
    ∀ x ∈ twoScaleMinorMask M P R₀,
      ‖exponentialSum M.succ x‖ ≤ minorEnvelope M R₀ Q C := by
  intro x hx
  obtain ⟨i, hl, hh, hi⟩ := minor_has_admissible_estimate C hV M P Q R₀ hM hP hQ x hx
  exact hi.trans (vaughanEnvelope_le_minorEnvelope M i.1.1 R₀ Q C hC hR hl.le hh)

theorem minorFourthMoment_bound_of_real_estimate (C : ℝ) (hC : 0≤C)
    (hV : RealVaughanEstimate C) (M P Q R₀ : ℕ) (hM : 3≤M) (hP : 0<P)
    (hR : 0<R₀) (hQ : Q=⌈(M : ℝ)/(P : ℝ)⌉₊) :
    minorFourthMoment M P R₀≤
      (minorEnvelope M R₀ Q C)^2*((M : ℝ)*(Real.log (M : ℝ))^2) := by
  apply minorFourthMoment_le_bound_mul_M_log_sq M P R₀ _ (sq_nonneg _)
  intro x hx
  have h := uniform_minor_bound_of_real_estimate C hC hV M P Q R₀ hM hP hR hQ x hx
  nlinarith [norm_nonneg (exponentialSum M.succ x)]

end GoldbachCircleMethodRealApproximationMinorAdapterV1873
