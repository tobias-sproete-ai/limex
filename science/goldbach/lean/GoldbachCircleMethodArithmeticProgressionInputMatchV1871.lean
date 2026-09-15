import GoldbachCircleMethodPrefixBudgetAbsorptionV1870

/-! # V1.8.71: semantic match to the usual finite arithmetic-progression sum.
No Siegel-Walfisz theorem or unproved instance is added.
-/
open scoped BigOperators
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodUniformResidueInputBridgeV1869
open GoldbachCircleMethodUniformMajorPrefixReductionV1865
open GoldbachCircleMethodPrefixBudgetAbsorptionV1870
open GoldbachCircleMethodCeilScaleEnvelopesV1864

namespace GoldbachCircleMethodArithmeticProgressionInputMatchV1871

noncomputable def psiAP (k q a : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 k).filter (fun n => Nat.ModEq q n a), ArithmeticFunction.vonMangoldt n

theorem psiResidue_natCast_eq_psiAP (k q a : ℕ) [NeZero q] :
    psiResidue k q (a : ZMod q) = psiAP k q a := by
  simp only [psiResidue, ZMod.natCast_eq_natCast_iff]
  unfold psiAP
  symm
  apply Finset.sum_subset
  · intro n hn
    obtain ⟨hn, ha⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hn; omega), ha⟩
  · intro n hn hnot
    obtain ⟨hn, ha⟩ := Finset.mem_filter.mp hn
    have hz : n=0 := by
      by_contra hne
      apply hnot
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨by omega, by have := Finset.mem_range.mp hn; omega⟩, ha⟩
    subst n
    simp

theorem psiResidue_eq_psiAP (k q : ℕ) [NeZero q] (r : ZMod q) :
    psiResidue k q r = psiAP k q r.val := by
  simpa only [ZMod.natCast_zmod_val] using psiResidue_natCast_eq_psiAP k q r.val

/-- Still an unproved analytic input, now expressed on the literal congruence carrier. -/
def ScaleAPEstimate (D k₀ : ℕ) (C c : ℝ) : Prop :=
  ∀ k ≥ k₀, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ (Real.log (k : ℝ))^D →
    ∀ a : ℕ, Nat.Coprime a q →
      |psiAP k q a-(k : ℝ)/(Nat.totient q : ℝ)| ≤ prefixEnvelope k C c

theorem scale_estimate_iff_AP (D k₀ : ℕ) (C c : ℝ) :
    ScaleReducedClassEstimate D k₀ C c ↔ ScaleAPEstimate D k₀ C c := by
  constructor
  · intro h k hk q hq hqlog a ha
    let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
    have hr : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime _ _).mpr ha
    simpa only [psiResidue_natCast_eq_psiAP] using h k hk q hq hqlog (a : ZMod q) hr
  · intro h k hk q hq hqlog r hr
    let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
    have hu : IsUnit (r.val : ZMod q) := by simpa only [ZMod.natCast_zmod_val] using hr
    have ha : Nat.Coprime r.val q := (ZMod.isUnit_iff_coprime _ _).mp hu
    simpa only [psiResidue_eq_psiAP] using h k hk q hq hqlog r.val ha

theorem uniform_major_reserve_of_AP_estimate (K k₀ : ℕ) (hK : 0 < K) (C c : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c) (hAP : ScaleAPEstimate (K+1) k₀ C c) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ N : ℕ, 4 ≤ N → N ≤ M → Even N → M ≤ 2*N →
      (M : ℝ)/14 ≤ GoldbachCircleMethodTwoScaleIntegralPartitionV1831.twoScaleMajorIntegralReal
        M (logWidth K M) (logRadius K M) N :=
  uniform_major_reserve_of_scale_estimate K k₀ hK C c hC hc
    ((scale_estimate_iff_AP (K+1) k₀ C c).mpr hAP)

end GoldbachCircleMethodArithmeticProgressionInputMatchV1871
