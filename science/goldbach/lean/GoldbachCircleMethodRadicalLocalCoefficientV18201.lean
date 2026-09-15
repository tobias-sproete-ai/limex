import GoldbachCircleMethodActualCoupledCutoffAdapterV18199
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Zeta

set_option autoImplicit false
open scoped BigOperators Classical

namespace GoldbachCircleMethodRadicalLocalCoefficientV18201

open GoldbachCircleMethodActualCoupledCutoffAdapterV18199
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open UniqueFactorizationMonoid

@[simp] theorem coefficient_one (N : ℕ) :
    squarefreeCompanionCoefficient 1 N = 1 := by
  simp [squarefreeCompanionCoefficient]

theorem coefficient_prime {p N : ℕ} (hp : p.Prime) :
    squarefreeCompanionCoefficient p N =
      if p ∣ N then -1 else (1 : ℂ) / (p - 1 : ℕ) := by
  by_cases h : p ∣ N
  · simp [squarefreeCompanionCoefficient, h, Nat.gcd_eq_left h,
      ArithmeticFunction.moebius_apply_prime hp, Nat.div_self hp.pos]
  · have hc := hp.coprime_iff_not_dvd.mpr h
    simp [squarefreeCompanionCoefficient, h, hc.gcd_eq_one, Nat.totient_prime hp]

/-- The actual coefficient on its squarefree support, zero elsewhere. -/
noncomputable def supportedCoefficient (N : ℕ) : ArithmeticFunction ℂ where
  toFun q := if Squarefree q then squarefreeCompanionCoefficient q N else 0
  map_zero' := by simp

@[simp] theorem supportedCoefficient_of_squarefree {q N : ℕ} (hq : Squarefree q) :
    supportedCoefficient N q = squarefreeCompanionCoefficient q N := by
  simp [supportedCoefficient, hq]

theorem supportedCoefficient_multiplicative (N : ℕ) :
    (supportedCoefficient N).IsMultiplicative := by
  constructor
  · simp [supportedCoefficient]
  · intro a b hab
    by_cases ha : Squarefree a
    · by_cases hb : Squarefree b
      · simp only [supportedCoefficient, ArithmeticFunction.coe_mk, if_pos ha,
          if_pos hb, if_pos ((Nat.squarefree_mul hab).mpr ⟨ha, hb⟩)]
        exact squarefreeCompanionCoefficient_mul ha hb hab
      · have hn : ¬ Squarefree (a * b) := fun h => hb h.of_mul_right
        simp [supportedCoefficient, hb, hn]
    · have hn : ¬ Squarefree (a * b) := fun h => ha h.of_mul_left
      simp [supportedCoefficient, ha, hn]

/-- The actual local carrier contains all divisors of the radical, with no
lost natural cutoff points. The positive-modulus assumption is essential. -/
theorem localCarrier_eq_radical_divisors {r : ℕ} (hr : 0 < r) :
    dividingSquarefreePrefix (radical r) r = (radical r).divisors := by
  ext d
  simp only [dividingSquarefreePrefix, Finset.mem_filter, mem_fullSquarefreePrefix,
    Nat.mem_divisors]
  constructor
  · rintro ⟨⟨_, _⟩, hd⟩
    exact ⟨hd, radical_ne_zero⟩
  · rintro ⟨hd, _⟩
    exact ⟨⟨Nat.le_of_dvd hr (dvd_trans hd radical_dvd_self),
      squarefree_radical.squarefree_of_dvd hd⟩, hd⟩

/-- A finite Euler product for the literal V199 local divisor coefficient. -/
theorem radicalLocalCoefficient_eq_primeProduct {r : ℕ} (hr : 0 < r) (N : ℕ) :
    radicalLocalCoefficient r N =
      ∏ p ∈ r.primeFactors, (1 + squarefreeCompanionCoefficient p N) := by
  have hz : (ArithmeticFunction.zeta : ArithmeticFunction ℂ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast
  have hp := (supportedCoefficient_multiplicative N).prodPrimeFactors_add_of_squarefree
    hz (n := radical r) squarefree_radical
  rw [ArithmeticFunction.prodPrimeFactors_apply radical_ne_zero,
    ArithmeticFunction.coe_mul_zeta_apply] at hp
  calc
    radicalLocalCoefficient r N =
        ∑ d ∈ (radical r).divisors, supportedCoefficient N d := by
      unfold radicalLocalCoefficient
      rw [localCarrier_eq_radical_divisors hr]
      apply Finset.sum_congr rfl
      intro d hd
      exact (supportedCoefficient_of_squarefree
        (squarefree_radical.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))).symm
    _ = ∏ p ∈ (radical r).primeFactors,
        (supportedCoefficient N + (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) p := hp.symm
    _ = _ := by
      rw [Nat.primeFactors_radical]
      apply Finset.prod_congr rfl
      intro p hp
      have hprime := Nat.prime_of_mem_primeFactors hp
      simp [ArithmeticFunction.add_apply, hprime.squarefree, hprime.ne_zero,
        ArithmeticFunction.zeta_apply, add_comm]

theorem local_prime_factor {p N : ℕ} (hp : p.Prime) :
    (1 : ℂ) + squarefreeCompanionCoefficient p N =
      if p ∣ N then 0 else (p : ℂ) / (p - 1 : ℕ) := by
  rw [coefficient_prime hp]
  by_cases h : p ∣ N
  · simp [h]
  · simp only [if_neg h]
    have hden : ((p - 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.sub_pos_of_lt hp.one_lt).ne'
    apply (eq_div_iff hden).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hden, Nat.cast_sub hp.one_le]
    ring

/-- The finite prime-ratio product has the exact totient normalization. -/
theorem primeRatioProduct_eq_totientRatio {r : ℕ} (hr : 0 < r) :
    (∏ p ∈ r.primeFactors, (p : ℂ) / (p - 1 : ℕ)) =
      (r : ℂ) / (r.totient : ℂ) := by
  have hd : (∏ p ∈ r.primeFactors, ((p - 1 : ℕ) : ℂ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact_mod_cast (Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt).ne'
  have hphi : (r.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hr).ne'
  have hi : (r.totient : ℂ) * (∏ p ∈ r.primeFactors, (p : ℂ)) =
      (r : ℂ) * (∏ p ∈ r.primeFactors, ((p - 1 : ℕ) : ℂ)) := by
    simpa only [Nat.cast_mul, Nat.cast_prod] using
      congrArg (fun n : ℕ => (n : ℂ)) (Nat.totient_mul_prod_primeFactors r)
  rw [Finset.prod_div_distrib]
  apply (div_eq_div_iff hd hphi).mpr
  simpa only [mul_comm] using hi

/-- Closed form of the actual local coefficient, with the zero-modulus case
excluded rather than hidden in a quotient convention. -/
theorem radicalLocalCoefficient_eq_ite {r : ℕ} (hr : 0 < r) (N : ℕ) :
    radicalLocalCoefficient r N =
      if Nat.Coprime N r then (r : ℂ) / (r.totient : ℂ) else 0 := by
  rw [radicalLocalCoefficient_eq_primeProduct hr]
  by_cases h : Nat.Coprime N r
  · rw [if_pos h]
    calc
      _ = ∏ p ∈ r.primeFactors, (p : ℂ) / (p - 1 : ℕ) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        have hnot : ¬ p ∣ N :=
          hprime.coprime_iff_not_dvd.mp
            (h.of_dvd_right (Nat.dvd_of_mem_primeFactors hp)).symm
        rw [local_prime_factor hprime, if_neg hnot]
      _ = _ := primeRatioProduct_eq_totientRatio hr
  · rw [if_neg h]
    obtain ⟨p, hp, hpN, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    apply Finset.prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp, hpr, hr.ne'⟩)
    rw [local_prime_factor hp, if_pos hpN]

/-- The local coefficient is the existing V108 unit indicator, not a newly
invented support predicate. -/
theorem radicalLocalCoefficient_eq_unitIndicator {r : ℕ} [NeZero r] (hr : 0 < r) (N : ℕ) :
    radicalLocalCoefficient r N =
      ((r : ℂ) / (r.totient : ℂ)) *
        GoldbachCircleMethodSmallConductorPairReserveV18108.unitIndicator r (N : ZMod r) := by
  rw [radicalLocalCoefficient_eq_ite hr]
  unfold GoldbachCircleMethodSmallConductorPairReserveV18108.unitIndicator
  simp only [ZMod.isUnit_iff_coprime]
  split_ifs <;> simp

/-- V199's exact actual-operator identity with the local factor evaluated.
The two independently defined cutoff corrections remain present. -/
theorem principalFiniteCompanion_eq_unitFactor_add_deltas
    {Q : ℕ} (hQ : 1 ≤ Q)
    (r : GoldbachCircleMethodBoundedConductorReindexV18117.PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ) :
    GoldbachCircleMethodFiniteCompanionBindingV18118.finiteCompanion
        (GoldbachCircleMethodPrincipalWindowBoundaryV18121.oneLevel hQ) N w =
      (((r.val : ℂ) / (r.val.totient : ℂ)) *
        GoldbachCircleMethodSmallConductorPairReserveV18108.unitIndicator r.val
          (N : ZMod r.val)) *
        GoldbachCircleMethodFiniteCompanionBindingV18118.finiteCompanion r N w +
      coupledWeightChange Q r.val N w + coupledUpperShell Q r.val N w := by
  rw [principalFiniteCompanion_eq_local_mul_add_deltas hQ r,
    radicalLocalCoefficient_eq_unitIndicator (Nat.pos_of_ne_zero (NeZero.ne r.val)) N]

end GoldbachCircleMethodRadicalLocalCoefficientV18201
