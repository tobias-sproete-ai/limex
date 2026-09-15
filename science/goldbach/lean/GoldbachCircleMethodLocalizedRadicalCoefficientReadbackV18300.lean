import GoldbachCircleMethodLocalizedSquarefreeDivisorBindingV18299

/-!
# Goldbach V1.8.300: localized radical-coefficient readback

At constant weight one, the exact localized squarefree-divisor sum is
identified with the already verified radical local coefficient.  This exposes
the sharp dichotomy: active-conductor coprimality gives `r / φ(r)`, while a
shared prime factor makes the localized coefficient zero.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodLocalizedRadicalCoefficientReadbackV18300

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodActualCoupledCutoffAdapterV18199
open GoldbachCircleMethodRadicalLocalCoefficientV18201
open GoldbachCircleMethodLocalizedSquarefreeDivisorBindingV18299
open UniqueFactorizationMonoid

/-- The positive-level squarefree divisors of the active conductor are
exactly the divisors of its radical. -/
theorem localizedSquarefreeCarrier_eq_radicalDivisors
    {Q : ℕ} (active : PositiveLevel Q) :
    (Finset.Icc 1 Q).filter
        (fun l => Squarefree l ∧ l ∣ active.val) =
      (radical active.val).divisors := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hl1, _hlQ⟩, hsq, hdiv⟩
    have hrad : l ∣ radical active.val :=
      (dvd_radical_iff hsq.isRadical (NeZero.ne active.val)).2 hdiv
    exact ⟨hrad, radical_ne_zero⟩
  · rintro ⟨hrad, _hr0⟩
    have hsq : Squarefree l := squarefree_radical.squarefree_of_dvd hrad
    have hdiv : l ∣ active.val := dvd_trans hrad radical_dvd_self
    have hlpos : 0 < l := hsq.ne_zero.bot_lt
    have hlactive : l ≤ active.val :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne active.val)) hdiv
    exact ⟨⟨hlpos, hlactive.trans (Finset.mem_Icc.mp active.property).2⟩,
      hsq, hdiv⟩

/-- Constant-weight localized squarefree-divisor sum equals the existing
radical local coefficient exactly. -/
theorem localizedSquarefreeDivisorSum_one_eq_radicalLocalCoefficient
    {Q : ℕ} (active : PositiveLevel Q) (N : ℕ) :
    localizedSquarefreeDivisorSum active N (fun _ => 1) =
      radicalLocalCoefficient active.val N := by
  unfold localizedSquarefreeDivisorSum radicalLocalCoefficient
  rw [← Finset.sum_subtype (Finset.Icc 1 Q) (by intro l; rfl)
    (fun l => if Squarefree l ∧ l ∣ active.val then
      squarefreeCompanionCoefficient l N * 1 else 0)]
  simp only [mul_one]
  rw [← Finset.sum_filter]
  rw [localizedSquarefreeCarrier_eq_radicalDivisors active]
  rw [localCarrier_eq_radical_divisors
    (Nat.pos_of_ne_zero (NeZero.ne active.val))]

/-- Closed-form dichotomy for the localized constant-weight principal
channel. -/
theorem localizedSquarefreeDivisorSum_one_eq_ite
    {Q : ℕ} (active : PositiveLevel Q) (N : ℕ) :
    localizedSquarefreeDivisorSum active N (fun _ => 1) =
      if Nat.Coprime N active.val then
        (active.val : ℂ) / (active.val.totient : ℂ)
      else 0 := by
  rw [localizedSquarefreeDivisorSum_one_eq_radicalLocalCoefficient active N]
  exact radicalLocalCoefficient_eq_ite
    (Nat.pos_of_ne_zero (NeZero.ne active.val)) N

/-- A shared prime factor forces exact cancellation of the localized
constant-weight principal channel. -/
theorem localizedSquarefreeDivisorSum_one_eq_zero_of_not_coprime
    {Q : ℕ} (active : PositiveLevel Q) (N : ℕ)
    (hN : ¬ Nat.Coprime N active.val) :
    localizedSquarefreeDivisorSum active N (fun _ => 1) = 0 := by
  rw [localizedSquarefreeDivisorSum_one_eq_ite active N, if_neg hN]

end GoldbachCircleMethodLocalizedRadicalCoefficientReadbackV18300

