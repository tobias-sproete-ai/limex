import GoldbachCircleMethodActualUnitPairPrimePowerV18197
import GoldbachCircleMethodCompanionSquarefreeGcdBindingV18139
import Mathlib.RingTheory.Radical.NatInt

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualCoupledCutoffAdapterV18199

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodCompanionSquarefreeGcdBindingV18139
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodRamanujanCharacterProductV1843
open GoldbachCircleMethodGeneralCoprimeCharacterV1868

/-- The genuine squarefree companion coefficient, written in the already
verified gcd form so it is total even at modulus zero. -/
noncomputable def squarefreeCompanionCoefficient (q N : ℕ) : ℂ :=
  (((ArithmeticFunction.moebius (Nat.gcd q N) : ℤ) : ℂ) /
    ((q / Nat.gcd q N).totient : ℂ))

/-- On a positive squarefree modulus, the total gcd form is the literal
Ramanujan/Moebius/totient coefficient used by `finiteCompanion`. -/
theorem squarefreeCompanionCoefficient_eq_actual (q N : ℕ) [NeZero q]
    (hq : Squarefree q) :
    squarefreeCompanionCoefficient q N =
      ((ArithmeticFunction.moebius q : ℤ) : ℂ) *
        unitCharacterSum q (N : ZMod q) / (q.totient : ℂ) := by
  exact (moebius_character_quotient_gcd q N hq).symm

/-- The genuine companion coefficient is multiplicative on coprime positive
squarefree factors.  This uses the actual Ramanujan sum, Moebius function and
totient, rather than a formal replacement coefficient. -/
theorem squarefreeCompanionCoefficient_mul {a b N : ℕ}
    (ha : Squarefree a) (hb : Squarefree b) (hab : Nat.Coprime a b) :
    squarefreeCompanionCoefficient (a * b) N =
      squarefreeCompanionCoefficient a N * squarefreeCompanionCoefficient b N := by
  let _ : NeZero a := ⟨ha.ne_zero⟩
  let _ : NeZero b := ⟨hb.ne_zero⟩
  let _ : NeZero (a * b) := ⟨Nat.mul_ne_zero ha.ne_zero hb.ne_zero⟩
  have hsum : unitCharacterSum (a * b) (N : ZMod (a * b)) =
      unitCharacterSum a (N : ZMod a) * unitCharacterSum b (N : ZMod b) := by
    calc
      _ = finiteFourierRamanujan (a * b) N
          (Nat.mul_ne_zero ha.ne_zero hb.ne_zero) :=
        (finiteFourierRamanujan_eq_unitCharacterSum (a * b) N
          (Nat.mul_ne_zero ha.ne_zero hb.ne_zero)).symm
      _ = finiteFourierRamanujan a N ha.ne_zero *
          finiteFourierRamanujan b N hb.ne_zero :=
        finiteFourierRamanujan_mul_of_coprime ha.ne_zero hb.ne_zero hab N
      _ = _ := by
        rw [finiteFourierRamanujan_eq_unitCharacterSum a N ha.ne_zero,
          finiteFourierRamanujan_eq_unitCharacterSum b N hb.ne_zero]
  rw [squarefreeCompanionCoefficient_eq_actual (a * b) N
      ((Nat.squarefree_mul hab).mpr ⟨ha, hb⟩),
    squarefreeCompanionCoefficient_eq_actual a N ha,
    squarefreeCompanionCoefficient_eq_actual b N hb,
    hsum,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab,
    Nat.totient_mul hab]
  push_cast
  ring

/-- The actual conductor-one finite companion on its exact squarefree prefix.
No rectangular cutoff or replacement weight is introduced. -/
theorem principalFiniteCompanion_eq_squarefreePrefix {Q : ℕ} (hQ : 1 ≤ Q)
    (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion (oneLevel hQ) N w =
      ∑ q ∈ fullSquarefreePrefix Q,
        squarefreeCompanionCoefficient q N * w q := by
  rw [finite_companion_squarefree_sum]
  simp only [oneLevel, Nat.div_one, one_mul]
  apply Finset.sum_congr rfl
  intro q hq
  have hsq := (mem_fullSquarefreePrefix.mp hq).2
  simp [squarefreeCompanionCoefficient]

/-- Exact whole finite reindex `q=d*l` on the existing coupled carrier.
The common part divides `radical r`; the complementary part remains coprime
to that radical; and the original coupled cutoff and weight are unchanged. -/
theorem principalFiniteCompanion_radical_split {Q : ℕ} (hQ : 1 ≤ Q)
    (r N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion (oneLevel hQ) N w =
      ∑ t ∈ coupledSquarefreePairs (UniqueFactorizationMonoid.radical r) Q,
        squarefreeCompanionCoefficient (t.1 * t.2) N * w (t.1 * t.2) := by
  rw [principalFiniteCompanion_eq_squarefreePrefix hQ]
  exact fullSquarefreePrefix_sum_split (UniqueFactorizationMonoid.radical r) Q
    (fun q => squarefreeCompanionCoefficient q N * w q)

/-- The same exact reindex with the genuine coprime coefficient product
exposed term by term.  The coupled inequality `d*l ≤ Q` remains in the
existing carrier. -/
theorem principalFiniteCompanion_radical_split_mul {Q : ℕ} (hQ : 1 ≤ Q)
    (r N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion (oneLevel hQ) N w =
      ∑ t ∈ coupledSquarefreePairs (UniqueFactorizationMonoid.radical r) Q,
        squarefreeCompanionCoefficient t.1 N *
          squarefreeCompanionCoefficient t.2 N * w (t.1 * t.2) := by
  rw [principalFiniteCompanion_radical_split hQ]
  apply Finset.sum_congr rfl
  intro t ht
  have ha := (mem_coupledSquarefreePairs.mp ht).1
  have hb := (mem_coupledSquarefreePairs.mp ht).2.1
  rw [squarefreeCompanionCoefficient_mul ha hb (pair_factors_coprime ht)]

/-- Coprimality against the radical is exactly coprimality against the
original positive modulus. -/
theorem coprime_radical_iff {a r : ℕ} (hr : r ≠ 0) :
    Nat.Coprime a (UniqueFactorizationMonoid.radical r) ↔ Nat.Coprime a r := by
  constructor
  · intro h
    apply Nat.coprime_of_dvd
    intro p hp hpa hpr
    have hpMem : p ∈ r.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpr, hr⟩
    have hpRad : p ∣ UniqueFactorizationMonoid.radical r := by
      rw [Nat.radical_eq_prod_primeFactors]
      exact Finset.dvd_prod_of_mem (fun x => x) hpMem
    exact (hp.coprime_iff_not_dvd.mp (h.of_dvd_left hpa)) hpRad
  · intro h
    exact h.of_dvd_right UniqueFactorizationMonoid.radical_dvd_self

/-- Readable membership contract for the reused V46 carrier: the second
factor is genuinely coprime to `r`, not merely to a new surrogate modulus. -/
theorem mem_radical_coupledSquarefreePairs_iff {d l r Q : ℕ} (hr : r ≠ 0) :
    (d, l) ∈ coupledSquarefreePairs (UniqueFactorizationMonoid.radical r) Q ↔
      Squarefree d ∧ Squarefree l ∧
        d ∣ UniqueFactorizationMonoid.radical r ∧ Nat.Coprime l r ∧ d * l ≤ Q := by
  rw [mem_coupledSquarefreePairs]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr (coprime_radical_iff hr) Iff.rfl

/-- The common-range slice of the existing coupled carrier. -/
noncomputable def commonRadicalPairs (Q r : ℕ) : Finset (ℕ × ℕ) :=
  (coupledSquarefreePairs (UniqueFactorizationMonoid.radical r) Q).filter
    (fun t => t.2 ≤ Q / r)

/-- The literal finite local coefficient sum over divisors of `radical r`.
No closed Euler-product value is asserted here. -/
noncomputable def radicalLocalCoefficient (r N : ℕ) : ℂ :=
  ∑ d ∈ dividingSquarefreePrefix (UniqueFactorizationMonoid.radical r) r,
    squarefreeCompanionCoefficient d N

/-- For `1 ≤ r ≤ Q`, the common-range slice is exactly the product of the
existing squarefree divisor carrier with the genuine coprime companion
carrier.  Odd cutoffs and natural division are retained. -/
theorem commonRadicalPairs_eq_product {Q r : ℕ} (hr : 1 ≤ r) (_hrQ : r ≤ Q) :
    commonRadicalPairs Q r =
      dividingSquarefreePrefix (UniqueFactorizationMonoid.radical r) r ×ˢ
        (fullSquarefreePrefix (Q / r)).filter (fun l => Nat.Coprime r l) := by
  ext t
  constructor
  · intro ht
    obtain ⟨htPair, htl⟩ := Finset.mem_filter.mp ht
    obtain ⟨hd, hl, hdRad, hlRad, hdl⟩ :=
      mem_coupledSquarefreePairs.mp htPair
    have hr0 : r ≠ 0 := Nat.ne_of_gt hr
    have hdle : t.1 ≤ r :=
      (Nat.le_of_dvd (Nat.radical_pos r) hdRad).trans
        (Nat.radical_le_self_iff.mpr hr0)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr
        ⟨mem_fullSquarefreePrefix.mpr ⟨hdle, hd⟩, hdRad⟩,
       Finset.mem_filter.mpr
        ⟨mem_fullSquarefreePrefix.mpr ⟨htl, hl⟩,
          ((coprime_radical_iff hr0).mp hlRad).symm⟩⟩
  · intro ht
    obtain ⟨htd, htl⟩ := Finset.mem_product.mp ht
    obtain ⟨hdFull, hdRad⟩ := Finset.mem_filter.mp htd
    obtain ⟨hlFull, hlCop⟩ := Finset.mem_filter.mp htl
    obtain ⟨hdle, hd⟩ := mem_fullSquarefreePrefix.mp hdFull
    obtain ⟨hlle, hl⟩ := mem_fullSquarefreePrefix.mp hlFull
    have hr0 : r ≠ 0 := Nat.ne_of_gt hr
    have hprod : t.1 * t.2 ≤ Q := by
      calc
        t.1 * t.2 ≤ r * (Q / r) := Nat.mul_le_mul hdle hlle
        _ ≤ Q := Nat.mul_div_le Q r
    apply Finset.mem_filter.mpr
    exact ⟨mem_coupledSquarefreePairs.mpr
      ⟨hd, hl, hdRad, (coprime_radical_iff hr0).mpr hlCop.symm, hprod⟩,
      hlle⟩

/-- The common rectangular portion of the exact coupled carrier.  It retains
the original coefficient factors and changes only the displayed weight from
`w (d*l)` to `w (r*l)` on the genuine common range `l ≤ Q/r`. -/
noncomputable def coupledRectangularCore (Q r N : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ t ∈ coupledSquarefreePairs (UniqueFactorizationMonoid.radical r) Q,
    if t.2 ≤ Q / r then
      squarefreeCompanionCoefficient t.1 N *
        squarefreeCompanionCoefficient t.2 N * w (r * t.2)
    else 0

/-- First explicit cutoff remainder: the changed weight on the common range. -/
noncomputable def coupledWeightChange (Q r N : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ t ∈ coupledSquarefreePairs (UniqueFactorizationMonoid.radical r) Q,
    if t.2 ≤ Q / r then
      squarefreeCompanionCoefficient t.1 N *
        squarefreeCompanionCoefficient t.2 N *
          (w (t.1 * t.2) - w (r * t.2))
    else 0

/-- Second explicit cutoff remainder: the actual upper shell left by the
coupled inequalities `d*l ≤ Q` and `Q/r < l`. -/
noncomputable def coupledUpperShell (Q r N : ℕ) (w : ℕ → ℂ) : ℂ :=
  ∑ t ∈ coupledSquarefreePairs (UniqueFactorizationMonoid.radical r) Q,
    if Q / r < t.2 then
      squarefreeCompanionCoefficient t.1 N *
        squarefreeCompanionCoefficient t.2 N * w (t.1 * t.2)
    else 0

/-- Kernel-checked exact two-piece Delta split on the existing coupled
carrier.  This theorem deliberately stops before identifying the rectangular
core with a local factor times the literal conductor-`r` companion. -/
theorem principalFiniteCompanion_eq_rectangular_add_deltas {Q : ℕ}
    (hQ : 1 ≤ Q) (r N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion (oneLevel hQ) N w =
      coupledRectangularCore Q r N w + coupledWeightChange Q r N w +
        coupledUpperShell Q r N w := by
  rw [principalFiniteCompanion_radical_split_mul hQ]
  unfold coupledRectangularCore coupledWeightChange coupledUpperShell
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hcommon : t.2 ≤ Q / r
  · have hshell : ¬Q / r < t.2 := Nat.not_lt.mpr hcommon
    simp only [hcommon, hshell, if_true, if_false, add_zero]
    ring
  · have hshell : Q / r < t.2 := Nat.lt_of_not_ge hcommon
    simp only [hcommon, hshell, if_true, if_false, zero_add]

/-- The rectangular core is exactly the finite local coefficient times the
literal conductor-`r` companion.  This is the finite `T_r * L_(r,Q)` bridge;
it still makes no claim about a closed value for `T_r`. -/
theorem coupledRectangularCore_eq_local_mul_finiteCompanion {Q : ℕ}
    (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) :
    coupledRectangularCore Q r.val N w =
      radicalLocalCoefficient r.val N * finiteCompanion r N w := by
  have hr : 1 ≤ r.val := (Finset.mem_Icc.mp r.property).1
  have hrQ : r.val ≤ Q := (Finset.mem_Icc.mp r.property).2
  rw [finite_companion_squarefree_sum]
  change coupledRectangularCore Q r.val N w =
    radicalLocalCoefficient r.val N *
      ∑ l ∈ fullSquarefreePrefix (Q / r.val),
        if Nat.Coprime r.val l then
          squarefreeCompanionCoefficient l N * w (r.val * l) else 0
  rw [← Finset.sum_filter]
  unfold coupledRectangularCore radicalLocalCoefficient
  rw [← Finset.sum_filter]
  change (∑ t ∈ commonRadicalPairs Q r.val,
      squarefreeCompanionCoefficient t.1 N *
        squarefreeCompanionCoefficient t.2 N * w (r.val * t.2)) = _
  rw [commonRadicalPairs_eq_product hr hrQ,
    Finset.sum_product, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Full exact finite decomposition of the actual principal companion:
`A_Q = T_r * L_(r,Q) + Delta_change + Delta_shell`.  Both Delta terms are
defined independently above on the reused coupled carrier. -/
theorem principalFiniteCompanion_eq_local_mul_add_deltas {Q : ℕ}
    (hQ : 1 ≤ Q) (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion (oneLevel hQ) N w =
      radicalLocalCoefficient r.val N * finiteCompanion r N w +
        coupledWeightChange Q r.val N w + coupledUpperShell Q r.val N w := by
  rw [principalFiniteCompanion_eq_rectangular_add_deltas hQ r.val N w,
    coupledRectangularCore_eq_local_mul_finiteCompanion]

end GoldbachCircleMethodActualCoupledCutoffAdapterV18199
