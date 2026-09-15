import GoldbachCircleMethodActualInputModelResidualV18138
import GoldbachCircleMethodFullSquarefreeCoefficientV1847
import GoldbachCircleMethodGeneralCoprimeCharacterV1868

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodFullSquarefreeCoefficientV1847
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118

namespace GoldbachCircleMethodCompanionSquarefreeGcdBindingV18139

/-- The actual character quotient on the exact squarefree coupled carrier.
Squarefreeness constrains the modulus a*b, not the evaluation point N. -/
theorem pair_moebius_character_quotient {a b N H : ℕ}
    (h : (a,b) ∈ coupledSquarefreePairs N H) :
    ((ArithmeticFunction.moebius (a*b) : ℤ) : ℂ) *
      finiteFourierRamanujan (a*b) N
        (mem_fullSquarefreePrefix.mp (pair_product_mem h)).2.ne_zero /
          ((a*b).totient : ℂ) =
      ((ArithmeticFunction.moebius a : ℤ) : ℂ) / (b.totient : ℂ) := by
  have ha := (mem_coupledSquarefreePairs.mp h).1
  have hb := (mem_coupledSquarefreePairs.mp h).2.1
  have hpa : (a.totient : ℂ)≠0 := by
    exact_mod_cast (Nat.totient_pos.mpr ha.ne_zero.bot_lt).ne'
  have hpb : (b.totient : ℂ)≠0 := by
    exact_mod_cast (Nat.totient_pos.mpr hb.ne_zero.bot_lt).ne'
  have hmu : (((ArithmeticFunction.moebius b : ℤ) : ℂ))^2=1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hb
  rw [finiteFourierRamanujan_pair_eq_totient_mul_moebius (R:=H) h le_rfl,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (pair_factors_coprime h),
    Nat.totient_mul (pair_factors_coprime h)]
  push_cast
  calc
    _ = ((ArithmeticFunction.moebius a : ℤ) : ℂ) *
        (((ArithmeticFunction.moebius b : ℤ) : ℂ))^2 / (b.totient : ℂ) := by
      field_simp
    _ = _ := by rw [hmu,mul_one]

/-- Canonical gcd specialization, using the already checked bijection V46. -/
theorem moebius_character_quotient_gcd (q N : ℕ) [NeZero q] (hq : Squarefree q) :
    ((ArithmeticFunction.moebius q : ℤ) : ℂ) *
        unitCharacterSum q (N : ZMod q) / (q.totient : ℂ) =
      ((ArithmeticFunction.moebius (Nat.gcd q N) : ℤ) : ℂ) /
        ((q/Nat.gcd q N).totient : ℂ) := by
  have hp := canonical_pair_mem (N:=N)
    (mem_fullSquarefreePrefix.mpr ⟨le_rfl,hq⟩ : q ∈ fullSquarefreePrefix q)
  have he := pair_moebius_character_quotient hp
  simpa only [canonical_product,finiteFourierRamanujan_eq_unitCharacterSum] using he

/-- Non-squarefree moduli vanish solely because their Moebius coefficient
vanishes; nothing is asserted about squarefreeness of N. -/
theorem moebius_character_quotient_piecewise (q N : ℕ) [NeZero q] :
    ((ArithmeticFunction.moebius q : ℤ) : ℂ) *
        unitCharacterSum q (N : ZMod q) / (q.totient : ℂ) =
      if Squarefree q then
        ((ArithmeticFunction.moebius (Nat.gcd q N) : ℤ) : ℂ) /
          ((q/Nat.gcd q N).totient : ℂ)
      else 0 := by
  by_cases hq : Squarefree q
  · simpa only [hq,if_true] using moebius_character_quotient_gcd q N hq
  · simp only [hq,if_false,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq,
      Int.cast_zero,zero_mul,zero_div]

/-- The unchanged finite companion is now bound to its exact gcd coefficients.
The product cutoff and conductor coprimality remain explicit, with the
weight still evaluated at r*l, never at l alone. -/
theorem finite_companion_gcd_coefficients {Q : ℕ} (r : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r N w =
      ∑ l : PositiveLevel Q,
        if r.val*l.val≤Q ∧ Nat.Coprime r.val l.val ∧ Squarefree l.val then
          (((ArithmeticFunction.moebius (Nat.gcd l.val N) : ℤ) : ℂ) /
            ((l.val/Nat.gcd l.val N).totient : ℂ)) * w (r.val*l.val)
        else 0 := by
  unfold finiteCompanion
  apply Finset.sum_congr rfl
  intro l _
  by_cases hc : r.val*l.val≤Q
  · by_cases hcop : Nat.Coprime r.val l.val
    · rw [if_pos ⟨hc,hcop⟩]
      by_cases hs : Squarefree l.val
      · rw [if_pos ⟨hc,hcop,hs⟩,moebius_character_quotient_gcd l.val N hs]
      · rw [if_neg (by tauto : ¬(r.val*l.val≤Q ∧ Nat.Coprime r.val l.val ∧ Squarefree l.val))]
        simp only [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs,
          Int.cast_zero,zero_mul,zero_div]
    · simp [hcop]
  · simp [hc]


/-- Exact natural squarefree carrier; Q/r is not replaced by Q and the
input N is unrestricted, including non-squarefree values. -/
theorem finite_companion_squarefree_sum {Q : ℕ} (r : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r N w =
      ∑ l ∈ fullSquarefreePrefix (Q/r.val),
        if Nat.Coprime r.val l then
          (((ArithmeticFunction.moebius (Nat.gcd l N) : ℤ) : ℂ) /
            ((l/Nat.gcd l N).totient : ℂ)) * w (r.val*l)
        else 0 := by
  let f : ℕ → ℂ := fun l =>
    (((ArithmeticFunction.moebius (Nat.gcd l N) : ℤ) : ℂ) /
      ((l/Nat.gcd l N).totient : ℂ)) * w (r.val*l)
  have hr : 0<r.val := Nat.pos_of_ne_zero (NeZero.ne r.val)
  have hs : (Finset.Icc 1 Q).filter
      (fun l => r.val*l≤Q ∧ Nat.Coprime r.val l ∧ Squarefree l) =
      (fullSquarefreePrefix (Q/r.val)).filter (fun l => Nat.Coprime r.val l) := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_Icc,mem_fullSquarefreePrefix]
    constructor
    · rintro ⟨⟨_,_⟩,hl,hcop,hsq⟩
      exact ⟨⟨(Nat.le_div_iff_mul_le hr).mpr (by simpa [Nat.mul_comm] using hl),hsq⟩,hcop⟩
    · rintro ⟨⟨hl,hsq⟩,hcop⟩
      have hrl : r.val*l≤Q := by
        simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hr).mp hl
      exact ⟨⟨hsq.ne_zero.bot_lt,hl.trans (Nat.div_le_self Q r.val)⟩,hrl,hcop,hsq⟩
  rw [finite_companion_gcd_coefficients]
  change (∑ l : PositiveLevel Q,
      if r.val*l.val≤Q ∧ Nat.Coprime r.val l.val ∧ Squarefree l.val then f l.val else 0) =
    ∑ l ∈ fullSquarefreePrefix (Q/r.val), if Nat.Coprime r.val l then f l else 0
  rw [←Finset.sum_subtype (Finset.Icc 1 Q) (by intro l; rfl)
    (fun l => if r.val*l≤Q ∧ Nat.Coprime r.val l ∧ Squarefree l then f l else 0)]
  rw [←Finset.sum_filter,hs,Finset.sum_filter]

/-- Entire actual finite companion on the coupled gcd fiber a*b<=Q/r.
Conductor exclusions, squarefreeness and the weight at r*a*b are preserved. -/
theorem finite_companion_coupled_gcd_sum {Q : ℕ} (r : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r N w =
      ∑ t ∈ coupledSquarefreePairs N (Q/r.val),
        if Nat.Coprime r.val t.1 ∧ Nat.Coprime r.val t.2 then
          (((ArithmeticFunction.moebius t.1 : ℤ) : ℂ) / (t.2.totient : ℂ)) *
            w (r.val*(t.1*t.2))
        else 0 := by
  rw [finite_companion_squarefree_sum,fullSquarefreePrefix_sum_split N (Q/r.val)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [pair_div_recovery ht,pair_gcd_recovery ht]
  simp only [Nat.coprime_mul_iff_right]


/-- Finite divisor identity on squarefree moduli, entirely in integers. -/
theorem squarefree_moebius_divisor_sum (n : ℕ) (hn : Squarefree n) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d*(d : ℤ)) =
      ArithmeticFunction.moebius n*(n.totient : ℤ) := by
  have hphi : n.totient=∏ p ∈ n.primeFactors, (p-1) := by
    rw [Nat.totient_eq_div_primeFactors_mul,Nat.prod_primeFactors_of_squarefree hn,
      Nat.div_self hn.ne_zero.bot_lt,one_mul]
  have hid := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    (ArithmeticFunction.id : ArithmeticFunction ℤ)
    ArithmeticFunction.isMultiplicative_id.natCast hn
  have hsum : (∏ p ∈ n.primeFactors, (1-(p : ℤ))) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius d*(d : ℤ) := by
    simpa only [ArithmeticFunction.natCoe_apply,ArithmeticFunction.intCoe_apply,
      ArithmeticFunction.id_apply,Int.cast_id] using hid
  rw [←hsum]
  calc
    _ = ∏ p ∈ n.primeFactors, ArithmeticFunction.moebius p*((p-1 : ℕ) : ℤ) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      rw [ArithmeticFunction.moebius_apply_prime hpp,Nat.cast_sub hpp.one_le]
      ring
    _ = (∏ p ∈ n.primeFactors, ArithmeticFunction.moebius p) *
        (∏ p ∈ n.primeFactors, ((p-1 : ℕ) : ℤ)) := Finset.prod_mul_distrib
    _ = _ := by
      rw [ArithmeticFunction.isMultiplicative_moebius.prod_primeFactors hn,
        ←Nat.cast_prod,←hphi]

/-- The genuine character coefficient in its finite divisor form.
This is the local algebra needed before any Fourier inversion or infinite sum. -/
theorem moebius_character_finite_divisor_sum (q N : ℕ) [NeZero q]
    (hq : Squarefree q) :
    ((ArithmeticFunction.moebius q : ℤ) : ℂ) *
        unitCharacterSum q (N : ZMod q) / (q.totient : ℂ) =
      (∑ d ∈ (Nat.gcd q N).divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)) /
          (q.totient : ℂ) := by
  have hp := canonical_pair_mem (N:=N)
    (mem_fullSquarefreePrefix.mpr ⟨le_rfl,hq⟩ : q ∈ fullSquarefreePrefix q)
  have ha := (mem_coupledSquarefreePairs.mp hp).1
  have hb := (mem_coupledSquarefreePairs.mp hp).2.1
  have hsum : (∑ d ∈ (Nat.gcd q N).divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)) =
      ((ArithmeticFunction.moebius (Nat.gcd q N) : ℤ) : ℂ) *
        ((Nat.gcd q N).totient : ℂ) := by
    exact_mod_cast squarefree_moebius_divisor_sum (Nat.gcd q N) ha
  have hphi : q.totient=(Nat.gcd q N).totient*(q/Nat.gcd q N).totient := by
    nth_rw 1 [←canonical_product q N]
    exact Nat.totient_mul (pair_factors_coprime hp)
  have hpa : ((Nat.gcd q N).totient : ℂ)≠0 := by
    exact_mod_cast (Nat.totient_pos.mpr ha.ne_zero.bot_lt).ne'
  have hpb : ((q/Nat.gcd q N).totient : ℂ)≠0 := by
    exact_mod_cast (Nat.totient_pos.mpr hb.ne_zero.bot_lt).ne'
  rw [moebius_character_quotient_gcd q N hq,hsum,hphi]
  push_cast
  field_simp


/-- The original finite companion with the actual finite divisor expansion
inserted. No infinite series, integration or truncation error is used. -/
theorem finite_companion_divisor_expansion {Q : ℕ} (r : PositiveLevel Q)
    (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r N w =
      ∑ l : PositiveLevel Q,
        if r.val*l.val≤Q ∧ Nat.Coprime r.val l.val ∧ Squarefree l.val then
          ((∑ d ∈ (Nat.gcd l.val N).divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)) /
              (l.val.totient : ℂ)) * w (r.val*l.val)
        else 0 := by
  unfold finiteCompanion
  apply Finset.sum_congr rfl
  intro l _
  by_cases hc : r.val*l.val≤Q
  · by_cases hcop : Nat.Coprime r.val l.val
    · rw [if_pos ⟨hc,hcop⟩]
      by_cases hs : Squarefree l.val
      · rw [if_pos ⟨hc,hcop,hs⟩,moebius_character_finite_divisor_sum l.val N hs]
      · rw [if_neg (by tauto : ¬(r.val*l.val≤Q ∧ Nat.Coprime r.val l.val ∧ Squarefree l.val))]
        simp only [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs,
          Int.cast_zero,zero_mul,zero_div]
    · simp [hcop]
  · simp [hc]

end GoldbachCircleMethodCompanionSquarefreeGcdBindingV18139
