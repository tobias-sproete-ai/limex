import GoldbachCircleMethodCompanionSquarefreeGcdBindingV18139

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFullSquarefreeCarrierV1846
open GoldbachCircleMethodCompanionSquarefreeGcdBindingV18139
open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteResiduePrefixV1866

namespace GoldbachCircleMethodCompanionDivisorReindexV18140

/-- The original finite index (q,d), d an arbitrary divisor of gcd(q,N). -/
def divisorIndex (N H : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (fullSquarefreePrefix H).sigma fun q => (Nat.gcd q N).divisors

/-- The complementary index (d,l), retaining d*l<=H. No coprimality
between l and N is imposed: d need not equal the entire gcd. -/
def complementIndex (N H : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (fullSquarefreePrefix H).sigma fun d =>
    (fullSquarefreePrefix (H/d)).filter fun l => d ∣ N ∧ Nat.Coprime d l

theorem mem_divisorIndex {q d N H : ℕ} :
    (⟨q,d⟩ : Σ _ : ℕ, ℕ) ∈ divisorIndex N H ↔
      q ≤ H ∧ Squarefree q ∧ d ∣ q ∧ d ∣ N := by
  simp only [divisorIndex,Finset.mem_sigma,mem_fullSquarefreePrefix,
    Nat.mem_divisors,Nat.dvd_gcd_iff]
  constructor
  · tauto
  · rintro ⟨hq,hs,hdq,hdN⟩
    exact ⟨⟨hq,hs⟩,⟨hdq,hdN⟩,Nat.gcd_ne_zero_left hs.ne_zero⟩

theorem mem_complementIndex {d l N H : ℕ} :
    (⟨d,l⟩ : Σ _ : ℕ, ℕ) ∈ complementIndex N H ↔
      Squarefree d ∧ Squarefree l ∧ Nat.Coprime d l ∧ d ∣ N ∧ d*l ≤ H := by
  simp only [complementIndex,Finset.mem_sigma,Finset.mem_filter,mem_fullSquarefreePrefix]
  constructor
  · rintro ⟨⟨_,hd⟩,⟨hl,hls⟩,hdN,hcop⟩
    exact ⟨hd,hls,hcop,hdN,by
      simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd.ne_zero.bot_lt).mp hl⟩
  · rintro ⟨hd,hl,hcop,hdN,hprod⟩
    have hdH := (Nat.le_mul_of_pos_right d hl.ne_zero.bot_lt).trans hprod
    exact ⟨⟨hdH,hd⟩,⟨(Nat.le_div_iff_mul_le hd.ne_zero.bot_lt).mpr
      (by simpa [Nat.mul_comm] using hprod),hl⟩,hdN,hcop⟩

theorem divisor_to_complement {q d N H : ℕ}
    (h : (⟨q,d⟩ : Σ _ : ℕ, ℕ) ∈ divisorIndex N H) :
    (⟨d,q/d⟩ : Σ _ : ℕ, ℕ) ∈ complementIndex N H := by
  obtain ⟨hq,hs,hdq,hdN⟩ := mem_divisorIndex.mp h
  have hprod : d*(q/d)=q := Nat.mul_div_cancel' hdq
  have hsprod : Squarefree (d*(q/d)) := by rwa [hprod]
  exact mem_complementIndex.mpr
    ⟨hsprod.of_mul_left,hsprod.of_mul_right,Nat.coprime_of_squarefree_mul hsprod,
      hdN,by rwa [hprod]⟩

theorem complement_to_divisor {d l N H : ℕ}
    (h : (⟨d,l⟩ : Σ _ : ℕ, ℕ) ∈ complementIndex N H) :
    (⟨d*l,d⟩ : Σ _ : ℕ, ℕ) ∈ divisorIndex N H := by
  obtain ⟨hd,hl,hcop,hdN,hprod⟩ := mem_complementIndex.mp h
  exact mem_divisorIndex.mpr
    ⟨hprod,(Nat.squarefree_mul hcop).mpr ⟨hd,hl⟩,dvd_mul_right d l,hdN⟩

/-- Exact finite reindexing; no truncation enlargement, convergence or
assumption on prime powers in N is used. -/
theorem finite_divisor_reindex {α : Type*} [AddCommMonoid α]
    (N H : ℕ) (f : ℕ → ℕ → α) :
    (∑ q ∈ fullSquarefreePrefix H, ∑ d ∈ (Nat.gcd q N).divisors, f q d) =
      ∑ d ∈ fullSquarefreePrefix H,
        ∑ l ∈ (fullSquarefreePrefix (H/d)).filter (fun l => d ∣ N ∧ Nat.Coprime d l),
          f (d*l) d := by
  rw [Finset.sum_sigma',Finset.sum_sigma']
  change (∑ t ∈ divisorIndex N H, f t.1 t.2) =
    ∑ t ∈ complementIndex N H, f (t.1*t.2) t.1
  exact Finset.sum_nbij'
    (fun (t : Σ _ : ℕ, ℕ) => (⟨t.2,t.1/t.2⟩ : Σ _ : ℕ, ℕ))
    (fun (t : Σ _ : ℕ, ℕ) => (⟨t.1*t.2,t.1⟩ : Σ _ : ℕ, ℕ))
    (fun _ h => divisor_to_complement h)
    (fun _ h => complement_to_divisor h)
    (fun t h => by
      have ht := (mem_divisorIndex.mp h).2.2.1
      simp only [Nat.mul_div_cancel' ht])
    (fun t h => by
      have ht := (mem_complementIndex.mp h).1.ne_zero.bot_lt
      simp only [Nat.mul_div_cancel_left _ ht])
    (fun t h => by
      have ht := (mem_divisorIndex.mp h).2.2.1
      simp only [Nat.mul_div_cancel' ht])


/-- Natural-index version of the actual companion divisor expansion,
with the original cutoff H=Q/r and weight w(r*q). -/
theorem finite_companion_natural_divisor_expansion {Q : ℕ}
    (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r N w =
      ∑ q ∈ fullSquarefreePrefix (Q/r.val),
        ∑ d ∈ (Nat.gcd q N).divisors,
          if Nat.Coprime r.val q then
            (((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ) /
              (q.totient : ℂ)) * w (r.val*q)
          else 0 := by
  rw [finite_companion_squarefree_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hs := (mem_fullSquarefreePrefix.mp hq).2
  have : NeZero q := ⟨hs.ne_zero⟩
  by_cases hc : Nat.Coprime r.val q
  · rw [if_pos hc]
    simp_rw [if_pos hc]
    rw [←moebius_character_quotient_gcd q N hs,
      moebius_character_finite_divisor_sum q N hs]
    rw [Finset.sum_div,Finset.sum_mul]
  · simp only [hc,if_false,Finset.sum_const_zero]

/-- The existing companion reindexed along q=d*l. The complementary
factor l is constrained by coprimality with d and r, NOT with N. -/
theorem finite_companion_complement_sum {Q : ℕ}
    (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r N w =
      ∑ d ∈ fullSquarefreePrefix (Q/r.val),
        ∑ l ∈ (fullSquarefreePrefix ((Q/r.val)/d)).filter
            (fun l => d ∣ N ∧ Nat.Coprime d l),
          if Nat.Coprime r.val d ∧ Nat.Coprime r.val l then
            (((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ) /
              ((d.totient : ℂ)*(l.totient : ℂ))) * w (r.val*(d*l))
          else 0 := by
  rw [finite_companion_natural_divisor_expansion,finite_divisor_reindex]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro l hl
  have hcop := (Finset.mem_filter.mp hl).2.2
  rw [Nat.totient_mul hcop]
  simp only [Nat.cast_mul,Nat.coprime_mul_iff_right]

/-- Concrete regression witness: the complementary divisor need not be
coprime to the input, even when that input contains a prime square. -/
theorem complement_need_not_coprime_input :
    (⟨1,2⟩ : Σ _ : ℕ, ℕ) ∈ complementIndex 4 2 ∧ ¬Nat.Coprime 2 4 := by
  constructor
  · exact mem_complementIndex.mpr
      ⟨squarefree_one,Nat.prime_two.squarefree,by decide,by decide,by decide⟩
  · decide

/-- Factored finite divisor form. The inner cutoff remains Q/(r*d);
the weight remains on the coupled product. No infinite extension is made. -/
theorem finite_companion_factored_divisor_sum {Q : ℕ}
    (r : PositiveLevel Q) (N : ℕ) (w : ℕ → ℂ) :
    finiteCompanion r N w =
      ∑ d ∈ (fullSquarefreePrefix (Q/r.val)).filter
          (fun d => d ∣ N ∧ Nat.Coprime r.val d),
        (((ArithmeticFunction.moebius d : ℤ) : ℂ)*(d : ℂ)/(d.totient : ℂ)) *
          ∑ l ∈ (fullSquarefreePrefix (Q/(r.val*d))).filter
              (fun l => Nat.Coprime (r.val*d) l),
            w (r.val*d*l)/(l.totient : ℂ) := by
  rw [finite_companion_complement_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hdN : d ∣ N
  · by_cases hrd : Nat.Coprime r.val d
    · rw [if_pos ⟨hdN,hrd⟩,Finset.mul_sum]
      rw [Nat.div_div_eq_div_mul]
      rw [Finset.sum_filter,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hdl : Nat.Coprime d l
      · by_cases hrl : Nat.Coprime r.val l
        · simp only [Nat.coprime_mul_iff_left]
          rw [if_pos (show d ∣ N ∧ Nat.Coprime d l from ⟨hdN,hdl⟩),
            if_pos (show Nat.Coprime r.val d ∧ Nat.Coprime r.val l from ⟨hrd,hrl⟩),
            if_pos (show Nat.Coprime r.val l ∧ Nat.Coprime d l from ⟨hrl,hdl⟩)]
          rw [Nat.mul_assoc]
          ring
        · simp only [Nat.coprime_mul_iff_left]
          simp [hdN,hrl]
      · simp only [Nat.coprime_mul_iff_left]
        simp [hdl]
    · simp [hrd]
  · simp [hdN]

end GoldbachCircleMethodCompanionDivisorReindexV18140
