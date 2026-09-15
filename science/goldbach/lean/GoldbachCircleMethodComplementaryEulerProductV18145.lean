import GoldbachCircleMethodLogWeightMellinBindingV18144
import Mathlib.NumberTheory.EulerProduct.Basic

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodCompanionAbsoluteConvergenceV18141

namespace GoldbachCircleMethodComplementaryEulerProductV18145

theorem complementary_zero (k : ℕ) (s : ℂ) :
    complementaryDirichletTerm k s 0 = 0 := by
  simp [complementaryDirichletTerm]

theorem complementary_one (k : ℕ) (s : ℂ) :
    complementaryDirichletTerm k s 1 = 1 := by
  simp [complementaryDirichletTerm]

theorem complementary_multiplicative (k : ℕ) (s : ℂ) {m n : ℕ}
    (hmn : Nat.Coprime m n) :
    complementaryDirichletTerm k s (m*n) =
      complementaryDirichletTerm k s m * complementaryDirichletTerm k s n := by
  have hg : (Squarefree (m*n) ∧ Nat.Coprime k (m*n)) ↔
      (Squarefree m ∧ Nat.Coprime k m) ∧ (Squarefree n ∧ Nat.Coprime k n) := by
    rw [Nat.squarefree_mul_iff,Nat.coprime_mul_iff_right]
    tauto
  unfold complementaryDirichletTerm
  by_cases hm : Squarefree m ∧ Nat.Coprime k m
  · by_cases hn : Squarefree n ∧ Nat.Coprime k n
    · rw [if_pos (hg.mpr ⟨hm,hn⟩),if_pos hm,if_pos hn,Nat.totient_mul hmn]
      push_cast
      rw [Complex.natCast_mul_natCast_cpow]
      ring
    · have hbad : ¬(Squarefree (m*n) ∧ Nat.Coprime k (m*n)) :=
        fun h => hn (hg.mp h).2
      simp only [if_neg hbad,if_neg hn,mul_zero]
  · have hbad : ¬(Squarefree (m*n) ∧ Nat.Coprime k (m*n)) :=
      fun h => hm (hg.mp h).1
    simp only [if_neg hbad,if_neg hm,zero_mul]

theorem complementary_prime_power_zero (k : ℕ) (s : ℂ) {p e : ℕ}
    (hp : p.Prime) (he : 2 ≤ e) :
    complementaryDirichletTerm k s (p^e) = 0 := by
  have hs : ¬Squarefree (p^e) := by
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega : e ≠ 0)]
    omega
  simp only [complementaryDirichletTerm,hs,false_and,if_false]

/-- Literal prime local factor of the actual complementary series.
When p divides k the factor is one, not an omitted coprimality premise. -/
noncomputable def complementaryLocalFactor (k : ℕ) (s : ℂ) (p : ℕ) : ℂ :=
  if p ∣ k then 1 else 1+1/((p.totient : ℂ)*(p : ℂ)^s)

theorem complementary_prime_power_sum (k : ℕ) (s : ℂ) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, complementaryDirichletTerm k s (p^e)) =
      complementaryLocalFactor k s p := by
  have hfin : HasSum (fun e : ℕ => complementaryDirichletTerm k s (p^e))
      (∑ e ∈ ({0,1} : Finset ℕ), complementaryDirichletTerm k s (p^e)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro e he
    have he2 : 2 ≤ e := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at he
      omega
    exact complementary_prime_power_zero k s hp he2
  rw [hfin.tsum_eq]
  simp only [Finset.sum_insert,Finset.mem_singleton,zero_ne_one,not_false_eq_true,
    Finset.sum_singleton,pow_zero,pow_one,complementary_one]
  unfold complementaryLocalFactor complementaryDirichletTerm
  have hk : Nat.Coprime k p ↔ ¬p ∣ k := Nat.coprime_comm.trans hp.coprime_iff_not_dvd
  simp only [hk]
  by_cases hpk : p ∣ k
  · simp [hpk]
  · simp [hpk,hp.squarefree]

theorem complementary_euler_hasProd (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasProd (fun p : Nat.Primes => complementaryLocalFactor k s p)
      (∑' n, complementaryDirichletTerm k s n) := by
  have hp := EulerProduct.eulerProduct_hasProd
    (complementary_one k s) (complementary_multiplicative k s)
    (summable_complementaryDirichletTerm_norm k hs) (complementary_zero k s)
  have he : (fun p : Nat.Primes => ∑' e : ℕ, complementaryDirichletTerm k s (p.val^e)) =
      (fun p : Nat.Primes => complementaryLocalFactor k s p.val) :=
    funext (fun p => complementary_prime_power_sum k s p.property)
  rw [he] at hp
  exact hp

end GoldbachCircleMethodComplementaryEulerProductV18145
