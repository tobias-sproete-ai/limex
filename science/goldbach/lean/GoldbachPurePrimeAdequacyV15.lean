import Mathlib

/-!
# Pure-prime support adequacy for binary Goldbach, V1.5

This module proves that the canonical finite support, its cardinality, and its
positive logarithmic fibre sum detect exactly the same pointwise Goldbach
statement. It contains no analytic estimate proving positivity for arbitrary
even inputs.
-/

set_option autoImplicit false

open scoped BigOperators

namespace GoldbachPurePrimeAdequacyV15

/-- Pointwise binary Goldbach statement at the natural number `N`. -/
def GoldbachAt (N : Nat) : Prop :=
  ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p + q = N

/-- Canonical finite support of ordered prime-pair candidates at `N`. -/
def goldbachPairs (N : Nat) : Finset Nat :=
  (Finset.range N).filter
    (fun p => Nat.Prime p ∧ Nat.Prime (N - p))

/-- Number of elements in the canonical ordered support. -/
def representationCount (N : Nat) : Nat :=
  (goldbachPairs N).card

theorem mem_goldbachPairs_iff {N p : Nat} :
    p ∈ goldbachPairs N ↔
      p < N ∧ Nat.Prime p ∧ Nat.Prime (N - p) := by
  simp [goldbachPairs]

/-- The finite support is inhabited exactly when `N` has a prime-pair witness. -/
theorem representationCount_pos_iff_goldbachAt (N : Nat) :
    0 < representationCount N ↔ GoldbachAt N := by
  constructor
  · intro hCount
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hCount
    have hpData := mem_goldbachPairs_iff.mp hp
    exact ⟨p, N - p, hpData.2.1, hpData.2.2, by omega⟩
  · rintro ⟨p, q, hpPrime, hqPrime, hpq⟩
    have hqTwo : 2 ≤ q := hqPrime.two_le
    have hpLt : p < N := by omega
    have hqEq : N - p = q := by omega
    apply Finset.card_pos.mpr
    refine ⟨p, mem_goldbachPairs_iff.mpr ?_⟩
    exact ⟨hpLt, hpPrime, hqEq.symm ▸ hqPrime⟩

/-- Positive logarithmic weight used by the pure-prime fibre. -/
noncomputable def purePrimeWeight (N p : Nat) : Real :=
  Real.log (p : Real) * Real.log ((N - p : Nat) : Real)

/-- Canonical logarithmically weighted pure-prime fibre sum. -/
noncomputable def purePrimeSum (N : Nat) : Real :=
  ∑ p ∈ goldbachPairs N, purePrimeWeight N p

theorem purePrimeWeight_pos {N p : Nat} (hp : p ∈ goldbachPairs N) :
    0 < purePrimeWeight N p := by
  have hpData := mem_goldbachPairs_iff.mp hp
  have hpOneNat : 1 < p := hpData.2.1.one_lt
  have hqOneNat : 1 < N - p := hpData.2.2.one_lt
  have hpOneReal : (1 : Real) < (p : Real) := by
    exact_mod_cast hpOneNat
  have hqOneReal : (1 : Real) < ((N - p : Nat) : Real) := by
    exact_mod_cast hqOneNat
  exact mul_pos (Real.log_pos hpOneReal) (Real.log_pos hqOneReal)

/-- The weighted fibre is positive exactly when its finite support is nonempty. -/
theorem purePrimeSum_pos_iff_representationCount_pos (N : Nat) :
    0 < purePrimeSum N ↔ 0 < representationCount N := by
  constructor
  · intro hSum
    by_contra hCount
    have hCardZero : (goldbachPairs N).card = 0 := by
      simpa [representationCount] using Nat.eq_zero_of_not_pos hCount
    have hEmpty : goldbachPairs N = ∅ := Finset.card_eq_zero.mp hCardZero
    have hSumZero : purePrimeSum N = 0 := by
      simp [purePrimeSum, hEmpty]
    linarith
  · intro hCount
    have hNonempty : (goldbachPairs N).Nonempty := by
      exact Finset.card_pos.mp hCount
    simpa [purePrimeSum] using
      Finset.sum_pos (fun p hp => purePrimeWeight_pos hp) hNonempty

/-- Canonical adequacy bridge: positivity means exactly a strict prime pair. -/
theorem purePrimeSum_pos_iff_strictGoldbach (N : Nat) :
    0 < purePrimeSum N ↔ GoldbachAt N := by
  rw [purePrimeSum_pos_iff_representationCount_pos,
    representationCount_pos_iff_goldbachAt]

/-!
The next analytic route may use the von Mangoldt function, but must preserve
the defining weight `Λ(p^k) = log p`; it must not replace it by
`log(p^k) = k * log p`.
-/

end GoldbachPurePrimeAdequacyV15
