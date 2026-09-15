import GoldbachCircleMethodActualResidualExactDecompositionV18225

/-!
# Goldbach V1.8.227: exact block-pair carrier

This module reduces the integer-frequency convolution at a natural target to
its literal finite pair carrier.  For the canonical half block it then proves
the exact closed interval of admissible first coordinates.  No periodic
diagonal, interval remainder estimate, source reserve, exceptional-set bound,
or Goldbach statement is inferred here.
-/

open scoped BigOperators Classical

set_option autoImplicit false

namespace GoldbachCircleMethodBlockPairCarrierV18227

open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodSupportedResidualParsevalV18190
open GoldbachCircleMethodUncorrectedSupportedErrorConvolutionV18184
open GoldbachCircleMethodCanonicalBumpPrincipalFloorV18220
open GoldbachCircleMethodActualResidualExactDecompositionV18225

/-- First coordinates in `J` whose natural complement at target `N` also
belongs to `J`. -/
def pairFirstCarrier (J : Finset ℕ) (N : ℕ) : Finset ℕ :=
  J.filter (fun n => N - n ∈ J)

/-- At a natural target, the integer-frequency pair convolution is exactly the
single sum over the complement-closed carrier.  The hypothesis prevents
truncated natural subtraction from manufacturing a false complement. -/
theorem integerPairConvolution_nat_eq_pairFirstCarrier
    (J : Finset ℕ) (v w : ℕ → ℂ) (N : ℕ)
    (hJN : ∀ n ∈ J, n ≤ N) :
    integerPairConvolution J v w (N : ℤ) =
      ∑ n ∈ pairFirstCarrier J N, v n * w (N - n) := by
  unfold integerPairConvolution pairFirstCarrier
  calc
    (∑ n ∈ J, ∑ u ∈ J,
        if (N : ℤ) = (n : ℤ) + (u : ℤ) then v n * w u else 0) =
        ∑ n ∈ J, if N - n ∈ J then v n * w (N - n) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hcomp : N - n ∈ J
      · rw [if_pos hcomp]
        have hnN : n ≤ N := hJN n hn
        have hNat : N = n + (N - n) := by omega
        have hInt : (N : ℤ) = (n : ℤ) + ((N - n : ℕ) : ℤ) := by
          exact_mod_cast hNat
        calc
          (∑ u ∈ J,
              if (N : ℤ) = (n : ℤ) + (u : ℤ) then v n * w u else 0) =
              (if (N : ℤ) = (n : ℤ) + ((N - n : ℕ) : ℤ) then
                v n * w (N - n) else 0) := by
            apply Finset.sum_eq_single (N - n)
            · intro u hu hune
              rw [if_neg]
              intro heq
              have hNat' : N = n + u := by exact_mod_cast heq
              have : u = N - n := by omega
              exact hune this
            · intro hnot
              exact (hnot hcomp).elim
          _ = v n * w (N - n) := by rw [if_pos hInt]
      · rw [if_neg hcomp]
        apply Finset.sum_eq_zero
        intro u hu
        rw [if_neg]
        intro heq
        have hNat : N = n + u := by exact_mod_cast heq
        have hnN : n ≤ N := hJN n hn
        have : u = N - n := by omega
        exact hcomp (this ▸ hu)
    _ = ∑ n ∈ J.filter (fun n => N - n ∈ J), v n * w (N - n) := by
      rw [Finset.sum_filter]

/-- Left endpoint of the literal pair interval in the upper-half block. -/
def blockPairLower (B N : ℕ) : ℕ := max (B / 2 + 1) (N - B)

/-- Right endpoint of the literal pair interval in the upper-half block. -/
def blockPairUpper (B N : ℕ) : ℕ := min B (N - (B / 2 + 1))

/-- The pair carrier of the canonical upper-half block is exactly a closed
natural interval.  This theorem fixes both endpoints and hence forbids a later
off-by-one or hidden empty-range substitution. -/
theorem pairFirstCarrier_block_eq_Icc
    (B N : ℕ) (hB : 1 ≤ B) (hBN : B ≤ N) :
    pairFirstCarrier (blockCarrier B) N =
      Finset.Icc (blockPairLower B N) (blockPairUpper B N) := by
  ext n
  simp only [pairFirstCarrier, blockCarrier, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_Icc, blockPairLower, blockPairUpper]
  omega

/-- Exact pair-carrier representation of the canonical supported principal
model at a natural target.  No interval diagonal has yet been substituted. -/
theorem canonicalPrincipalModelAt_nat_eq_pairFirstCarrier
    (B N : ℕ) (rho : ℝ) (hBN : B ≤ N) :
    canonicalPrincipalModelAt B rho (N : ℤ) =
      ∑ n ∈ pairFirstCarrier (blockCarrier B) N,
        supportedPrincipalModel B n ((B : ℝ) ^ rho) canonicalLogBump *
          supportedPrincipalModel B (N - n) ((B : ℝ) ^ rho)
            canonicalLogBump := by
  apply integerPairConvolution_nat_eq_pairFirstCarrier
  intro n hn
  simp only [blockCarrier, Finset.mem_Ioc] at hn
  omega

/-- Endpoint-explicit form of the preceding identity. -/
theorem canonicalPrincipalModelAt_nat_eq_interval
    (B N : ℕ) (rho : ℝ) (hB : 1 ≤ B) (hBN : B ≤ N) :
    canonicalPrincipalModelAt B rho (N : ℤ) =
      ∑ n ∈ Finset.Icc (blockPairLower B N) (blockPairUpper B N),
        supportedPrincipalModel B n ((B : ℝ) ^ rho) canonicalLogBump *
          supportedPrincipalModel B (N - n) ((B : ℝ) ^ rho)
            canonicalLogBump := by
  rw [canonicalPrincipalModelAt_nat_eq_pairFirstCarrier B N rho hBN,
    pairFirstCarrier_block_eq_Icc B N hB hBN]

end GoldbachCircleMethodBlockPairCarrierV18227
