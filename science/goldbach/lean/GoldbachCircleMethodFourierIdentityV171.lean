import Mathlib.Analysis.Fourier.AddCircle
import GoldbachCircleMethodTargetV17

/-!
# Exact finite Fourier identity, V1.7.1 candidate

This module proves an exact coefficient identity for the finite von Mangoldt
exponential sum. It does not define major or minor arcs, estimate a remainder,
construct the V1.7 dominance interface, or prove Goldbach's conjecture.
-/

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodFourierIdentityV171

open GoldbachVonMangoldtDecompositionV16

/-- The finite von Mangoldt exponential sum on the unit additive circle. -/
noncomputable def exponentialSum (cutoff : Nat) : C(UnitAddCircle, Complex) :=
  ∑ n ∈ Finset.range cutoff,
    (ArithmeticFunction.vonMangoldt n : Complex) • fourier (n : Int)

private lemma integrable_const_mul_fourier (c : Complex) (n : Int) :
    MeasureTheory.Integrable
      (fun x : UnitAddCircle => c * fourier n x)
      AddCircle.haarAddCircle := by
  have h : MeasureTheory.Integrable
      (fourier n : UnitAddCircle → Complex) AddCircle.haarAddCircle := by
    simpa only [MeasureTheory.IntegrableOn,
      MeasureTheory.Measure.restrict_univ] using
      (ContinuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle)
        (K := Set.univ) isCompact_univ (fourier n).continuous.continuousOn)
  exact h.const_mul c

private lemma coeff_const_mul_fourier (c : Complex) (n k : Int) :
    fourierCoeff (fun x : UnitAddCircle => c * fourier n x) k =
      if k = n then c else 0 := by
  rw [fourierCoeff.const_mul]
  rw [congrFun (fourierCoeff_fourier n) k]
  by_cases h : k = n
  · subst k
    simp
  · simp [h]

private lemma coeff_finset_fourier_sum
    (s : Finset Nat) (c : Nat → Complex) (frequency : Nat → Int) (k : Int) :
    fourierCoeff
        (fun x : UnitAddCircle =>
          ∑ n ∈ s, c n * fourier (frequency n) x) k =
      ∑ n ∈ s, if k = frequency n then c n else 0 := by
  have hFunction :
      (fun x : UnitAddCircle =>
        ∑ n ∈ s, c n * fourier (frequency n) x) =
        ∑ n ∈ s,
          (fun x : UnitAddCircle => c n * fourier (frequency n) x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hFunction, fourierCoeff.sum]
  simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro n hn
    exact coeff_const_mul_fourier _ _ _
  · intro n hn
    exact integrable_const_mul_fourier _ _

private lemma integrable_finset_fourier_sum
    (s : Finset Nat) (c : Nat → Complex) (frequency : Nat → Int) :
    MeasureTheory.Integrable
      (fun x : UnitAddCircle =>
        ∑ n ∈ s, c n * fourier (frequency n) x)
      AddCircle.haarAddCircle := by
  have hFunction :
      (fun x : UnitAddCircle =>
        ∑ n ∈ s, c n * fourier (frequency n) x) =
        ∑ n ∈ s,
          (fun x : UnitAddCircle => c n * fourier (frequency n) x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hFunction]
  exact MeasureTheory.integrable_finsetSum' _ fun n hn =>
    integrable_const_mul_fourier _ _

/-- The finite double Fourier polynomial obtained by expanding the square. -/
noncomputable def expandedSquare (N : Nat) : UnitAddCircle → Complex :=
  fun x =>
    ∑ n ∈ Finset.range N.succ,
      ∑ m ∈ Finset.range N.succ,
        ((ArithmeticFunction.vonMangoldt n : Complex) *
            ArithmeticFunction.vonMangoldt m) *
          fourier ((n : Int) + (m : Int)) x

private lemma coeff_expandedSquare (N : Nat) :
    fourierCoeff (expandedSquare N) (N : Int) =
      ∑ n ∈ Finset.range N.succ,
        ∑ m ∈ Finset.range N.succ,
          if (N : Int) = (n : Int) + (m : Int) then
            (ArithmeticFunction.vonMangoldt n : Complex) *
              ArithmeticFunction.vonMangoldt m
          else 0 := by
  unfold expandedSquare
  have hOuter :
      (fun x : UnitAddCircle =>
        ∑ n ∈ Finset.range N.succ,
          ∑ m ∈ Finset.range N.succ,
            ((ArithmeticFunction.vonMangoldt n : Complex) *
                ArithmeticFunction.vonMangoldt m) *
              fourier ((n : Int) + (m : Int)) x) =
        ∑ n ∈ Finset.range N.succ,
          (fun x : UnitAddCircle =>
            ∑ m ∈ Finset.range N.succ,
              ((ArithmeticFunction.vonMangoldt n : Complex) *
                  ArithmeticFunction.vonMangoldt m) *
                fourier ((n : Int) + (m : Int)) x) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hOuter, fourierCoeff.sum]
  simp only [Finset.sum_apply]
  · apply Finset.sum_congr rfl
    intro n hn
    exact coeff_finset_fourier_sum
      (Finset.range N.succ)
      (fun m => (ArithmeticFunction.vonMangoldt n : Complex) *
        ArithmeticFunction.vonMangoldt m)
      (fun m => (n : Int) + (m : Int))
      (N : Int)
  · intro n hn
    exact integrable_finset_fourier_sum
      (Finset.range N.succ)
      (fun m => (ArithmeticFunction.vonMangoldt n : Complex) *
        ArithmeticFunction.vonMangoldt m)
      (fun m => (n : Int) + (m : Int))

private lemma exponentialSum_sq_eq_expandedSquare
    (N : Nat) (x : UnitAddCircle) :
    exponentialSum N.succ x * exponentialSum N.succ x = expandedSquare N x := by
  have hExponential : exponentialSum N.succ x =
      ∑ n ∈ Finset.range N.succ,
        (ArithmeticFunction.vonMangoldt n : Complex) * fourier (n : Int) x := by
    simp [exponentialSum]
  have hExpanded : expandedSquare N x =
      ∑ n ∈ Finset.range N.succ,
        ∑ m ∈ Finset.range N.succ,
          ((ArithmeticFunction.vonMangoldt n : Complex) *
              ArithmeticFunction.vonMangoldt m) *
            fourier ((n : Int) + (m : Int)) x := rfl
  rw [hExponential, hExpanded]
  show
    (∑ n ∈ Finset.range N.succ,
      (ArithmeticFunction.vonMangoldt n : Complex) * fourier (n : Int) x) *
      (∑ m ∈ Finset.range N.succ,
        (ArithmeticFunction.vonMangoldt m : Complex) * fourier (m : Int) x) =
      ∑ n ∈ Finset.range N.succ,
        ∑ m ∈ Finset.range N.succ,
          ((ArithmeticFunction.vonMangoldt n : Complex) *
              ArithmeticFunction.vonMangoldt m) *
            fourier ((n : Int) + (m : Int)) x
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [fourier_add]
  ring

private lemma inner_frequency_N_sum
    (N n : Nat) (hn : n ∈ Finset.range N.succ) :
    (∑ m ∈ Finset.range N.succ,
      if (N : Int) = (n : Int) + (m : Int) then
        (ArithmeticFunction.vonMangoldt n : Complex) *
          ArithmeticFunction.vonMangoldt m
      else 0) =
      (ArithmeticFunction.vonMangoldt n : Complex) *
        ArithmeticFunction.vonMangoldt (N - n) := by
  have hnle : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
  calc
    _ = if (N : Int) = (n : Int) + ((N - n : Nat) : Int) then
          (ArithmeticFunction.vonMangoldt n : Complex) *
            ArithmeticFunction.vonMangoldt (N - n)
        else 0 := by
      apply Finset.sum_eq_single (N - n)
      · intro m hm hne
        rw [if_neg]
        intro heq
        norm_cast at heq
        apply hne
        omega
      · intro hnotmem
        exfalso
        apply hnotmem
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le N n))
    _ = _ := by
      rw [if_pos]
      norm_cast
      omega

private lemma vonMangoldt_zero : ArithmeticFunction.vonMangoldt 0 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
  exact not_isPrimePow_zero

private lemma complex_vonMangoldt_pair_sum_range_succ (N : Nat) :
    (∑ n ∈ Finset.range N.succ,
      (ArithmeticFunction.vonMangoldt n : Complex) *
        ArithmeticFunction.vonMangoldt (N - n)) =
      (vonMangoldtPairSum N : Complex) := by
  rw [Finset.sum_range_succ]
  rw [show N - N = 0 by omega, vonMangoldt_zero]
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  rw [vonMangoldtPairSum]
  norm_cast

/--
The `N`-th Fourier coefficient of the exact finite square equals the ordered
von Mangoldt convolution already defined in V1.6. This is a finite algebraic
identity only; it supplies no positivity or asymptotic estimate.
-/
theorem fourierCoeff_exponentialSum_sq_eq_vonMangoldtPairSum (N : Nat) :
    fourierCoeff
        (fun x : UnitAddCircle =>
          exponentialSum N.succ x * exponentialSum N.succ x)
        (N : Int) =
      (vonMangoldtPairSum N : Complex) := by
  have hFunction :
      (fun x : UnitAddCircle =>
        exponentialSum N.succ x * exponentialSum N.succ x) =
        expandedSquare N := by
    funext x
    exact exponentialSum_sq_eq_expandedSquare N x
  rw [hFunction, coeff_expandedSquare]
  calc
    _ = ∑ n ∈ Finset.range N.succ,
        (ArithmeticFunction.vonMangoldt n : Complex) *
          ArithmeticFunction.vonMangoldt (N - n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact inner_frequency_N_sum N n hn
    _ = (vonMangoldtPairSum N : Complex) :=
      complex_vonMangoldt_pair_sum_range_succ N

end GoldbachCircleMethodFourierIdentityV171
