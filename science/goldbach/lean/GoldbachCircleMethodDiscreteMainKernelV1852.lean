import GoldbachCircleMethodFiniteRemainderBudgetV1851
import Mathlib.Analysis.Fourier.AddCircle

/-! # V1.8.52: the actual unweighted discrete main polynomial.
It contains indices 1..M, not 0..M and not a continuous replacement.
The full Fourier coefficient is N-1 on 2<=N<=M. Local arc tails remain separate.
-/
open scoped BigOperators
namespace GoldbachCircleMethodDiscreteMainKernelV1852

noncomputable def discreteMainPolynomial (M : ℕ) (x : UnitAddCircle) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, fourier (n : ℤ) x

theorem discreteMainPolynomial_continuous (M : ℕ) :
    Continuous (discreteMainPolynomial M) := by
  unfold discreteMainPolynomial
  fun_prop

private theorem compact_integrable {f : UnitAddCircle → ℂ} (hf : Continuous f) :
    MeasureTheory.Integrable f AddCircle.haarAddCircle := by
  simpa only [MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_univ] using
    (ContinuousOn.integrableOn_compact (μ := AddCircle.haarAddCircle)
      (K := Set.univ) isCompact_univ hf.continuousOn)

private theorem coefficient_finite_character_sum {ι : Type*} (s : Finset ι)
    (k : ι → ℤ) (N : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => ∑ a ∈ s, fourier (k a) x) N =
      ∑ a ∈ s, if N = k a then (1 : ℂ) else 0 := by
  have hfun : (fun x : UnitAddCircle => ∑ a ∈ s, fourier (k a) x) =
      ∑ a ∈ s, (fourier (k a) : UnitAddCircle → ℂ) := by
    funext x
    simp only [Finset.sum_apply]
  rw [hfun, fourierCoeff.sum]
  · simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [congrFun (fourierCoeff_fourier (k a)) N]
    by_cases h : N = k a <;> simp [h]
  · intro a _
    exact compact_integrable (fourier (k a)).continuous

theorem discreteMainPolynomial_square_expansion (M : ℕ) (x : UnitAddCircle) :
    discreteMainPolynomial M x * discreteMainPolynomial M x =
      ∑ t ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        fourier ((t.1 : ℤ) + (t.2 : ℤ)) x := by
  simp only [discreteMainPolynomial, Finset.sum_product, fourier_add]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.mul_sum]

private theorem inner_pair_count (M N n : ℕ) (hNM : N ≤ M) (hn : 1 ≤ n) :
    (∑ m ∈ Finset.Icc 1 M, if (N : ℤ) = (n : ℤ) + (m : ℤ) then (1 : ℂ) else 0) =
      if n < N then 1 else 0 := by
  by_cases hnN : n < N
  · rw [if_pos hnN]
    have hm : N-n ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr (by omega)
    rw [Finset.sum_eq_single (N-n)]
    · have heq : (N : ℤ) = (n : ℤ) + ((N-n : ℕ) : ℤ) := by omega
      simp [heq]
    · intro m _ hne
      have hne' : (N : ℤ) ≠ (n : ℤ) + (m : ℤ) := by omega
      simp [hne']
    · exact fun h => (h hm).elim
  · rw [if_neg hnN]
    apply Finset.sum_eq_zero
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    have hne : (N : ℤ) ≠ (n : ℤ) + (m : ℤ) := by omega
    simp [hne]

theorem discreteMainPolynomial_square_fourierCoeff (M N : ℕ)
    (hN : 2 ≤ N) (hNM : N ≤ M) :
    fourierCoeff (fun x : UnitAddCircle =>
      discreteMainPolynomial M x * discreteMainPolynomial M x) (N : ℤ) =
        (N : ℂ) - 1 := by
  have hexp : (fun x : UnitAddCircle =>
      discreteMainPolynomial M x * discreteMainPolynomial M x) =
      fun x => ∑ t ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        fourier ((t.1 : ℤ)+(t.2 : ℤ)) x := by
    funext x
    exact discreteMainPolynomial_square_expansion M x
  rw [hexp, coefficient_finite_character_sum, Finset.sum_product]
  have hinner : (∑ n ∈ Finset.Icc 1 M,
      ∑ m ∈ Finset.Icc 1 M, if (N : ℤ) = (n : ℤ)+(m : ℤ) then (1 : ℂ) else 0) =
      ∑ n ∈ Finset.Icc 1 M, if n < N then (1 : ℂ) else 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    exact inner_pair_count M N n hNM (Finset.mem_Icc.mp hn).1
  rw [hinner, ← Finset.sum_filter]
  have hset : (Finset.Icc 1 M).filter (fun n => n < N) = Finset.Icc 1 (N-1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hset]
  simp [Nat.cast_sub (show 1 ≤ N by omega)]

noncomputable def discreteMainIntegrand (M N : ℕ) (x : UnitAddCircle) : ℂ :=
  fourier (-(N : ℤ)) x * (discreteMainPolynomial M x * discreteMainPolynomial M x)

theorem discreteMainIntegrand_integrable (M N : ℕ) :
    MeasureTheory.Integrable (discreteMainIntegrand M N) AddCircle.haarAddCircle := by
  apply compact_integrable
  exact (fourier (-(N : ℤ))).continuous.mul
    ((discreteMainPolynomial_continuous M).mul (discreteMainPolynomial_continuous M))

theorem integral_discreteMainIntegrand (M N : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M) :
    (∫ x : UnitAddCircle, discreteMainIntegrand M N x ∂AddCircle.haarAddCircle) =
      (N : ℂ) - 1 :=
  discreteMainPolynomial_square_fourierCoeff M N hN hNM

end GoldbachCircleMethodDiscreteMainKernelV1852
