import GoldbachCircleMethodTwoScaleMaskAdapterV1829

/-!
# Two-scale Dirichlet binding, V1.8.30

Reuses the existing V1.7.6 Dirichlet theorem with auxiliary parameters
`N = Q`, `R = 1`. These are local approximation parameters, not a change
to the Fourier length or Goldbach target. V1.8.29's mask is unchanged.
No exponential-sum estimate or Goldbach theorem is asserted.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodTwoScaleDirichletBindingV1830

open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodMinorLocalizationV176
open GoldbachCircleMethodTwoScaleMaskAdapterV1829

/-- Exact reciprocal-radius interface supplied by the existing Dirichlet proof. -/
theorem exists_reduced_approximant_reciprocal_radius
    (Q : Nat) (hQ : 0 < Q) (x : UnitAddCircle) :
    ∃ i : ReducedRationalIndex Q,
      dist x (majorArcCenter i) ≤
        1 / (((i.1.1 : Nat) : Real) * (Q : Real)) := by
  let auxiliary : ArcParameters := ⟨Q, 1, hQ, by decide⟩
  have hCoupling : auxiliary.N ≤ auxiliary.R * (Q + 1) := by
    change Q ≤ 1 * (Q + 1)
    omega
  obtain ⟨i, hi⟩ := exists_dirichlet_index auxiliary Q hQ hCoupling x
  exact ⟨i, by simpa only [localizationRadius, auxiliary, Nat.cast_one] using hi⟩

/-- Outside the fixed two-scale major mask, an actual Dirichlet index has
`R0 < q ≤ Q`; no separate approximation-existence premise is required. -/
theorem exists_dirichlet_outside_twoScaleMajorMask
    (M P Q R0 : Nat)
    (hM : 0 < M) (hP : 0 < P)
    (hQ : Q = ⌈(M : Real) / (P : Real)⌉₊)
    (x : UnitAddCircle) (hx : x ∉ twoScaleMajorMask M P R0) :
    ∃ i : ReducedRationalIndex Q,
      R0 < i.1.1 ∧ i.1.1 ≤ Q ∧
      dist x (majorArcCenter i) ≤
        1 / (((i.1.1 : Nat) : Real) * (Q : Real)) := by
  have hQpos : 0 < Q := by
    rw [hQ]
    exact Nat.ceil_pos.mpr
      (div_pos (Nat.cast_pos.mpr hM) (Nat.cast_pos.mpr hP))
  exact exists_large_denominator_approximant_of_outside_twoScaleMajorMask
    M P Q R0 hM hP hQ
    (exists_reduced_approximant_reciprocal_radius Q hQpos) x hx

end GoldbachCircleMethodTwoScaleDirichletBindingV1830
