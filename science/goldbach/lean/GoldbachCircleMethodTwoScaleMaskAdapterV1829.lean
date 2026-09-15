import GoldbachCircleMethodTwoScaleElementaryKernelV1828

/-!
# Internal two-scale mask adapter, V1.8.29 source candidate

This module separates the denominator cutoff `R0` from the radius numerator
`P`.  It proves only the finite geometric adapter needed by the V1.8.27
two-scale candidate: a reduced Dirichlet approximant at
`Q = ceil (M / P)` cannot have denominator at most `R0` when the point lies
outside every `P / (q * M)` arc with denominator at most `R0`.

The existence of the approximant is an explicit parameter.  No Dirichlet
approximation theorem, Fourier identity, analytic estimate, or Goldbach result
is introduced here.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodTwoScaleMaskAdapterV1829

open GoldbachCircleMethodMajorMinorPartitionV172

/-- Radius `P / (q * M)` for one reduced rational index. -/
noncomputable def twoScaleArcRadius (M P : Nat) {Q : Nat}
    (i : ReducedRationalIndex Q) : Real :=
  (P : Real) / (((i.1.1 : Nat) : Real) * (M : Real))

/--
The fixed internal two-scale mask.  The cutoff is `R0`, while `P` controls
the width; unlike `majorArcs`, these are intentionally independent inputs.
-/
noncomputable def twoScaleMajorMask (M P R0 : Nat) : Set UnitAddCircle :=
  ⋃ i : ReducedRationalIndex R0,
    Metric.closedBall (majorArcCenter i) (twoScaleArcRadius M P i)

/--
A reduced approximation returned at `Q = ceil (M / P)` has denominator above
`R0` whenever its point is outside the fixed two-scale mask.

The proof first derives
`1 / (q * Q) ≤ P / (q * M)` from the natural-ceiling inequality.  If
`q ≤ R0`, the same reduced pair can then be re-indexed at cutoff `R0`, which
would put `x` inside the mask and contradict `hx`.
-/
theorem returned_denominator_gt_R0_of_outside_twoScaleMajorMask
    (M P Q R0 : Nat)
    (hM : 0 < M) (hP : 0 < P)
    (hQ : Q = ⌈(M : Real) / (P : Real)⌉₊)
    (x : UnitAddCircle) (i : ReducedRationalIndex Q)
    (hiApprox :
      dist x (majorArcCenter i) ≤
        1 / (((i.1.1 : Nat) : Real) * (Q : Real)))
    (hx : x ∉ twoScaleMajorMask M P R0) :
    R0 < i.1.1 := by
  have hMReal : (0 : Real) < (M : Real) := Nat.cast_pos.mpr hM
  have hPReal : (0 : Real) < (P : Real) := Nat.cast_pos.mpr hP
  have hRatioPos : (0 : Real) < (M : Real) / (P : Real) :=
    div_pos hMReal hPReal
  have hQNat : 0 < Q := by
    rw [hQ]
    exact Nat.ceil_pos.mpr hRatioPos
  have hQReal : (0 : Real) < (Q : Real) := Nat.cast_pos.mpr hQNat
  have hqReal : (0 : Real) < (i.1.1 : Nat) :=
    Nat.cast_pos.mpr (index_denominator_pos i)
  have hCeil : (M : Real) / (P : Real) ≤ (Q : Real) := by
    rw [hQ]
    exact Nat.le_ceil _
  have hMQ : (M : Real) ≤ (P : Real) * (Q : Real) := by
    rw [div_le_iff₀ hPReal] at hCeil
    simpa only [mul_comm] using hCeil
  have hRadius :
      1 / (((i.1.1 : Nat) : Real) * (Q : Real)) ≤
        twoScaleArcRadius M P i := by
    unfold twoScaleArcRadius
    rw [div_le_div_iff₀ (mul_pos hqReal hQReal)
      (mul_pos hqReal hMReal)]
    calc
      (1 : Real) * ((i.1.1 : Nat) * (M : Real)) =
          (i.1.1 : Nat) * (M : Real) := by ring
      _ ≤ (i.1.1 : Nat) * ((P : Real) * (Q : Real)) :=
        mul_le_mul_of_nonneg_left hMQ hqReal.le
      _ = (P : Real) * ((i.1.1 : Nat) * (Q : Real)) := by ring
  by_contra hnot
  have hqLeR0 : i.1.1 ≤ R0 := Nat.le_of_not_gt hnot
  have hiFilter := Finset.mem_filter.mp i.2
  have haLtQ := hiFilter.2.1
  have haCoprimeQ := hiFilter.2.2
  let j : ReducedRationalIndex R0 :=
    ⟨i.1, by
      unfold reducedRationalPairs
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨index_denominator_pos i, hqLeR0⟩,
            Finset.mem_range.mpr (haLtQ.trans_le hqLeR0)⟩
      · exact ⟨haLtQ, haCoprimeQ⟩⟩
  apply hx
  simp only [twoScaleMajorMask, Set.mem_iUnion]
  refine ⟨j, ?_⟩
  rw [Metric.mem_closedBall]
  have hBound := hiApprox.trans hRadius
  simpa only [j, majorArcCenter, twoScaleArcRadius] using hBound

/--
Quantified adapter for a supplied reduced-approximation interface.  The
result exposes both sides of the denominator window `R0 < q ≤ Q`.
No separate `R0 < Q` premise is needed: it follows from the resulting window.
-/
theorem exists_large_denominator_approximant_of_outside_twoScaleMajorMask
    (M P Q R0 : Nat)
    (hM : 0 < M) (hP : 0 < P)
    (hQ : Q = ⌈(M : Real) / (P : Real)⌉₊)
    (hApprox : ∀ x : UnitAddCircle,
      ∃ i : ReducedRationalIndex Q,
        dist x (majorArcCenter i) ≤
          1 / (((i.1.1 : Nat) : Real) * (Q : Real)))
    (x : UnitAddCircle) (hx : x ∉ twoScaleMajorMask M P R0) :
    ∃ i : ReducedRationalIndex Q,
      R0 < i.1.1 ∧ i.1.1 ≤ Q ∧
      dist x (majorArcCenter i) ≤
        1 / (((i.1.1 : Nat) : Real) * (Q : Real)) := by
  rcases hApprox x with ⟨i, hiApprox⟩
  refine ⟨i,
    returned_denominator_gt_R0_of_outside_twoScaleMajorMask
      M P Q R0 hM hP hQ x i hiApprox hx,
    ?_, hiApprox⟩
  have hiFilter := Finset.mem_filter.mp i.2
  have hiProduct := Finset.mem_product.mp hiFilter.1
  exact (Finset.mem_Icc.mp hiProduct.1).2

end GoldbachCircleMethodTwoScaleMaskAdapterV1829
