import GoldbachCircleMethodMinorLocalizationV176

/-!
# Sharpened minor-arc localization, V1.7.7 probe

This file adds only arithmetic consequences of an explicit cutoff coupling,
negation symmetry of the minimal admitted denominator, and a concrete real
lift realizing the torus-distance witness. It introduces no analytic estimate.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodMinorLocalizationSharpV177

open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodMinorLocalizationV176

/-- The extra cutoff condition forces the selected denominator below `N / R`. -/
theorem R_mul_qStar_lt_N (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (hCutoff : p.R * Q < p.N) (x : UnitAddCircle) :
    p.R * qStar p Q hQ hCoupling x < p.N := by
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_left p.R (qStar_le_Q p Q hQ hCoupling x)) hCutoff

/-- The V1.7.6 radius is strictly smaller than the classical `q⁻²` scale. -/
theorem qStar_radius_lt_inv_sq (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (hCutoff : p.R * Q < p.N) (x : UnitAddCircle) :
    (p.R : Real) /
        (((qStar p Q hQ hCoupling x : Nat) : Real) * (p.N : Real)) <
      1 / (((qStar p Q hQ hCoupling x : Nat) : Real) ^ 2) := by
  let q := qStar p Q hQ hCoupling x
  have hqNat : 0 < q := qStar_pos p Q hQ hCoupling x
  have hRqNat : p.R * q < p.N :=
    R_mul_qStar_lt_N p Q hQ hCoupling hCutoff x
  have hq : (0 : Real) < (q : Real) := Nat.cast_pos.mpr hqNat
  have hN : (0 : Real) < (p.N : Real) := Nat.cast_pos.mpr p.N_pos
  have hRq : (p.R : Real) * (q : Real) < (p.N : Real) := by
    exact_mod_cast hRqNat
  rw [div_lt_div_iff₀ (mul_pos hq hN) (sq_pos_of_pos hq)]
  have hmul := mul_lt_mul_of_pos_right hRq hq
  simpa only [one_mul, mul_one, pow_two, mul_assoc, mul_left_comm, mul_comm]
    using hmul

/-- Reflection preserves the denominator and the V1.7.6 localization radius. -/
theorem reflected_localization_index_exists (p : ArcParameters) (Q : Nat)
    (i : ReducedRationalIndex Q) :
    ∃ j : ReducedRationalIndex Q,
      j.1.1 = i.1.1 ∧
      majorArcCenter j = -majorArcCenter i ∧
      localizationRadius p j = localizationRadius p i := by
  have hiFilter := Finset.mem_filter.mp i.2
  have hiProduct := Finset.mem_product.mp hiFilter.1
  have hqIcc := Finset.mem_Icc.mp hiProduct.1
  have ha_lt_q := hiFilter.2.1
  have ha_coprime_q := hiFilter.2.2
  by_cases ha0 : i.1.2 = 0
  · refine ⟨i, rfl, ?_, rfl⟩
    unfold majorArcCenter
    simp [ha0]
  · let j : ReducedRationalIndex Q :=
      ⟨(i.1.1, i.1.1 - i.1.2), by
        unfold reducedRationalPairs
        rw [Finset.mem_filter]
        constructor
        · exact Finset.mem_product.mpr
            ⟨hiProduct.1, Finset.mem_range.mpr (by omega)⟩
        · constructor
          · omega
          · exact (Nat.coprime_self_sub_left
              (Nat.le_of_lt ha_lt_q)).mpr ha_coprime_q⟩
    refine ⟨j, rfl, ?_, rfl⟩
    unfold majorArcCenter
    change
      ((((i.1.1 - i.1.2 : Nat) : Real) / (i.1.1 : Real) : Real) :
          UnitAddCircle) =
        -((((i.1.2 : Nat) : Real) / (i.1.1 : Real) : Real) :
          UnitAddCircle)
    have hq_ne : ((i.1.1 : Nat) : Real) ≠ 0 := by
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (index_denominator_pos i))
    rw [Nat.cast_sub (Nat.le_of_lt ha_lt_q)]
    have hReal :
        ((i.1.1 : Real) - (i.1.2 : Real)) / (i.1.1 : Real) =
          1 - (i.1.2 : Real) / (i.1.1 : Real) := by
      field_simp
    rw [hReal, AddCircle.coe_sub]
    simp

private theorem denominatorAdmissible_neg_of (p : ArcParameters) (Q q : Nat)
    {x : UnitAddCircle} (hx : DenominatorAdmissible p Q x q) :
    DenominatorAdmissible p Q (-x) q := by
  rcases hx with ⟨i, hiq, hiDist⟩
  rcases reflected_localization_index_exists p Q i with
    ⟨j, hjq, hCenter, hRadius⟩
  refine ⟨j, hjq.trans hiq, ?_⟩
  rw [hCenter, hRadius, dist_neg_neg]
  exact hiDist

/-- Admissibility at fixed denominator is invariant under torus negation. -/
theorem denominatorAdmissible_neg_iff (p : ArcParameters) (Q q : Nat)
    (x : UnitAddCircle) :
    DenominatorAdmissible p Q (-x) q ↔ DenominatorAdmissible p Q x q := by
  constructor
  · intro hx
    have h := denominatorAdmissible_neg_of p Q q hx
    simpa using h
  · exact denominatorAdmissible_neg_of p Q q

/-- Minimal admissible denominator is unchanged by torus negation. -/
theorem qStar_neg (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) :
    qStar p Q hQ hCoupling (-x) = qStar p Q hQ hCoupling x := by
  apply Nat.le_antisymm
  · apply qStar_min p Q hQ hCoupling (-x)
    exact (denominatorAdmissible_neg_iff p Q
      (qStar p Q hQ hCoupling x) x).mpr
        (qStar_spec p Q hQ hCoupling x)
  · apply qStar_min p Q hQ hCoupling x
    exact (denominatorAdmissible_neg_iff p Q
      (qStar p Q hQ hCoupling (-x)) x).mp
        (qStar_spec p Q hQ hCoupling (-x))

/-- The low-denominator minor band is negation-invariant. -/
theorem neg_mem_lowMinorBand_iff (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) :
    -x ∈ lowMinorBand p Q hQ hCoupling ↔
      x ∈ lowMinorBand p Q hQ hCoupling := by
  simp only [lowMinorBand, Set.mem_inter_iff, Set.mem_ofPred_eq,
    GoldbachCircleMethodSymmetryV175.neg_mem_minorArcs_iff,
    qStar_neg]

/-- The central-denominator minor band is negation-invariant. -/
theorem neg_mem_centralMinorBand_iff (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) :
    -x ∈ centralMinorBand p Q hQ hCoupling ↔
      x ∈ centralMinorBand p Q hQ hCoupling := by
  simp only [centralMinorBand, Set.mem_inter_iff, Set.mem_ofPred_eq,
    GoldbachCircleMethodSymmetryV175.neg_mem_minorArcs_iff,
    qStar_neg]

/-- The high-denominator minor band is negation-invariant. -/
theorem neg_mem_highMinorBand_iff (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) :
    -x ∈ highMinorBand p Q hQ hCoupling ↔
      x ∈ highMinorBand p Q hQ hCoupling := by
  simp only [highMinorBand, Set.mem_inter_iff, Set.mem_ofPred_eq,
    GoldbachCircleMethodSymmetryV175.neg_mem_minorArcs_iff,
    qStar_neg]

/--
The torus witness has a real lift, shifted by the nearest integer, whose
distance from the selected reduced rational is strictly below `qStar⁻²`.
-/
theorem exists_real_lift_qStar_approximation (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (hCutoff : p.R * Q < p.N) (x : UnitAddCircle) :
    ∃ (alpha : Real) (i : ReducedRationalIndex Q),
      (alpha : UnitAddCircle) = x ∧
      i.1.1 = qStar p Q hQ hCoupling x ∧
      |alpha - ((i.1.2 : Nat) : Real) / ((i.1.1 : Nat) : Real)| <
        1 / (((qStar p Q hQ hCoupling x : Nat) : Real) ^ 2) := by
  obtain ⟨xi, rfl⟩ := QuotientAddGroup.mk_surjective x
  rcases qStar_spec p Q hQ hCoupling (xi : UnitAddCircle) with
    ⟨i, hiq, hiDist⟩
  let beta : Real := ((i.1.2 : Nat) : Real) / ((i.1.1 : Nat) : Real)
  let k : Int := round (xi - beta)
  refine ⟨xi - (k : Real), i, ?_, hiq, ?_⟩
  · rw [AddCircle.coe_sub]
    simp
  · have hDistAsAbs :
        |(xi - beta) - (round (xi - beta) : Real)| ≤
          localizationRadius p i := by
      calc
        |(xi - beta) - (round (xi - beta) : Real)| =
            ‖(((xi - beta) : Real) : UnitAddCircle)‖ := by
              exact UnitAddCircle.norm_eq.symm
        _ = dist (xi : UnitAddCircle) (majorArcCenter i) := by
          unfold majorArcCenter beta
          rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
        _ ≤ localizationRadius p i := hiDist
    have hRadius :
        localizationRadius p i <
          1 / (((qStar p Q hQ hCoupling (xi : UnitAddCircle) : Nat) : Real) ^ 2) := by
      unfold localizationRadius
      rw [hiq]
      exact qStar_radius_lt_inv_sq p Q hQ hCoupling hCutoff
        (xi : UnitAddCircle)
    have hApprox := lt_of_le_of_lt hDistAsAbs hRadius
    change |(xi - (k : Real)) - ((i.1.2 : Nat) : Real) /
      ((i.1.1 : Nat) : Real)| < _
    calc
      |(xi - (k : Real)) - ((i.1.2 : Nat) : Real) /
          ((i.1.1 : Nat) : Real)| =
          |(xi - beta) - (round (xi - beta) : Real)| := by
            congr 1
            simp only [beta, k]
            ring
      _ < _ := hApprox

end GoldbachCircleMethodMinorLocalizationSharpV177
