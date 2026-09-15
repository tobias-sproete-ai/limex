import GoldbachCircleMethodSymmetryV175
import Mathlib.NumberTheory.DiophantineApproximation.Basic

set_option autoImplicit false

namespace GoldbachCircleMethodMinorLocalizationV176

open GoldbachCircleMethodMajorMinorPartitionV172

noncomputable def localizationRadius (p : ArcParameters) {Q : Nat}
    (i : ReducedRationalIndex Q) : Real :=
  (p.R : Real) / (((i.1.1 : Nat) : Real) * (p.N : Real))

theorem exists_dirichlet_index (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) :
    ∃ i : ReducedRationalIndex Q,
      dist x (majorArcCenter i) ≤ localizationRadius p i := by
  obtain ⟨xi, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨r, hrApprox, hrDen⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le xi hQ
  let s : Rat := Int.fract r
  have hsNonneg : (0 : Rat) ≤ s := by
    exact Int.fract_nonneg r
  have hsLtOne : s < (1 : Rat) := by
    exact Int.fract_lt_one r
  have hsNumNonneg : 0 ≤ s.num := Rat.num_nonneg.mpr hsNonneg
  have hsNumLtDen : s.num.natAbs < s.den := by
    have hnum : s.num < (s.den : Int) :=
      Rat.num_lt_denom_iff.mpr hsLtOne
    have habs : (s.num.natAbs : Int) = s.num :=
      Int.natAbs_of_nonneg hsNumNonneg
    exact_mod_cast (habs ▸ hnum)
  have hsDenLe : s.den ≤ Q := by
    simpa only [s, Rat.den_intFract] using hrDen
  let i : ReducedRationalIndex Q :=
    ⟨(s.den, s.num.natAbs), by
      unfold reducedRationalPairs
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨s.pos, hsDenLe⟩,
            Finset.mem_range.mpr (hsNumLtDen.trans_le hsDenLe)⟩
      · exact ⟨hsNumLtDen, s.reduced⟩⟩
  refine ⟨i, ?_⟩
  have hCenterReal :
      (((i.1.2 : Nat) : Real) / ((i.1.1 : Nat) : Real)) = (s : Real) := by
    change ((s.num.natAbs : Nat) : Real) / (s.den : Real) = (s : Real)
    rw [show ((s.num.natAbs : Nat) : Real) = (s.num : Int) by
      rw [Nat.cast_natAbs, abs_of_nonneg]
      exact_mod_cast hsNumNonneg]
    exact_mod_cast Rat.num_div_den s
  have hCenterCircle :
      majorArcCenter i = ((r : Real) : UnitAddCircle) := by
    unfold majorArcCenter
    rw [hCenterReal]
    change ((s : Real) : UnitAddCircle) = ((r : Real) : UnitAddCircle)
    simp only [s, Int.fract, Rat.cast_sub, Rat.cast_intCast]
    simp
  rw [hCenterCircle]
  calc
    dist (xi : UnitAddCircle) ((r : Real) : UnitAddCircle) =
        ‖(((xi - (r : Real)) : Real) : UnitAddCircle)‖ := by
          rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
    _ ≤ ‖xi - (r : Real)‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |xi - (r : Real)| := Real.norm_eq_abs _
    _ ≤ 1 / (((Q + 1 : Nat) : Real) * (r.den : Real)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hrApprox
    _ ≤ localizationRadius p i := by
      unfold localizationRadius
      change 1 / (((Q + 1 : Nat) : Real) * (r.den : Real)) ≤
        (p.R : Real) / ((s.den : Real) * (p.N : Real))
      rw [show s.den = r.den by simp [s]]
      have hCouplingReal :
          (p.N : Real) ≤ (p.R : Real) * ((Q + 1 : Nat) : Real) := by
        exact_mod_cast hCoupling
      have hDenPos : (0 : Real) < (r.den : Real) := by positivity
      rw [div_le_div_iff₀ (mul_pos (by positivity) hDenPos)
        (mul_pos hDenPos (Nat.cast_pos.mpr p.N_pos))]
      nlinarith

/-- Denominator `q` supports one concrete approximation at the V1.7.2 radius. -/
def DenominatorAdmissible (p : ArcParameters) (Q : Nat)
    (x : UnitAddCircle) (q : Nat) : Prop :=
  ∃ i : ReducedRationalIndex Q,
    i.1.1 = q ∧ dist x (majorArcCenter i) ≤ localizationRadius p i

theorem exists_admissible_denominator (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) :
    ∃ q : Nat, DenominatorAdmissible p Q x q := by
  rcases exists_dirichlet_index p Q hQ hCoupling x with ⟨i, hi⟩
  exact ⟨i.1.1, i, rfl, hi⟩

/-- The least denominator among all admitted Dirichlet approximants. -/
noncomputable def qStar (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) : Nat :=
  by
    classical
    exact Nat.find (exists_admissible_denominator p Q hQ hCoupling x)

theorem qStar_spec (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) :
    DenominatorAdmissible p Q x (qStar p Q hQ hCoupling x) := by
  classical
  exact Nat.find_spec (exists_admissible_denominator p Q hQ hCoupling x)

theorem qStar_min (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) {q : Nat} (hq : DenominatorAdmissible p Q x q) :
    qStar p Q hQ hCoupling x ≤ q := by
  classical
  exact Nat.find_min' (exists_admissible_denominator p Q hQ hCoupling x) hq

theorem qStar_pos (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) :
    0 < qStar p Q hQ hCoupling x := by
  rcases qStar_spec p Q hQ hCoupling x with ⟨i, hiq, _⟩
  rw [← hiq]
  exact index_denominator_pos i

theorem qStar_le_Q (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) :
    qStar p Q hQ hCoupling x ≤ Q := by
  rcases qStar_spec p Q hQ hCoupling x with ⟨i, hiq, _⟩
  rw [← hiq]
  have hiFilter := Finset.mem_filter.mp i.2
  have hiProduct := Finset.mem_product.mp hiFilter.1
  exact (Finset.mem_Icc.mp hiProduct.1).2

theorem qStar_gt_R_of_mem_minor (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    {x : UnitAddCircle} (hx : x ∈ minorArcs p) :
    p.R < qStar p Q hQ hCoupling x := by
  rcases qStar_spec p Q hQ hCoupling x with ⟨i, hiq, hiDist⟩
  by_contra hnot
  have hqLeR : i.1.1 ≤ p.R := by
    rw [hiq]
    exact Nat.le_of_not_gt hnot
  have hiFilter := Finset.mem_filter.mp i.2
  have hiProduct := Finset.mem_product.mp hiFilter.1
  have haLtQ := hiFilter.2.1
  have haCoprimeQ := hiFilter.2.2
  let j : ReducedRationalIndex p.R :=
    ⟨i.1, by
      unfold reducedRationalPairs
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨index_denominator_pos i, hqLeR⟩,
            Finset.mem_range.mpr (haLtQ.trans_le hqLeR)⟩
      · exact ⟨haLtQ, haCoprimeQ⟩⟩
  have hxMajor : x ∈ majorArcs p := by
    simp only [majorArcs, Set.mem_iUnion]
    refine ⟨j, ?_⟩
    rw [Metric.mem_closedBall]
    exact hiDist
  exact hx hxMajor

theorem denominatorAdmissible_measurable (p : ArcParameters) (Q q : Nat) :
    Measurable (fun x : UnitAddCircle => DenominatorAdmissible p Q x q) := by
  unfold DenominatorAdmissible
  apply Measurable.exists
  intro i
  apply Measurable.and measurable_const
  rw [← measurableSet_setOfPred]
  exact measurableSet_le
    (continuous_id.dist continuous_const).measurable measurable_const

theorem qStar_eq_iff (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (x : UnitAddCircle) (q : Nat) :
    qStar p Q hQ hCoupling x = q ↔
      DenominatorAdmissible p Q x q ∧
        ∀ m < q, ¬ DenominatorAdmissible p Q x m := by
  classical
  unfold qStar
  exact Nat.find_eq_iff (exists_admissible_denominator p Q hQ hCoupling x)

theorem qStar_measurable (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    Measurable (qStar p Q hQ hCoupling) := by
  apply measurable_to_countable'
  intro q
  have hset :
      qStar p Q hQ hCoupling ⁻¹' ({q} : Set Nat) =
        {x | DenominatorAdmissible p Q x q ∧
          ∀ m < q, ¬ DenominatorAdmissible p Q x m} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact qStar_eq_iff p Q hQ hCoupling x q
  rw [hset, measurableSet_setOfPred]
  exact (denominatorAdmissible_measurable p Q q).and
    (Measurable.forall fun m =>
      measurable_const.imp (denominatorAdmissible_measurable p Q m).not)

noncomputable def lowMinorBand (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    Set UnitAddCircle :=
  minorArcs p ∩ {x | (qStar p Q hQ hCoupling x) ^ 5 ≤ p.N ^ 2}

noncomputable def centralMinorBand (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    Set UnitAddCircle :=
  minorArcs p ∩ {x | p.N ^ 2 < (qStar p Q hQ hCoupling x) ^ 5 ∧
    (qStar p Q hQ hCoupling x) ^ 5 ≤ p.N ^ 3}

noncomputable def highMinorBand (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    Set UnitAddCircle :=
  minorArcs p ∩ {x | p.N ^ 3 < (qStar p Q hQ hCoupling x) ^ 5}

theorem lowMinorBand_measurable (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    MeasurableSet (lowMinorBand p Q hQ hCoupling) := by
  exact (minorArcs_measurable p).inter
    (measurableSet_le ((qStar_measurable p Q hQ hCoupling).pow_const 5)
      measurable_const)

theorem centralMinorBand_measurable (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    MeasurableSet (centralMinorBand p Q hQ hCoupling) := by
  have hpow := (qStar_measurable p Q hQ hCoupling).pow_const 5
  exact (minorArcs_measurable p).inter
    ((measurableSet_lt measurable_const hpow).inter
      (measurableSet_le hpow measurable_const))

theorem highMinorBand_measurable (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    MeasurableSet (highMinorBand p Q hQ hCoupling) := by
  exact (minorArcs_measurable p).inter
    (measurableSet_lt measurable_const
      ((qStar_measurable p Q hQ hCoupling).pow_const 5))

theorem low_central_disjoint (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    Disjoint (lowMinorBand p Q hQ hCoupling)
      (centralMinorBand p Q hQ hCoupling) := by
  rw [Set.disjoint_left]
  intro x hxLow hxCentral
  exact (not_lt_of_ge hxLow.2) hxCentral.2.1

theorem low_high_disjoint (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    Disjoint (lowMinorBand p Q hQ hCoupling)
      (highMinorBand p Q hQ hCoupling) := by
  rw [Set.disjoint_left]
  intro x hxLow hxHigh
  have hN23 : p.N ^ 2 ≤ p.N ^ 3 := by
    nlinarith [p.N_pos]
  exact (not_lt_of_ge (hxLow.2.trans hN23)) hxHigh.2

theorem central_high_disjoint (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    Disjoint (centralMinorBand p Q hQ hCoupling)
      (highMinorBand p Q hQ hCoupling) := by
  rw [Set.disjoint_left]
  intro x hxCentral hxHigh
  exact (not_lt_of_ge hxCentral.2.2) hxHigh.2

theorem minorBands_union (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1)) :
    lowMinorBand p Q hQ hCoupling ∪
      centralMinorBand p Q hQ hCoupling ∪
        highMinorBand p Q hQ hCoupling = minorArcs p := by
  ext x
  simp only [lowMinorBand, centralMinorBand, highMinorBand,
    Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
  · intro hx
    by_cases hLow : (qStar p Q hQ hCoupling x) ^ 5 ≤ p.N ^ 2
    · exact Or.inl (Or.inl ⟨hx, hLow⟩)
    · have hN2lt : p.N ^ 2 < (qStar p Q hQ hCoupling x) ^ 5 :=
        Nat.lt_of_not_ge hLow
      by_cases hCentral : (qStar p Q hQ hCoupling x) ^ 5 ≤ p.N ^ 3
      · exact Or.inl (Or.inr ⟨hx, hN2lt, hCentral⟩)
      · exact Or.inr ⟨hx, Nat.lt_of_not_ge hCentral⟩

end GoldbachCircleMethodMinorLocalizationV176
