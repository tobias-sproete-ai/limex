import GoldbachCircleMethodMinorLocalizationSharpV177

/-!
# Boolean geometry of the bound qStar denominator, V1.8.5

This module uses exactly the denominator admissibility relation and radius
`R / (q * N)` already fixed in V1.7.6 and sharpened in V1.7.7. It identifies
the points whose least admissible denominator lies in `(L, U]` with a set
difference of two nested denominator covers.

No Fourier estimate, Ramanujan-sum identity, analytic cancellation estimate,
or Goldbach proof is introduced here.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodQStarBooleanGeometryV185

open GoldbachCircleMethodMajorMinorPartitionV172
open GoldbachCircleMethodMinorLocalizationV176

/-- Points admitting a V1.7.6 denominator no larger than `T`. -/
def denominatorCover (p : ArcParameters) (Q T : Nat) : Set UnitAddCircle :=
  {x | ∃ q : Nat, q ≤ T ∧ DenominatorAdmissible p Q x q}

/-- Points whose least V1.7.6 admissible denominator lies in `(L, U]`. -/
noncomputable def qStarBand (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (L U : Nat) : Set UnitAddCircle :=
  {x | L < qStar p Q hQ hCoupling x ∧
    qStar p Q hQ hCoupling x ≤ U}

/-- Denominator covers are monotone in their cutoff. -/
theorem denominatorCover_mono (p : ArcParameters) (Q : Nat)
    {T T' : Nat} (hTT' : T ≤ T') :
    denominatorCover p Q T ⊆ denominatorCover p Q T' := by
  intro x hx
  rcases hx with ⟨q, hqT, hqAdmissible⟩
  exact ⟨q, hqT.trans hTT', hqAdmissible⟩

/--
The bound `qStar` band is exactly the Boolean difference of the upper and
lower denominator covers. The reverse inclusion uses both the admissibility
of `qStar` and its leastness among all admitted denominators.
-/
theorem qStarBand_eq_denominatorCover_sdiff (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    (L U : Nat) :
    qStarBand p Q hQ hCoupling L U =
      denominatorCover p Q U \ denominatorCover p Q L := by
  ext x
  simp only [qStarBand, denominatorCover, Set.mem_ofPred_eq, Set.mem_sdiff]
  constructor
  · rintro ⟨hLower, hUpper⟩
    constructor
    · exact ⟨qStar p Q hQ hCoupling x, hUpper,
        qStar_spec p Q hQ hCoupling x⟩
    · rintro ⟨q, hqLower, hqAdmissible⟩
      have hLeast := qStar_min p Q hQ hCoupling x hqAdmissible
      omega
  · rintro ⟨⟨q, hqUpper, hqAdmissible⟩, hNotLower⟩
    have hStarUpper : qStar p Q hQ hCoupling x ≤ U :=
      (qStar_min p Q hQ hCoupling x hqAdmissible).trans hqUpper
    have hStarNotLower : ¬ qStar p Q hQ hCoupling x ≤ L := by
      intro hStarLower
      apply hNotLower
      exact ⟨qStar p Q hQ hCoupling x, hStarLower,
        qStar_spec p Q hQ hCoupling x⟩
    exact ⟨Nat.lt_of_not_ge hStarNotLower, hStarUpper⟩

/-- If the upper endpoint does not exceed the lower one, the band is empty. -/
theorem qStarBand_eq_empty_of_upper_le_lower (p : ArcParameters) (Q : Nat)
    (hQ : 0 < Q) (hCoupling : p.N ≤ p.R * (Q + 1))
    {L U : Nat} (hUL : U ≤ L) :
    qStarBand p Q hQ hCoupling L U = ∅ := by
  rw [qStarBand_eq_denominatorCover_sdiff]
  exact Set.sdiff_eq_empty.mpr (denominatorCover_mono p Q hUL)

end GoldbachCircleMethodQStarBooleanGeometryV185
