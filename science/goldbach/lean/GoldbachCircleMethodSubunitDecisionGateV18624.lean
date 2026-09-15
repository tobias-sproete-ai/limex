import GoldbachCircleMethodLogDecayNondecisionWitnessV18623

/-!
# V1.8.624: exact subunit exceptional-count decision gate

V1.8.623 proves that fixed-power logarithmic decay alone does not decide
Goldbach. This module states and proves the exact quantitative threshold which
would decide it for the already frozen cumulative exception carrier: an eventual
strict upper bound below one.

No such analytic bound is supplied here. `proof_status = NO_PROOF`.
-/
set_option autoImplicit false
open Filter
open GoldbachPurePrimeAdequacyV15
open GoldbachCircleMethodFiniteDyadicExceptionCarrierV1876

namespace GoldbachCircleMethodSubunitDecisionGateV18624

/-- The literal strong binary Goldbach target represented by the frozen
`GoldbachAt` predicate. -/
def StrongGoldbach : Prop :=
  ∀ N : ℕ, 4 ≤ N → Even N → GoldbachAt N

/-- A real-valued strict subunit bound on a finite cardinality is exactly
emptiness of the finite exception carrier. -/
theorem globalExceptions_card_lt_one_iff_empty (X : ℕ) :
    ((globalExceptions X).card : ℝ) < 1 ↔ globalExceptions X = ∅ := by
  constructor
  · intro hlt
    have hltNat : (globalExceptions X).card < 1 := by exact_mod_cast hlt
    have hzero : (globalExceptions X).card = 0 := by omega
    exact Finset.card_eq_zero.mp hzero
  · intro hempty
    rw [hempty]
    norm_num

/-- If the actual cumulative Goldbach exception count is eventually strictly
below one, then the frozen strong Goldbach target follows for every even N>=4.
This is a decision bridge, not a proof of its analytic premise. -/
theorem eventual_subunit_global_exception_bound_implies_strongGoldbach
    (hsub : ∀ᶠ X : ℕ in atTop,
      ((globalExceptions X).card : ℝ) < 1) :
    StrongGoldbach := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hsub
  intro N hN4 hEven
  let X := max X₀ N
  have hX₀X : X₀ ≤ X := le_max_left _ _
  have hNX : N ≤ X := le_max_right _ _
  have hempty : globalExceptions X = ∅ :=
    (globalExceptions_card_lt_one_iff_empty X).mp (hX₀ X hX₀X)
  by_contra hNot
  have hmem : N ∈ globalExceptions X :=
    (mem_globalExceptions_iff X N).mpr ⟨hN4, hNX, hEven, hNot⟩
  rw [hempty] at hmem
  simp at hmem

/-- Conversely, the strong target empties every cumulative exception carrier. -/
theorem strongGoldbach_implies_all_globalExceptions_empty
    (hG : StrongGoldbach) (X : ℕ) :
    globalExceptions X = ∅ := by
  ext N
  constructor
  · intro hmem
    obtain ⟨hN4, _hNX, hEven, hNot⟩ :=
      (mem_globalExceptions_iff X N).mp hmem
    exact (hNot (hG N hN4 hEven)).elim
  · simp

/-- The exact decision interface: the strong target is equivalent to emptiness
of every frozen cumulative exception carrier. -/
theorem strongGoldbach_iff_all_globalExceptions_empty :
    StrongGoldbach ↔ ∀ X : ℕ, globalExceptions X = ∅ := by
  constructor
  · exact strongGoldbach_implies_all_globalExceptions_empty
  · intro hEmpty N hN4 hEven
    by_contra hNot
    have hmem : N ∈ globalExceptions N :=
      (mem_globalExceptions_iff N N).mpr ⟨hN4, le_rfl, hEven, hNot⟩
    rw [hEmpty N] at hmem
    simp at hmem

end GoldbachCircleMethodSubunitDecisionGateV18624
