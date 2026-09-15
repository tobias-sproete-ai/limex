import GoldbachCircleMethodDisjointPrimeFactorCompositionV18171

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodBadPrimeResidueCountV18163
open GoldbachCircleMethodBadPrimeActualWeightV18164
open GoldbachCircleMethodLocalEulerRadicalBoundsV18149
open GoldbachCircleMethodRadicalArithmeticClassV18159
open GoldbachCircleMethodHenriotArithmeticGrowthClassV18170
namespace GoldbachCircleMethodCorrectedLocalFactorBindingV18172

/-- The three nonzero Boolean valuation patterns for two linear forms.
The all-zero pattern is intentionally absent: it is represented by the outer
constant `1` in `correctedLocalFactor`. -/
def nonzeroValuationPairs : Finset (Bool × Bool) :=
  {(true, false), (false, true), (true, true)}

/-- Exponent one means exact first-power divisibility. Exponent zero imposes
only the unitary divisor `1`, hence no nondivisibility condition. -/
def valuationRequirement (p : ℕ) (active : Bool) (z : ℤ) : Prop :=
  if active then exactFirstPower p z else True

/-- The corrected two-form local condition (Erratum property P) for
`L₁(n)=n`, `L₂(n)=m-n`, expressed over `ℤ`.

When just one valuation is active, the inactive form must not be divisible by
`p`. This extra clause belongs to property P; it is not the meaning of the
unitary relation `1 ∥ Lᵢ(n)`. -/
def erratumPairCondition (p m : ℕ) (ν : Bool × Bool) (n : ℕ) : Prop :=
  valuationRequirement p ν.1 (n : ℤ) ∧
  valuationRequirement p ν.2 ((m : ℤ) - n) ∧
  (ν = (false, true) → ¬(p : ℤ) ∣ (n : ℤ)) ∧
  (ν = (true, false) → ¬(p : ℤ) ∣ ((m : ℤ) - n))

noncomputable def correctedValuationResidues
    (p m : ℕ) (ν : Bool × Bool) : Finset ℕ :=
  (Finset.range (p*p)).filter (erratumPairCondition p m ν)

def valuationDivisor (p : ℕ) (active : Bool) : ℕ :=
  if active then p else 1

noncomputable def correctedTupleContribution
    (R ξ η : ℝ) (p m : ℕ) (ν : Bool × Bool) : ℝ :=
  pairWeight R ξ η (valuationDivisor p ν.1) (valuationDivisor p ν.2) *
    (((correctedValuationResidues p m ν).card : ℝ) / (p : ℝ)^2)

noncomputable def correctedPositiveValuationSum
    (R ξ η : ℝ) (p m : ℕ) : ℝ :=
  ∑ ν ∈ nonzeroValuationPairs, correctedTupleContribution R ξ η p m ν

noncomputable def correctedLocalFactor
    (R ξ η : ℝ) (p m : ℕ) : ℝ :=
  1 + correctedPositiveValuationSum R ξ η p m

/-- Exponent zero carries only the unitary divisor-one requirement. -/
theorem zero_valuation_requirement (p : ℕ) (z : ℤ) :
    valuationRequirement p false z := by
  simp [valuationRequirement]

/-- The all-zero valuation pattern satisfies no hidden nondivisibility test. -/
theorem all_zero_condition (p m n : ℕ) :
    erratumPairCondition p m (false, false) n := by
  simp [erratumPairCondition, valuationRequirement]

/-- The all-zero valuation pattern is not part of the primed local sum. -/
theorem all_zero_excluded : (false, false) ∉ nonzeroValuationPairs := by
  simp [nonzeroValuationPairs]

/-- The finite source weight is normalized at the all-zero divisor tuple. -/
theorem pairWeight_one_one (R ξ η : ℝ) : pairWeight R ξ η 1 1 = 1 := by
  simp [pairWeight, divisorRadicalWeight, radicalEnvelope]

/-- If `p ∣ m`, the `(1,0)` valuation pattern is excluded by property P. -/
theorem mixed_left_carrier_empty {p m : ℕ} (hm : p ∣ m) :
    correctedValuationResidues p m (true, false) = ∅ := by
  ext n
  constructor
  · intro hn
    have hpair := (Finset.mem_filter.mp hn).2
    have hcore : exactFirstPower p (n : ℤ) ∧
        ¬(p : ℤ) ∣ ((m : ℤ) - n) := by
      simpa [erratumPairCondition, valuationRequirement] using hpair
    have hmz : (p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hm
    exact (hcore.2
      ((cross_divisibility p (m : ℤ) (n : ℤ) hmz).mp hcore.1.1)).elim
  · simp

/-- If `p ∣ m`, the `(0,1)` valuation pattern is excluded by property P. -/
theorem mixed_right_carrier_empty {p m : ℕ} (hm : p ∣ m) :
    correctedValuationResidues p m (false, true) = ∅ := by
  ext n
  constructor
  · intro hn
    have hpair := (Finset.mem_filter.mp hn).2
    have hcore : exactFirstPower p ((m : ℤ) - n) ∧
        ¬(p : ℤ) ∣ (n : ℤ) := by
      simpa [erratumPairCondition, valuationRequirement] using hpair
    have hmz : (p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hm
    exact (hcore.2
      ((cross_divisibility p (m : ℤ) (n : ℤ) hmz).mpr hcore.1.1)).elim
  · simp

/-- The surviving `(1,1)` carrier is exactly the already counted V164
bad-prime residue carrier. -/
theorem joint_carrier_eq (p m : ℕ) :
    correctedValuationResidues p m (true, true) = actualBadPrimeResidues p m := by
  ext n
  simp [correctedValuationResidues, actualBadPrimeResidues,
    erratumPairCondition, valuationRequirement]

theorem mixed_left_contribution_eq_zero (R ξ η : ℝ) {p m : ℕ} (hm : p ∣ m) :
    correctedTupleContribution R ξ η p m (true, false) = 0 := by
  rw [correctedTupleContribution, mixed_left_carrier_empty hm]
  simp

theorem mixed_right_contribution_eq_zero (R ξ η : ℝ) {p m : ℕ} (hm : p ∣ m) :
    correctedTupleContribution R ξ η p m (false, true) = 0 := by
  rw [correctedTupleContribution, mixed_right_carrier_empty hm]
  simp

theorem joint_contribution_eq (R ξ η : ℝ) (p m : ℕ) :
    correctedTupleContribution R ξ η p m (true, true) =
      pairWeight R ξ η p p *
        (((actualBadPrimeResidues p m).card : ℝ) / (p : ℝ)^2) := by
  rw [correctedTupleContribution, joint_carrier_eq]
  rfl

/-- For a prime divisor of `m`, the corrected nonzero valuation sum has only
the genuine `(1,1)` residue contribution. -/
theorem correctedPositiveValuationSum_eq_joint
    (R ξ η : ℝ) {p m : ℕ} (hm : p ∣ m) :
    correctedPositiveValuationSum R ξ η p m =
      pairWeight R ξ η p p *
        (((actualBadPrimeResidues p m).card : ℝ) / (p : ℝ)^2) := by
  have h10 := mixed_left_contribution_eq_zero R ξ η hm
  have h01 := mixed_right_contribution_eq_zero R ξ η hm
  have h11 := joint_contribution_eq R ξ η p m
  simp [correctedPositiveValuationSum, nonzeroValuationPairs, h10, h01, h11]

/-- Exact corrected local-factor binding. The outer `1` is the all-zero tuple;
the primed nonzero valuation sum supplies exactly V164's bad-prime term. -/
theorem correctedLocalFactor_eq_badPrimeFactor
    (R ξ η : ℝ) {p m : ℕ} (hm : p ∣ m) :
    correctedLocalFactor R ξ η p m = badPrimeFactor R ξ η p m := by
  rw [correctedLocalFactor, correctedPositiveValuationSum_eq_joint R ξ η hm]
  rfl

end GoldbachCircleMethodCorrectedLocalFactorBindingV18172
