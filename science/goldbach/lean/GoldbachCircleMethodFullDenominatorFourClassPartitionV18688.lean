import GoldbachCircleMethodOddOddFullDenominatorNormalFormV18676
import GoldbachCircleMethodOddDoubleSignedRealBridgeV18682
import GoldbachCircleMethodOddOddSmallCoreLargePerturbationV18670

/-!
# V1.8.688: exact four-class partition of the full denominator carrier

This append-only module partitions every `d : Denominator R` into exactly one
of four aggregate classes:

1. `d <= 2`;
2. an odd base `q > 2` with `2*q <= R`, together with its unique doubled
   denominator `2*q`;
3. a residual denominator divisible by four;
4. an odd residual `q > 2` whose double lies beyond `R`.

The paired class is represented internally by its two disjoint atomic sides,
but is exposed as one aggregate.  The resulting finite-sum identity is lifted
to the exact V1.8.676 project coefficient with the outer subtraction retained.
There is no factor `2`: each odd base and each doubled denominator occurs once.

No denominator budget, cross-term estimate, one-sided moment estimate, V1.8.669
target inhabitation, exceptional-set estimate, or Goldbach conclusion is made.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

open GoldbachCircleMethodOriginalMaskModelBindingV1859
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodOddOddExactSignedBudgetV18669
open GoldbachCircleMethodOddOddSmallCoreLargePerturbationV18670
open GoldbachCircleMethodOddOddFullDenominatorNormalFormV18676
open GoldbachCircleMethodOddDoubleSignedRealBridgeV18682

namespace GoldbachCircleMethodFullDenominatorFourClassPartitionV18688

/-- Five atomic labels; `pairedOddBase` and `pairedDouble` form the single
paired aggregate class in the four-class theorem below. -/
inductive DenominatorAtom
  | small
  | pairedOddBase
  | pairedDouble
  | fourDivisibleResidual
  | unpairedOddResidual
  deriving DecidableEq

/-- A total deterministic classifier for the bounded denominator subtype. -/
def denominatorAtom {R : Nat} (d : Denominator R) : DenominatorAtom :=
  if d.val <= 2 then .small
  else if Odd d.val then
    if 2 * d.val <= R then .pairedOddBase else .unpairedOddResidual
  else if 4 ∣ d.val then .fourDivisibleResidual else .pairedDouble

def smallDenominatorClass (R : Nat) : Finset (Denominator R) :=
  Finset.univ.filter (fun d => denominatorAtom d = .small)

def pairedOddBaseClass (R : Nat) : Finset (Denominator R) :=
  Finset.univ.filter (fun d => denominatorAtom d = .pairedOddBase)

def pairedDoubleClass (R : Nat) : Finset (Denominator R) :=
  Finset.univ.filter (fun d => denominatorAtom d = .pairedDouble)

/-- The second aggregate class: every selected odd base and its double. -/
def pairedOddDoubleClass (R : Nat) : Finset (Denominator R) :=
  pairedOddBaseClass R ∪ pairedDoubleClass R

def fourDivisibleResidualClass (R : Nat) : Finset (Denominator R) :=
  Finset.univ.filter (fun d => denominatorAtom d = .fourDivisibleResidual)

def unpairedOddResidualClass (R : Nat) : Finset (Denominator R) :=
  Finset.univ.filter (fun d => denominatorAtom d = .unpairedOddResidual)

theorem mem_smallDenominatorClass_iff {R : Nat} {d : Denominator R} :
    d ∈ smallDenominatorClass R ↔ d.val <= 2 := by
  rw [smallDenominatorClass, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  unfold denominatorAtom
  split <;> rename_i hsmall
  · simp [hsmall]
  · split <;> rename_i hodd
    · split <;> simp_all
    · split <;> simp_all

theorem mem_pairedOddBaseClass_iff {R : Nat} {d : Denominator R} :
    d ∈ pairedOddBaseClass R ↔
      2 < d.val ∧ Odd d.val ∧ 2 * d.val <= R := by
  rw [pairedOddBaseClass, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  unfold denominatorAtom
  split <;> rename_i hsmall
  · simp [hsmall]
  · split <;> rename_i hodd
    · split <;> simp_all
    · split <;> simp_all

theorem mem_pairedDoubleClass_iff {R : Nat} {d : Denominator R} :
    d ∈ pairedDoubleClass R ↔
      2 < d.val ∧ ¬ Odd d.val ∧ ¬ 4 ∣ d.val := by
  rw [pairedDoubleClass, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  unfold denominatorAtom
  split <;> rename_i hsmall
  · simp [hsmall]
  · split <;> rename_i hodd
    · split <;> simp_all
    · split <;> simp_all

/-- Selected odd bases, carrying all three literal range hypotheses. -/
abbrev PairedOddBase (R : Nat) :=
  {q : Denominator R // q ∈ pairedOddBaseClass R}

/-- The bounded doubled denominator attached to a selected odd base. -/
def pairedDoubleDenominator {R : Nat} (q : PairedOddBase R) : Denominator R :=
  ⟨2 * q.val.val, Finset.mem_Icc.mpr ⟨by
      have hq := (mem_pairedOddBaseClass_iff.mp q.property).1
      omega,
    (mem_pairedOddBaseClass_iff.mp q.property).2.2⟩⟩

@[simp] theorem pairedDoubleDenominator_val {R : Nat} (q : PairedOddBase R) :
    (pairedDoubleDenominator q).val = 2 * q.val.val := rfl

theorem pairedDoubleDenominator_injective {R : Nat} :
    Function.Injective (pairedDoubleDenominator (R := R)) := by
  intro q r h
  apply Subtype.ext
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  simp only [pairedDoubleDenominator_val] at hv
  omega

/-- The doubled image really lies in the classifier's doubled atomic side. -/
theorem pairedDoubleDenominator_mem {R : Nat} (q : PairedOddBase R) :
    pairedDoubleDenominator q ∈ pairedDoubleClass R := by
  rcases mem_pairedOddBaseClass_iff.mp q.property with ⟨hqLarge, hqOdd, hqBound⟩
  rw [mem_pairedDoubleClass_iff]
  refine ⟨by simp only [pairedDoubleDenominator_val]; omega, ?_, ?_⟩
  · rintro ⟨j, hj⟩
    obtain ⟨k, hk⟩ := hqOdd
    simp only [pairedDoubleDenominator_val] at hj
    omega
  · rintro ⟨j, hj⟩
    obtain ⟨k, hk⟩ := hqOdd
    simp only [pairedDoubleDenominator_val] at hj
    omega

/-- Every classifier-level doubled denominator has a unique selected odd
base.  This is the non-cosmetic bounded `q <-> 2*q` bridge. -/
theorem pairedDoubleClass_eq_image (R : Nat) :
    pairedDoubleClass R =
      Finset.univ.image (pairedDoubleDenominator (R := R)) := by
  ext d
  constructor
  · intro hd
    rcases mem_pairedDoubleClass_iff.mp hd with ⟨hdLarge, hdNotOdd, hdNotFour⟩
    have hdEven : Even d.val := Nat.not_odd_iff_even.mp hdNotOdd
    obtain ⟨q, hq⟩ := hdEven
    have hqLarge : 2 < q := by
      by_contra hqNotLarge
      have hqSmall : q <= 2 := by omega
      have hqEq : q = 2 := by omega
      apply hdNotFour
      refine ⟨1, ?_⟩
      omega
    have hqOdd : Odd q := by
      by_contra hqNotOdd
      have hqEven : Even q := Nat.not_odd_iff_even.mp hqNotOdd
      obtain ⟨j, hj⟩ := hqEven
      apply hdNotFour
      refine ⟨j, ?_⟩
      omega
    have hqUpper : 2 * q <= R := by
      have hdUpper := (Finset.mem_Icc.mp d.property).2
      omega
    let qD : Denominator R :=
      ⟨q, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
    have hqDmem : qD ∈ pairedOddBaseClass R := by
      rw [mem_pairedOddBaseClass_iff]
      exact ⟨hqLarge, hqOdd, hqUpper⟩
    let qb : PairedOddBase R := ⟨qD, hqDmem⟩
    refine Finset.mem_image.mpr ⟨qb, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    simp only [pairedDoubleDenominator_val, qb, qD]
    omega
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨q, _hq, rfl⟩
    exact pairedDoubleDenominator_mem q

theorem mem_fourDivisibleResidualClass_iff {R : Nat} {d : Denominator R} :
    d ∈ fourDivisibleResidualClass R ↔ 2 < d.val ∧ 4 ∣ d.val := by
  rw [fourDivisibleResidualClass, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  have hdOne : 1 <= d.val := (Finset.mem_Icc.mp d.property).1
  unfold denominatorAtom
  split <;> rename_i hsmall
  · constructor
    · intro h
      contradiction
    · rintro ⟨hlarge, _hfour⟩
      omega
  · split <;> rename_i hodd
    · split <;> rename_i hpair
      · constructor
        · intro h
          contradiction
        · rintro ⟨_hlarge, hfour⟩
          obtain ⟨j, hj⟩ := hodd
          obtain ⟨k, hk⟩ := hfour
          omega
      · constructor
        · intro h
          contradiction
        · rintro ⟨_hlarge, hfour⟩
          obtain ⟨j, hj⟩ := hodd
          obtain ⟨k, hk⟩ := hfour
          omega
    · split <;> simp_all

/-- The classifier's small class is exactly the pre-existing `q <= 2`
carrier, not a replacement notion. -/
theorem smallDenominatorClass_eq_filter_le_two (R : Nat) :
    smallDenominatorClass R =
      Finset.univ.filter (fun d : Denominator R => d.val <= 2) := by
  ext d
  rw [mem_smallDenominatorClass_iff]
  simp

theorem mem_unpairedOddResidualClass_iff {R : Nat} {d : Denominator R} :
    d ∈ unpairedOddResidualClass R ↔
      2 < d.val ∧ Odd d.val ∧ R < 2 * d.val := by
  rw [unpairedOddResidualClass, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  unfold denominatorAtom
  split <;> rename_i hsmall
  · simp [hsmall]
  · split <;> rename_i hodd
    · split <;> simp_all
    · split <;> simp_all

/-- The four aggregate classes exhaust the bounded denominator carrier. -/
theorem denominator_four_class_cover (R : Nat) :
    smallDenominatorClass R ∪ pairedOddDoubleClass R ∪
      fourDivisibleResidualClass R ∪ unpairedOddResidualClass R = Finset.univ := by
  ext d
  cases h : denominatorAtom d <;>
    simp [smallDenominatorClass, pairedOddDoubleClass, pairedOddBaseClass,
      pairedDoubleClass, fourDivisibleResidualClass, unpairedOddResidualClass, h]

/-- Distinct atomic labels induce disjoint carriers. -/
theorem denominatorAtomClass_disjoint {R : Nat} {a b : DenominatorAtom}
    (hab : a ≠ b) :
    Disjoint
      (Finset.univ.filter (fun d : Denominator R => denominatorAtom d = a))
      (Finset.univ.filter (fun d : Denominator R => denominatorAtom d = b)) := by
  rw [Finset.disjoint_left]
  intro d hda hdb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hda hdb
  exact hab (hda.symm.trans hdb)

theorem small_disjoint_paired {R : Nat} :
    Disjoint (smallDenominatorClass R) (pairedOddDoubleClass R) := by
  unfold smallDenominatorClass pairedOddDoubleClass pairedOddBaseClass pairedDoubleClass
  rw [Finset.disjoint_union_right]
  exact ⟨denominatorAtomClass_disjoint (by decide),
    denominatorAtomClass_disjoint (by decide)⟩

theorem pairedOddBase_disjoint_pairedDouble {R : Nat} :
    Disjoint (pairedOddBaseClass R) (pairedDoubleClass R) := by
  exact denominatorAtomClass_disjoint (by decide)

theorem small_disjoint_four {R : Nat} :
    Disjoint (smallDenominatorClass R) (fourDivisibleResidualClass R) := by
  exact denominatorAtomClass_disjoint (by decide)

theorem small_disjoint_unpaired {R : Nat} :
    Disjoint (smallDenominatorClass R) (unpairedOddResidualClass R) := by
  exact denominatorAtomClass_disjoint (by decide)

theorem paired_disjoint_four {R : Nat} :
    Disjoint (pairedOddDoubleClass R) (fourDivisibleResidualClass R) := by
  rw [Finset.disjoint_left]
  intro d hpaired hfour
  rcases Finset.mem_union.mp hpaired with hbase | hdouble
  · exact (Finset.disjoint_left.mp (denominatorAtomClass_disjoint
      (R := R) (a := .pairedOddBase) (b := .fourDivisibleResidual) (by decide)))
      hbase hfour
  · exact (Finset.disjoint_left.mp (denominatorAtomClass_disjoint
      (R := R) (a := .pairedDouble) (b := .fourDivisibleResidual) (by decide)))
      hdouble hfour

theorem paired_disjoint_unpaired {R : Nat} :
    Disjoint (pairedOddDoubleClass R) (unpairedOddResidualClass R) := by
  rw [Finset.disjoint_left]
  intro d hpaired hunpaired
  rcases Finset.mem_union.mp hpaired with hbase | hdouble
  · exact (Finset.disjoint_left.mp (denominatorAtomClass_disjoint
      (R := R) (a := .pairedOddBase) (b := .unpairedOddResidual) (by decide)))
      hbase hunpaired
  · exact (Finset.disjoint_left.mp (denominatorAtomClass_disjoint
      (R := R) (a := .pairedDouble) (b := .unpairedOddResidual) (by decide)))
      hdouble hunpaired

theorem four_disjoint_unpaired {R : Nat} :
    Disjoint (fourDivisibleResidualClass R) (unpairedOddResidualClass R) := by
  exact denominatorAtomClass_disjoint (by decide)

theorem pairedUnionFour_disjoint_unpaired {R : Nat} :
    Disjoint
      (pairedOddDoubleClass R ∪ fourDivisibleResidualClass R)
      (unpairedOddResidualClass R) := by
  rw [Finset.disjoint_left]
  intro d hleft hu
  rcases Finset.mem_union.mp hleft with hp | hf
  · exact (Finset.disjoint_left.mp (paired_disjoint_unpaired (R := R))) hp hu
  · exact (Finset.disjoint_left.mp (four_disjoint_unpaired (R := R))) hf hu

/-- The pre-existing `q > 2` carrier is exactly the union of the paired
aggregate and the two residual classes. -/
theorem largeDenominatorClass_eq_three_residual_classes (R : Nat) :
    Finset.univ.filter (fun d : Denominator R => 2 < d.val) =
      (pairedOddDoubleClass R ∪ fourDivisibleResidualClass R) ∪
        unpairedOddResidualClass R := by
  ext d
  constructor
  · intro hd
    have hdLarge : 2 < d.val := by simpa using hd
    have hdNotSmall : d ∉ smallDenominatorClass R := by
      rw [mem_smallDenominatorClass_iff]
      omega
    have hcover : d ∈
        (smallDenominatorClass R ∪ pairedOddDoubleClass R ∪
          fourDivisibleResidualClass R) ∪ unpairedOddResidualClass R := by
      rw [denominator_four_class_cover]
      simp
    rcases Finset.mem_union.mp hcover with hspf | hu
    · rcases Finset.mem_union.mp hspf with hsp | hf
      · rcases Finset.mem_union.mp hsp with hs | hp
        · exact False.elim (hdNotSmall hs)
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hp)))
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hf)))
    · exact Finset.mem_union.mpr (Or.inr hu)
  · intro hd
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ d, ?_⟩
    rcases Finset.mem_union.mp hd with hpf | hu
    · rcases Finset.mem_union.mp hpf with hp | hf
      · rcases Finset.mem_union.mp hp with hbase | hdouble
        · exact (mem_pairedOddBaseClass_iff.mp hbase).1
        · exact (mem_pairedDoubleClass_iff.mp hdouble).1
      · exact (mem_fourDivisibleResidualClass_iff.mp hf).1
    · exact (mem_unpairedOddResidualClass_iff.mp hu).1

/-- The five atomic carriers, grouped into four classes, give an exact finite
sum partition for every additive target. -/
theorem sum_denominator_four_class
    {R : Nat} {A : Type*} [AddCommMonoid A]
    (f : Denominator R -> A) :
    (∑ d : Denominator R, f d) =
      (∑ d ∈ smallDenominatorClass R, f d) +
      (∑ d ∈ pairedOddDoubleClass R, f d) +
      (∑ d ∈ fourDivisibleResidualClass R, f d) +
      (∑ d ∈ unpairedOddResidualClass R, f d) := by
  let s := smallDenominatorClass R
  let p := pairedOddDoubleClass R
  let f4 := fourDivisibleResidualClass R
  let u := unpairedOddResidualClass R
  have hsp : Disjoint s p := small_disjoint_paired (R := R)
  have hspf : Disjoint (s ∪ p) f4 := by
    rw [Finset.disjoint_left]
    intro d hspmem hf
    rcases Finset.mem_union.mp hspmem with hs | hp
    · exact (Finset.disjoint_left.mp (small_disjoint_four (R := R))) hs hf
    · exact (Finset.disjoint_left.mp (paired_disjoint_four (R := R))) hp hf
  have hallu : Disjoint ((s ∪ p) ∪ f4) u := by
    rw [Finset.disjoint_left]
    intro d hleft hu
    rcases Finset.mem_union.mp hleft with hspmem | hf
    · rcases Finset.mem_union.mp hspmem with hs | hp
      · exact (Finset.disjoint_left.mp (small_disjoint_unpaired (R := R))) hs hu
      · exact (Finset.disjoint_left.mp (paired_disjoint_unpaired (R := R))) hp hu
    · exact (Finset.disjoint_left.mp (four_disjoint_unpaired (R := R))) hf hu
  calc
    (∑ d : Denominator R, f d) = ∑ d ∈ ((s ∪ p) ∪ f4) ∪ u, f d := by
      rw [show ((s ∪ p) ∪ f4) ∪ u = Finset.univ by
        simpa [s, p, f4, u, Finset.union_assoc] using denominator_four_class_cover R]
    _ = (∑ d ∈ (s ∪ p) ∪ f4, f d) + ∑ d ∈ u, f d :=
      Finset.sum_union hallu
    _ = ((∑ d ∈ s ∪ p, f d) + ∑ d ∈ f4, f d) + ∑ d ∈ u, f d := by
      rw [Finset.sum_union hspf]
    _ = (((∑ d ∈ s, f d) + (∑ d ∈ p, f d)) + (∑ d ∈ f4, f d)) +
        (∑ d ∈ u, f d) := by rw [Finset.sum_union hsp]
    _ = (∑ d ∈ smallDenominatorClass R, f d) +
        (∑ d ∈ pairedOddDoubleClass R, f d) +
        (∑ d ∈ fourDivisibleResidualClass R, f d) +
        (∑ d ∈ unpairedOddResidualClass R, f d) := by rfl

/-- Exact reindex of the paired aggregate by its selected odd bases.  Both
`q` and `2*q` occur once; no multiplicity factor is introduced. -/
theorem sum_pairedOddDoubleClass_eq_selected_pairs
    {R : Nat} {A : Type*} [AddCommMonoid A]
    (f : Denominator R -> A) :
    (∑ d ∈ pairedOddDoubleClass R, f d) =
      ∑ q : PairedOddBase R, (f q.val + f (pairedDoubleDenominator q)) := by
  rw [pairedOddDoubleClass,
    Finset.sum_union (pairedOddBase_disjoint_pairedDouble (R := R))]
  have hbase :
      (∑ d ∈ pairedOddBaseClass R, f d) =
        ∑ q : PairedOddBase R, f q.val := by
    conv_lhs => rw [← Finset.sum_attach, Finset.attach_eq_univ]
  have hdouble :
      (∑ d ∈ pairedDoubleClass R, f d) =
        ∑ q : PairedOddBase R, f (pairedDoubleDenominator q) := by
    rw [pairedDoubleClass_eq_image]
    rw [Finset.sum_image]
    intro q _hq r _hr hqr
    exact pairedDoubleDenominator_injective hqr
  rw [hbase, hdouble, ← Finset.sum_add_distrib]

/-- Project contribution of the complete selected odd/double aggregate.  Its
minus sign is the literal V1.8.676 outer subtraction. -/
noncomputable def projectPairedOddDoubleAggregate (M N : Nat) : Real :=
  -∑ t ∈ oddOddOffDiagonalSumCarrier M N,
    oddOddPairFiberMass M t *
      (∑ d ∈ pairedOddDoubleClass (oddProjectRadius M),
        explicitDenominatorSincTerm M (oddProjectWidth M) (oddProjectRadius M)
          ((N : Int) - (t : Int)) d).re

/-- Project contribution of the residual denominators divisible by four. -/
noncomputable def projectFourDivisibleResidual (M N : Nat) : Real :=
  -∑ t ∈ oddOddOffDiagonalSumCarrier M N,
    oddOddPairFiberMass M t *
      (∑ d ∈ fourDivisibleResidualClass (oddProjectRadius M),
        explicitDenominatorSincTerm M (oddProjectWidth M) (oddProjectRadius M)
          ((N : Int) - (t : Int)) d).re

/-- Project contribution of odd residual denominators whose double is outside
the bounded carrier. -/
noncomputable def projectUnpairedOddResidual (M N : Nat) : Real :=
  -∑ t ∈ oddOddOffDiagonalSumCarrier M N,
    oddOddPairFiberMass M t *
      (∑ d ∈ unpairedOddResidualClass (oddProjectRadius M),
        explicitDenominatorSincTerm M (oddProjectWidth M) (oddProjectRadius M)
          ((N : Int) - (t : Int)) d).re

/-- The carrier-defined paired aggregate is exactly the sum of the selected
V1.8.682 signed contributions.  The reindexing contributes no factor `2`. -/
theorem projectPairedOddDoubleAggregate_eq_sum_selectedContributions
    (M N : Nat) :
    projectPairedOddDoubleAggregate M N =
      ∑ q : PairedOddBase (oddProjectRadius M),
        projectOddDoubleSignedContribution M N q.val
          (pairedDoubleDenominator q) := by
  unfold projectPairedOddDoubleAggregate projectOddDoubleSignedContribution
  simp_rw [sum_pairedOddDoubleClass_eq_selected_pairs]
  simp only [Complex.re_sum, Complex.add_re]
  conv_rhs => rw [Finset.sum_neg_distrib]
  apply congrArg Neg.neg
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The pre-existing V1.8.670 large-denominator perturbation is exactly the
sum of the paired aggregate and the two residual project contributions.  No
componentwise budget or cross-term estimate is introduced. -/
theorem largeDenominatorPerturbation_eq_three_project_classes
    (M N : Nat) :
    largeDenominatorPerturbation M (oddProjectWidth M) (oddProjectRadius M) N =
      projectPairedOddDoubleAggregate M N +
        projectFourDivisibleResidual M N +
        projectUnpairedOddResidual M N := by
  unfold largeDenominatorPerturbation largeDenominatorOddOddDeficit
    explicitLargeDenominatorSincKernel projectPairedOddDoubleAggregate
    projectFourDivisibleResidual projectUnpairedOddResidual
  rw [largeDenominatorClass_eq_three_residual_classes]
  simp_rw [Finset.sum_union
    (pairedUnionFour_disjoint_unpaired (R := oddProjectRadius M))]
  simp_rw [Finset.sum_union (paired_disjoint_four (R := oddProjectRadius M))]
  simp only [Complex.add_re, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- Exact project-level four-class identity.  Each denominator occurs exactly
once, all three non-small classes retain the inherited outer minus sign, and
there is no factor `2`. -/
theorem projectOddOddCoefficient_eq_four_class_partition
    (M N : Nat)
    (hscale : 2 * oddProjectWidth M * oddProjectRadius M < M) :
    projectOddOddCoefficient M N =
      compensatedSmallDenominatorCore M (oddProjectWidth M)
          (oddProjectRadius M) N +
        projectPairedOddDoubleAggregate M N +
        projectFourDivisibleResidual M N +
        projectUnpairedOddResidual M N := by
  rw [projectOddOddCoefficient_eq_expandedRamanujanSincSum M N hscale]
  unfold compensatedSmallDenominatorCore smallDenominatorOddOddDeficit
    projectPairedOddDoubleAggregate projectFourDivisibleResidual
    projectUnpairedOddResidual explicitSmallDenominatorSincKernel
  simp_rw [sum_denominator_four_class]
  rw [← smallDenominatorClass_eq_filter_le_two]
  simp only [Complex.add_re, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

end GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
