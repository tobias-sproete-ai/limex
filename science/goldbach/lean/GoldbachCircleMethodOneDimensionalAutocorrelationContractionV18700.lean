import GoldbachCircleMethodFactorizedSameResidueCollisionExactLagDecompositionV18699

/-!
# V1.8.700: exact one-dimensional autocorrelation contraction

This append-only module contracts the two residue coordinates in the exact
V1.8.699 diagonal--positive-lag--mean-square identity.  The contraction is
performed with the genuine V1.8.698 one-dimensional signed residue fiber.

Every contracted term is an exact product of two one-dimensional residue
kernels.  No absolute value, global triangle inequality, global LCM,
replacement weight, smallness estimate, asymptotic claim, moment estimate,
or Goldbach conclusion is introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodOneDimensionalAutocorrelationContractionV18700

open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualSignedTargetResidueFiberCenteredEnergyV18696
open GoldbachCircleMethodSelectedPairSignedResidueWeightExactOneDimensionalFactorizationV18698
open GoldbachCircleMethodFactorizedSameResidueCollisionExactLagDecompositionV18699

/-- The exact signed autocorrelation kernel of one V1.8.698 residue fiber. -/
noncomputable def selectedPairOneFiberResidueKernel
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n m : Nat) : Real :=
  ∑ x : ZMod q.val.val,
    selectedPairOneFiberSignedResidueWeight M q n x *
      selectedPairOneFiberSignedResidueWeight M q m x

/-- A finite product fiber contracts exactly into the product of its two
one-dimensional residue kernels. -/
theorem sum_residue_product_eq_kernel_product
    {A B : Type} [Fintype A] [Fintype B]
    (a c : A → Real) (b d : B → Real) :
    (∑ x : A, ∑ y : B, (a x * b y) * (c x * d y)) =
      (∑ x : A, a x * c x) * (∑ y : B, b y * d y) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  ring

/-- Finite-indexed form of the same two-coordinate contraction. -/
theorem sum_indexed_residue_product_eq_kernel_sum
    {A B I : Type} [Fintype A] [Fintype B]
    (s : Finset I)
    (a c : I → A → Real) (b d : I → B → Real) :
    (∑ x : A, ∑ y : B, ∑ i ∈ s,
      (a i x * b i y) * (c i x * d i y)) =
      ∑ i ∈ s,
        (∑ x : A, a i x * c i x) * (∑ y : B, b i y * d i y) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert, hi, not_false_eq_true]
      simp_rw [Finset.sum_add_distrib]
      rw [sum_residue_product_eq_kernel_product (a i) (c i) (b i) (d i)]
      rw [ih]

/-- Squaring a finite sum is its exact ordered double product sum. -/
theorem sq_sum_eq_ordered_double_sum
    {A : Type} [DecidableEq A]
    (s : Finset A) (f : A → Real) :
    (∑ a ∈ s, f a) ^ 2 =
      ∑ a ∈ s, ∑ b ∈ s, f a * f b := by
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]

/-- Summation of the diagonal over both residue coordinates contracts to a
product of one-dimensional diagonal kernels. -/
theorem sum_selectedPairFactorizedResidueSequence_sq_eq_kernel_diagonal
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    (∑ x : ZMod q.val.val, ∑ y : ZMod r.val.val,
      ∑ n ∈ Finset.range M.succ,
        selectedPairFactorizedResidueSequence M q r x y n ^ 2) =
      ∑ n ∈ Finset.range M.succ,
        selectedPairOneFiberResidueKernel M q n n *
          selectedPairOneFiberResidueKernel M r n n := by
  unfold selectedPairFactorizedResidueSequence selectedPairOneFiberResidueKernel
  simp only [pow_two]
  exact sum_indexed_residue_product_eq_kernel_sum
    (Finset.range M.succ)
    (fun n x => selectedPairOneFiberSignedResidueWeight M q n x)
    (fun n x => selectedPairOneFiberSignedResidueWeight M q n x)
    (fun n y => selectedPairOneFiberSignedResidueWeight M r n y)
    (fun n y => selectedPairOneFiberSignedResidueWeight M r n y)

/-- Summation of every endpoint-safe positive `K=q*r` lag over both residue
coordinates contracts to the product of the corresponding one-dimensional
autocorrelation kernels. -/
theorem sum_finitePositiveKSpacedLagSum_eq_kernel_lag_sum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    (∑ x : ZMod q.val.val, ∑ y : ZMod r.val.val,
      finitePositiveKSpacedLagSum M (q.val.val * r.val.val)
        (selectedPairFactorizedResidueSequence M q r x y)) =
      ∑ hn ∈ positiveKSpacedLagCarrier M (q.val.val * r.val.val),
        selectedPairOneFiberResidueKernel M q hn.2
            (hn.2 + hn.1 * (q.val.val * r.val.val)) *
          selectedPairOneFiberResidueKernel M r hn.2
            (hn.2 + hn.1 * (q.val.val * r.val.val)) := by
  unfold finitePositiveKSpacedLagSum selectedPairFactorizedResidueSequence
    selectedPairOneFiberResidueKernel
  exact sum_indexed_residue_product_eq_kernel_sum
    (positiveKSpacedLagCarrier M (q.val.val * r.val.val))
    (fun hn x => selectedPairOneFiberSignedResidueWeight M q hn.2 x)
    (fun hn x => selectedPairOneFiberSignedResidueWeight M q
      (hn.2 + hn.1 * (q.val.val * r.val.val)) x)
    (fun hn y => selectedPairOneFiberSignedResidueWeight M r hn.2 y)
    (fun hn y => selectedPairOneFiberSignedResidueWeight M r
      (hn.2 + hn.1 * (q.val.val * r.val.val)) y)

/-- Summation of the negative mean-square term over both residue coordinates
contracts exactly to the ordered `(n,m)` sum of products of one-dimensional
residue kernels. -/
theorem sum_selectedPairFactorizedResidueSequence_sum_sq_eq_kernel_double_sum
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    (∑ x : ZMod q.val.val, ∑ y : ZMod r.val.val,
      (∑ n ∈ Finset.range M.succ,
        selectedPairFactorizedResidueSequence M q r x y n) ^ 2) =
      ∑ n ∈ Finset.range M.succ,
        ∑ m ∈ Finset.range M.succ,
          selectedPairOneFiberResidueKernel M q n m *
            selectedPairOneFiberResidueKernel M r n m := by
  unfold selectedPairFactorizedResidueSequence selectedPairOneFiberResidueKernel
  simp_rw [sq_sum_eq_ordered_double_sum]
  have h := sum_indexed_residue_product_eq_kernel_sum
    ((Finset.range M.succ).product (Finset.range M.succ))
    (fun nm x => selectedPairOneFiberSignedResidueWeight M q nm.1 x)
    (fun nm x => selectedPairOneFiberSignedResidueWeight M q nm.2 x)
    (fun nm y => selectedPairOneFiberSignedResidueWeight M r nm.1 y)
    (fun nm y => selectedPairOneFiberSignedResidueWeight M r nm.2 y)
  simpa only [Finset.product_eq_sprod, Finset.sum_product, Prod.fst, Prod.snd] using h

/-- Exact two-coordinate contraction of the V1.8.699 project identity.

The diagonal, each positive `q*r`-spaced lag, and the negative mean square
are all retained with their original signs and exact coefficients. -/
theorem sum_selectedPairCenteredTargetResidueFiberEnergy_eq_oneDimensionalAutocorrelationContraction
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    (∑ x : ZMod q.val.val, ∑ y : ZMod r.val.val,
      selectedPairCenteredTargetResidueFiberEnergy M q r x y) =
      (∑ n ∈ Finset.range M.succ,
        selectedPairOneFiberResidueKernel M q n n *
          selectedPairOneFiberResidueKernel M r n n) +
        2 * (∑ hn ∈ positiveKSpacedLagCarrier M
            (q.val.val * r.val.val),
          selectedPairOneFiberResidueKernel M q hn.2
              (hn.2 + hn.1 * (q.val.val * r.val.val)) *
            selectedPairOneFiberResidueKernel M r hn.2
              (hn.2 + hn.1 * (q.val.val * r.val.val))) -
        (∑ n ∈ Finset.range M.succ,
          ∑ m ∈ Finset.range M.succ,
            selectedPairOneFiberResidueKernel M q n m *
              selectedPairOneFiberResidueKernel M r n m) /
          (q.val.val * r.val.val : Real) := by
  simp_rw [selectedPairCenteredTargetResidueFiberEnergy_eq_diagonal_lags_sub_meanSquare]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have htwo :
      (∑ x : ZMod q.val.val, ∑ y : ZMod r.val.val,
        2 * finitePositiveKSpacedLagSum M (q.val.val * r.val.val)
          (selectedPairFactorizedResidueSequence M q r x y)) =
        2 * (∑ x : ZMod q.val.val, ∑ y : ZMod r.val.val,
          finitePositiveKSpacedLagSum M (q.val.val * r.val.val)
            (selectedPairFactorizedResidueSequence M q r x y)) := by
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [Finset.mul_sum]
  have hdiv :
      (∑ x : ZMod q.val.val, ∑ y : ZMod r.val.val,
        (∑ n ∈ Finset.range M.succ,
          selectedPairFactorizedResidueSequence M q r x y n) ^ 2 /
            (q.val.val * r.val.val : Real)) =
        (∑ x : ZMod q.val.val, ∑ y : ZMod r.val.val,
          (∑ n ∈ Finset.range M.succ,
            selectedPairFactorizedResidueSequence M q r x y n) ^ 2) /
              (q.val.val * r.val.val : Real) := by
    symm
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [Finset.sum_div]
  rw [htwo, hdiv]
  rw [sum_selectedPairFactorizedResidueSequence_sq_eq_kernel_diagonal]
  rw [sum_finitePositiveKSpacedLagSum_eq_kernel_lag_sum]
  rw [sum_selectedPairFactorizedResidueSequence_sum_sq_eq_kernel_double_sum]

end GoldbachCircleMethodOneDimensionalAutocorrelationContractionV18700
