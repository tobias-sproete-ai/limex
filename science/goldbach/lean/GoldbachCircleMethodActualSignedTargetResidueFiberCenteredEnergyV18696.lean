import GoldbachCircleMethodExactSignedResidueFiberAggregationBeforeGlobalTriangleV18695

/-!
# V1.8.696: actual signed target-residue fiber and centered energy

For one ordered pair of distinct selected odd bases and one pair of base
residues, this append-only module regroups the literal V1.8.695 signed target
fiber by the actual target residue `z : ZMod (q*r)`.  It defines the exact
finite residue-fiber mean and centered energy.  The constant component is then
removed using the already kernel-checked complete-period zero of the genuine
pair-local atom, and finite real Cauchy--Schwarz exposes the exact product of
atom energy and actual centered residue-fiber energy.

All target and fiber gates, moving notches, arithmetic fiber masses, and sinc
radii remain definitionally inside the imported signed weight.  No global LCM,
replacement weight, smallness estimate, denominator summability, moment
estimate, exceptional-set statement, or Goldbach conclusion is introduced.

`proof_status = NO_PROOF`.
-/

set_option autoImplicit false

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualSignedTargetResidueFiberCenteredEnergyV18696

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodOddOddSignedFiberAdapterV18665
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodFullChannelPartitionedGramV18689
open GoldbachCircleMethodSelectedPairCrossCorrelationExpansionV18690
open GoldbachCircleMethodExactSignedResidueFiberAggregationBeforeGlobalTriangleV18695

/-- The actual signed target-residue fiber.  It aggregates exactly the
V1.8.695 signed `(a mod q,b mod r)` fiber weight over the finite target box
`n ∈ range (M+1)` with residue `z mod (q*r)`. -/
noncomputable def selectedPairSignedTargetResidueFiber
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val)
    (z : ZMod (q.val.val * r.val.val)) : Real :=
  ∑ n ∈ Finset.range M.succ,
    if (n : ZMod (q.val.val * r.val.val)) = z then
      selectedPairSignedResidueFiberWeight M q r n x y
    else 0

/-- Exact reindexing of one fixed `(x,y)` target sum by the pair-local target
residue.  No absolute value or estimate is used. -/
theorem sum_baseResidueAtom_mul_signedFiberWeight_eq_targetResidueFibers
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    (∑ n ∈ Finset.range M.succ,
        selectedPairBaseResidueAtom q r x y
            (n : ZMod (q.val.val * r.val.val)) *
          selectedPairSignedResidueFiberWeight M q r n x y) =
      ∑ z : ZMod (q.val.val * r.val.val),
        selectedPairBaseResidueAtom q r x y z *
          selectedPairSignedTargetResidueFiber M q r x y z := by
  unfold selectedPairSignedTargetResidueFiber
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.sum_eq_single
    (n : ZMod (q.val.val * r.val.val))]
  · simp
  · intro z _hz hzne
    simp [Ne.symm hzne]
  · simp

/-- The literal arithmetic mean of the actual signed target-residue fiber. -/
noncomputable def selectedPairSignedTargetResidueFiberMean
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) : Real :=
  (∑ z : ZMod (q.val.val * r.val.val),
      selectedPairSignedTargetResidueFiber M q r x y z) /
    (Fintype.card (ZMod (q.val.val * r.val.val)) : Real)

/-- The actual centered target-residue fiber. -/
noncomputable def selectedPairCenteredTargetResidueFiber
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val)
    (z : ZMod (q.val.val * r.val.val)) : Real :=
  selectedPairSignedTargetResidueFiber M q r x y z -
    selectedPairSignedTargetResidueFiberMean M q r x y

/-- The centering is exact: the centered actual target-residue fiber has
finite sum zero. -/
theorem sum_selectedPairCenteredTargetResidueFiber_eq_zero
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    (∑ z : ZMod (q.val.val * r.val.val),
      selectedPairCenteredTargetResidueFiber M q r x y z) = 0 := by
  have hcard :
      (Fintype.card (ZMod (q.val.val * r.val.val)) : Real) ≠ 0 := by
    positivity
  unfold selectedPairCenteredTargetResidueFiber
    selectedPairSignedTargetResidueFiberMean
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- The exact finite atom energy on the pair-local target residue ring. -/
noncomputable def selectedPairBaseResidueAtomEnergy
    {R : Nat} (q r : PairedOddBase R)
    (x : ZMod q.val.val) (y : ZMod r.val.val) : Real :=
  ∑ z : ZMod (q.val.val * r.val.val),
    selectedPairBaseResidueAtom q r x y z ^ 2

/-- The exact centered energy of the actual signed target-residue fiber. -/
noncomputable def selectedPairCenteredTargetResidueFiberEnergy
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) : Real :=
  ∑ z : ZMod (q.val.val * r.val.val),
    selectedPairCenteredTargetResidueFiber M q r x y z ^ 2

/-- The exact signed target-residue correlation for one fixed `(x,y)` fiber. -/
noncomputable def selectedPairSignedTargetResidueCorrelation
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (x : ZMod q.val.val) (y : ZMod r.val.val) : Real :=
  ∑ z : ZMod (q.val.val * r.val.val),
    selectedPairBaseResidueAtom q r x y z *
      selectedPairSignedTargetResidueFiber M q r x y z

/-- The atom is orthogonal to the constant part of every actual target fiber.
This is exactly where the imported complete-period zero is used. -/
theorem sum_baseResidueAtom_mul_targetFiberMean_eq_zero
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (hrErase : r ∈ Finset.univ.erase q)
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    (∑ z : ZMod (q.val.val * r.val.val),
        selectedPairBaseResidueAtom q r x y z *
          selectedPairSignedTargetResidueFiberMean M q r x y) = 0 := by
  rw [← Finset.sum_mul]
  rw [selectedPairBaseResidueAtom_complete_period_eq_zero q r hrErase x y]
  simp

/-- Exact removal of the constant target-residue component before applying
Cauchy--Schwarz. -/
theorem selectedPairSignedTargetResidueCorrelation_eq_centered
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (hrErase : r ∈ Finset.univ.erase q)
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    selectedPairSignedTargetResidueCorrelation M q r x y =
      ∑ z : ZMod (q.val.val * r.val.val),
        selectedPairBaseResidueAtom q r x y z *
          selectedPairCenteredTargetResidueFiber M q r x y z := by
  unfold selectedPairSignedTargetResidueCorrelation
    selectedPairCenteredTargetResidueFiber
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [sum_baseResidueAtom_mul_targetFiberMean_eq_zero M q r hrErase x y]
  simp

/-- Finite real Cauchy--Schwarz for the exact centered target residue fiber.
This is an identity-level reduction to the two actual energies, not a claim
that either energy is small in the project normalization. -/
theorem selectedPairSignedTargetResidueCorrelation_sq_le_energy_product
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (hrErase : r ∈ Finset.univ.erase q)
    (x : ZMod q.val.val) (y : ZMod r.val.val) :
    selectedPairSignedTargetResidueCorrelation M q r x y ^ 2 ≤
      selectedPairBaseResidueAtomEnergy q r x y *
        selectedPairCenteredTargetResidueFiberEnergy M q r x y := by
  rw [selectedPairSignedTargetResidueCorrelation_eq_centered
    M q r hrErase x y]
  unfold selectedPairBaseResidueAtomEnergy
    selectedPairCenteredTargetResidueFiberEnergy
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun z : ZMod (q.val.val * r.val.val) =>
      selectedPairBaseResidueAtom q r x y z)
    (fun z : ZMod (q.val.val * r.val.val) =>
      selectedPairCenteredTargetResidueFiber M q r x y z)

/-- Exact fixed-pair correlation reindexing into the actual signed target
residue correlations.  The distinct-pair hypothesis is retained for the
subsequent centered identity. -/
theorem selectedPairCrossFiberSum_eq_targetResidueFiberCorrelations
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M)) :
    (∑ N ∈ evenTargetBlock M,
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        ∑ u ∈ oddOddOffDiagonalSumCarrier M N,
          projectPairedBaseFiberTerm M q N t *
            projectPairedBaseFiberTerm M r N u) =
      ∑ x : ZMod q.val.val,
        ∑ y : ZMod r.val.val,
          selectedPairSignedTargetResidueCorrelation M q r x y := by
  rw [selectedPairCrossFiberSum_eq_signedResidueFibers]
  calc
    (∑ n ∈ Finset.range M.succ,
        ∑ x : ZMod q.val.val,
          ∑ y : ZMod r.val.val,
            selectedPairBaseResidueAtom q r x y
                (n : ZMod (q.val.val * r.val.val)) *
              selectedPairSignedResidueFiberWeight M q r n x y) =
      ∑ x : ZMod q.val.val,
        ∑ n ∈ Finset.range M.succ,
          ∑ y : ZMod r.val.val,
            selectedPairBaseResidueAtom q r x y
                (n : ZMod (q.val.val * r.val.val)) *
              selectedPairSignedResidueFiberWeight M q r n x y := by
        rw [Finset.sum_comm]
    _ = ∑ x : ZMod q.val.val,
          ∑ y : ZMod r.val.val,
            ∑ n ∈ Finset.range M.succ,
              selectedPairBaseResidueAtom q r x y
                  (n : ZMod (q.val.val * r.val.val)) *
                selectedPairSignedResidueFiberWeight M q r n x y := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      unfold selectedPairSignedTargetResidueCorrelation
      exact sum_baseResidueAtom_mul_signedFiberWeight_eq_targetResidueFibers
        M q r x y

/-- Exact pair-local centered representation of the original selected-pair
correlation.  No triangle inequality is taken over `(x,y)`. -/
theorem selectedPairCrossFiberSum_eq_centeredTargetResidueFibers
    (M : Nat)
    (q r : PairedOddBase (oddProjectRadius M))
    (hrErase : r ∈ Finset.univ.erase q) :
    (∑ N ∈ evenTargetBlock M,
      ∑ t ∈ oddOddOffDiagonalSumCarrier M N,
        ∑ u ∈ oddOddOffDiagonalSumCarrier M N,
          projectPairedBaseFiberTerm M q N t *
            projectPairedBaseFiberTerm M r N u) =
      ∑ x : ZMod q.val.val,
        ∑ y : ZMod r.val.val,
          ∑ z : ZMod (q.val.val * r.val.val),
            selectedPairBaseResidueAtom q r x y z *
              selectedPairCenteredTargetResidueFiber M q r x y z := by
  rw [selectedPairCrossFiberSum_eq_targetResidueFiberCorrelations
    M q r]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  exact selectedPairSignedTargetResidueCorrelation_eq_centered
    M q r hrErase x y

end GoldbachCircleMethodActualSignedTargetResidueFiberCenteredEnergyV18696
