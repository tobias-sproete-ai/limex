import GoldbachCircleMethodCrossResidualSharpSplitV18539

/-!
# Goldbach V1.8.540: explicit cross-conductor pair expansion

The signed residual isolated in V1.8.538 is expanded as the real part of the
ordered off-diagonal conductor-pair sum.  This turns an opaque difference of
energies into the exact pairwise object on which complete-period
orthogonality or an incomplete-period remainder estimate would have to act.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCrossConductorPairExpansionV18540

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodExactCrossConductorResidualV18538
open GoldbachCircleMethodNonprincipalConductorAlignedCorrelationV18527

/-- Ordered off-diagonal part of the Hermitian square of a finite complex
family. -/
noncomputable def orderedCrossTermSum
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) : ℂ :=
  ∑ i : ι, ∑ j ∈ (Finset.univ.erase i), star (f i) * f j

theorem star_mul_self_re (z : ℂ) :
    (star z * z).re = ‖z‖ ^ 2 := by
  calc
    (star z * z).re = ((Complex.normSq z : ℂ)).re := by
      rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
    _ = Complex.normSq z := rfl
    _ = ‖z‖ ^ 2 := (Complex.sq_norm z).symm

/-- Taking real parts commutes with a finite sum.  This local additive-hom
lemma keeps the expansion independent of simplifier-specific coercion rules. -/
theorem re_fintype_sum
    {ι : Type} [Fintype ι] (f : ι → ℂ) :
    (∑ i : ι, f i).re = ∑ i : ι, (f i).re := by
  let reHom : ℂ →+ ℝ :=
    { toFun := Complex.re
      map_zero' := rfl
      map_add' := fun x y => Complex.add_re x y }
  change reHom (∑ i : ι, f i) = ∑ i : ι, reHom (f i)
  exact map_sum reHom f Finset.univ

/-- Exact diagonal/off-diagonal expansion for a finite complex family. -/
theorem star_sum_mul_sum_eq_diagonal_add_ordered_cross
    {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) :
    star (∑ i : ι, f i) * (∑ i : ι, f i) =
      (∑ i : ι, star (f i) * f i) + orderedCrossTermSum f := by
  rw [star_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  unfold orderedCrossTermSum
  calc
    (∑ i : ι, ∑ j : ι, star (f i) * f j) =
        ∑ i : ι,
          (star (f i) * f i +
            ∑ j ∈ (Finset.univ.erase i), star (f i) * f j) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    _ = _ := by
      rw [Finset.sum_add_distrib]

/-- The literal ordered cross-conductor correlation at one target. -/
noncomputable def orderedCrossConductorCorrelation
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) : ℝ :=
  (orderedCrossTermSum (fun r : PositiveLevel Q =>
    nonprincipalConductorCorrelation Q B N H w r)).re

/-- The V1.8.538 residual is exactly the ordered off-diagonal conductor-pair
correlation. -/
theorem crossConductorResidual_eq_ordered_pair_sum
    (Q B N : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    crossConductorResidual Q B N H w =
      orderedCrossConductorCorrelation Q B N H w := by
  have hcomplex := star_sum_mul_sum_eq_diagonal_add_ordered_cross
    (fun r : PositiveLevel Q =>
      nonprincipalConductorCorrelation Q B N H w r)
  have hreal := congrArg Complex.re hcomplex
  have henergy :
      ‖∑ r : PositiveLevel Q,
          nonprincipalConductorCorrelation Q B N H w r‖ ^ 2 =
        (∑ r : PositiveLevel Q,
          ‖nonprincipalConductorCorrelation Q B N H w r‖ ^ 2) +
          orderedCrossConductorCorrelation Q B N H w := by
    calc
      ‖∑ r : PositiveLevel Q,
          nonprincipalConductorCorrelation Q B N H w r‖ ^ 2 =
          (star (∑ r : PositiveLevel Q,
              nonprincipalConductorCorrelation Q B N H w r) *
            (∑ r : PositiveLevel Q,
              nonprincipalConductorCorrelation Q B N H w r)).re := by
        exact (star_mul_self_re _).symm
      _ =
          ((∑ r : PositiveLevel Q,
              star (nonprincipalConductorCorrelation Q B N H w r) *
                nonprincipalConductorCorrelation Q B N H w r) +
            orderedCrossTermSum (fun r : PositiveLevel Q =>
              nonprincipalConductorCorrelation Q B N H w r)).re := hreal
      _ =
          (∑ r : PositiveLevel Q,
            (star (nonprincipalConductorCorrelation Q B N H w r) *
              nonprincipalConductorCorrelation Q B N H w r).re) +
            (orderedCrossTermSum (fun r : PositiveLevel Q =>
              nonprincipalConductorCorrelation Q B N H w r)).re := by
        rw [Complex.add_re, re_fintype_sum]
      _ =
          (∑ r : PositiveLevel Q,
            ‖nonprincipalConductorCorrelation Q B N H w r‖ ^ 2) +
            orderedCrossConductorCorrelation Q B N H w := by
        simp only [star_mul_self_re, orderedCrossConductorCorrelation]
  unfold crossConductorResidual
  rw [nonprincipalPrimitiveCorrelation_eq_sum_conductors]
  exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using henergy)

/-- Block-level readback: the exact residual is the sum of the explicit
ordered conductor-pair correlations. -/
theorem blockCrossConductorResidual_eq_ordered_pair_sum
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ) :
    blockCrossConductorResidual Q B H w =
      ∑ N ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B,
        orderedCrossConductorCorrelation Q B N H w := by
  unfold blockCrossConductorResidual
  apply Finset.sum_congr rfl
  intro N _hN
  exact crossConductorResidual_eq_ordered_pair_sum Q B N H w

end GoldbachCircleMethodCrossConductorPairExpansionV18540
