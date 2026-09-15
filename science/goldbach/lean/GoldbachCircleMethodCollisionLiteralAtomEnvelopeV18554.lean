import GoldbachCircleMethodCollisionLiteralCutoffEnvelopeV18553

/-!
# Goldbach V1.8.554: collision literal-atom envelope

The remaining collision energy is separated into its periodic atom and its
actual target-dependent weight.  A primitive twisted Ramanujan atom has norm
at most the complementary level, so a cross atom costs `l*k`, not a second
blind global product-carrier count.  All coefficient and primitive-source
weights remain literal.
-/

set_option autoImplicit false

open scoped BigOperators Classical ComplexConjugate

namespace GoldbachCircleMethodCollisionLiteralAtomEnvelopeV18554

open GoldbachCircleMethodBoundedConductorReindexV18117
open GoldbachCircleMethodCanonicalCoupledFirstMarginalAggregationV18378
open GoldbachCircleMethodCollisionLiteralBlockEnergyV18552
open GoldbachCircleMethodCollisionLiteralSliceEnergyV18551
open GoldbachCircleMethodLiteralCrossWeightFactorizationV18545
open GoldbachCircleMethodPairwiseActiveCostAggregationV18318
open GoldbachCircleMethodPrimitiveTwistedRamanujanSupportV18208
open GoldbachCircleMethodRemovedConvolutionNormV18123

/-- Pointwise norm of the primitive twisted Ramanujan product is bounded by
its complementary modulus. -/
theorem twistedRamanujan_norm_le_complement
    (r l : ℕ) [NeZero r] [NeZero l]
    (χ : DirichletCharacter ℂ r) (x : ZMod (r * l)) :
    ‖twistedRamanujan r l χ x‖ ≤ (l : ℝ) := by
  unfold twistedRamanujan
  rw [norm_mul]
  calc
    _ ≤ 1 * (l : ℝ) :=
      mul_le_mul (χ.norm_le_one _)
        (unit_character_norm_le_level l _)
        (norm_nonneg _) zero_le_one
    _ = (l : ℝ) := one_mul _

/-- The actual periodic cross atom retains the product `l*k` of the two
complementary levels. -/
theorem literalCrossAtom_norm_le_complement_product
    {Q : ℕ} (r s l k : PositiveLevel Q)
    (χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive})
    (ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive})
    (N : ℕ) :
    ‖literalCrossAtom r s l k χ ψ N‖ ≤ (l.val : ℝ) * (k.val : ℝ) := by
  unfold literalCrossAtom
  rw [norm_mul, norm_star]
  exact mul_le_mul
    (twistedRamanujan_norm_le_complement r.val l.val χ.val _)
    (twistedRamanujan_norm_le_complement s.val k.val ψ.val _)
    (norm_nonneg _) (by positivity)

/-- Exact collision energy after replacing only the periodic atom by its
complement-level norm envelope. -/
noncomputable def collisionLiteralAtomEnvelopeEnergy
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) : ℝ :=
  ∑ N ∈ GoldbachCircleMethodLogCutoffPresieveBindingV18120.blockCarrier B,
    ∑ ψ : {ψ : DirichletCharacter ℂ s.val // ψ.IsPrimitive},
      ∑ χ : {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive},
        ∑ k ∈ activeComplementCarrier s,
          ∑ l ∈ (activeComplementCarrier r).filter
              (fun l => r.val * l.val = s.val * k.val),
            ((l.val : ℝ) * (k.val : ℝ)) ^ 2 *
              ‖literalCrossWeight B N H w r s l k χ ψ‖ ^ 2

/-- The genuine weighted collision energy is bounded by the literal atom
envelope without altering its collision support. -/
theorem collisionLiteralBlockEnergy_le_atomEnvelope
    (Q B : ℕ) (H : ℝ) (w : ℕ → ℂ)
    (r s : PositiveLevel Q) :
    collisionLiteralBlockEnergy Q B H w r s ≤
      collisionLiteralAtomEnvelopeEnergy Q B H w r s := by
  unfold collisionLiteralBlockEnergy collisionLiteralSliceEnergy
    collisionLiteralAtomEnvelopeEnergy
  apply Finset.sum_le_sum
  intro N _hN
  apply Finset.sum_le_sum
  intro ψ _hψ
  apply Finset.sum_le_sum
  intro χ _hχ
  apply Finset.sum_le_sum
  intro k _hk
  apply Finset.sum_le_sum
  intro l _hl
  let z := literalCrossAtom r s l k χ ψ N *
    literalCrossWeight B N H w r s l k χ ψ
  have hre : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr
      (Complex.abs_re_le_norm _)
  have hatom : ‖literalCrossAtom r s l k χ ψ N‖ ^ 2 ≤
      ((l.val : ℝ) * (k.val : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      (literalCrossAtom_norm_le_complement_product r s l k χ ψ N) 2
  calc
    z.re ^ 2 ≤ ‖z‖ ^ 2 := hre
    _ = ‖literalCrossAtom r s l k χ ψ N‖ ^ 2 *
        ‖literalCrossWeight B N H w r s l k χ ψ‖ ^ 2 := by
      dsimp only [z]
      rw [norm_mul]
      ring
    _ ≤ ((l.val : ℝ) * (k.val : ℝ)) ^ 2 *
        ‖literalCrossWeight B N H w r s l k χ ψ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hatom (sq_nonneg _)

end GoldbachCircleMethodCollisionLiteralAtomEnvelopeV18554
