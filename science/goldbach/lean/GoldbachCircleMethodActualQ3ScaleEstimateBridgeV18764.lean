import GoldbachCircleMethodActualQ3SmallPrefixProjectAbsorptionV18763

/-!
# V1.8.764: actual q=3 bridge to the project scale estimate

The literal residue masses from V1.8.761 are identified with the pre-existing
`psiResidue` carrier.  Consequently, the general fixed-scale reduced-class
estimate from V1.8.69 can be applied to the genuine quadratic character at
modulus three.  The common main term cancels exactly.

The external `ScaleReducedClassEstimate` remains an explicit hypothesis.
No distribution theorem or Goldbach conclusion is asserted.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology

namespace GoldbachCircleMethodActualQ3ScaleEstimateBridgeV18764

open GoldbachCircleMethodCeilScaleEnvelopesV1864
open GoldbachCircleMethodUniformMajorPrefixReductionV1865
open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodUniformResidueInputBridgeV1869
open GoldbachCircleMethodActualQ3DirichletCharacterBindingV18760
open GoldbachCircleMethodActualQ3ExplicitPsiSourceMatchV18761

/-- The new literature-facing mass and the original project residue mass are
definitionally the same finite sum. -/
theorem fullLambdaQ3ResidueMass_eq_psiResidue
    (x : Nat) (r : ZMod 3) :
    fullLambdaQ3ResidueMass x r =
      (@psiResidue x 3 ⟨by norm_num⟩ r : Complex) := by
  unfold fullLambdaQ3ResidueMass psiResidue
  rw [Finset.sum_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases h : (a : ZMod 3) = r <;> simp [h]

/-- Two reduced-class errors with a common main term control the genuine
q=3 Dirichlet-character sum with exactly twice the class bound. -/
theorem dirichletCharacterPartialSum_norm_le_two_mul_of_psiResidueBounds
    (x : Nat) (B : Real)
    (hclasses : ∀ r : ZMod 3, IsUnit r →
      |@psiResidue x 3 ⟨by norm_num⟩ r - (x : Real) / 2| ≤ B) :
    ‖fullLambdaQ3DirichletCharacterPartialSum x.succ‖ ≤ 2 * B := by
  rw [fullLambdaQ3DirichletCharacterPartialSum_succ_eq_residueMass_sub]
  rw [fullLambdaQ3ResidueMass_eq_psiResidue,
    fullLambdaQ3ResidueMass_eq_psiResidue]
  have hunit1 : IsUnit (1 : ZMod 3) := by norm_num
  have hunit2 : IsUnit (2 : ZMod 3) := by decide
  have h1 := hclasses (1 : ZMod 3) hunit1
  have h2 := hclasses (2 : ZMod 3) hunit2
  have h1c :
      ‖(@psiResidue x 3 ⟨by norm_num⟩ (1 : ZMod 3) : Complex) -
          ((x : Real) / 2 : Complex)‖ ≤ B := by
    have hcast :
        ((@psiResidue x 3 ⟨by norm_num⟩ (1 : ZMod 3) : Real) : Complex) -
            ((x : Real) : Complex) / 2 =
          ((@psiResidue x 3 ⟨by norm_num⟩ (1 : ZMod 3) -
            (x : Real) / 2 : Real) : Complex) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact h1
  have h2c :
      ‖(@psiResidue x 3 ⟨by norm_num⟩ (2 : ZMod 3) : Complex) -
          ((x : Real) / 2 : Complex)‖ ≤ B := by
    have hcast :
        ((@psiResidue x 3 ⟨by norm_num⟩ (2 : ZMod 3) : Real) : Complex) -
            ((x : Real) : Complex) / 2 =
          ((@psiResidue x 3 ⟨by norm_num⟩ (2 : ZMod 3) -
            (x : Real) / 2 : Real) : Complex) := by norm_cast
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact h2
  calc
    ‖(@psiResidue x 3 ⟨by norm_num⟩ (1 : ZMod 3) : Complex) -
          (@psiResidue x 3 ⟨by norm_num⟩ (2 : ZMod 3) : Complex)‖ =
        ‖((@psiResidue x 3 ⟨by norm_num⟩ (1 : ZMod 3) : Real) : Complex) -
            ((x : Real) / 2 : Complex) +
          (((x : Real) / 2 : Complex) -
            ((@psiResidue x 3 ⟨by norm_num⟩ (2 : ZMod 3) : Real) : Complex))‖ := by
      congr 1
      ring
    _ ≤ ‖((@psiResidue x 3 ⟨by norm_num⟩ (1 : ZMod 3) : Real) : Complex) -
            ((x : Real) / 2 : Complex)‖ +
          ‖((x : Real) / 2 : Complex) -
            ((@psiResidue x 3 ⟨by norm_num⟩ (2 : ZMod 3) : Real) : Complex)‖ :=
      norm_add_le _ _
    _ ≤ B + B := by
      exact add_le_add h1c (by simpa only [norm_sub_rev] using h2c)
    _ = 2 * B := by ring

/-- The already isolated project-scale estimate yields a genuine-character
bound on every large prefix, once modulus three lies in the project radius. -/
theorem dirichletCharacterPartialSum_norm_le_largePrefixScaleEstimate
    (M x k₀ : Nat) (C c : Real)
    (hM : 0 < M) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hlog : (2 : Real) ^ 12 ≤ Real.log (M : Real))
    (hstart : (k₀ : Real) ≤ Real.sqrt (M : Real))
    (hscale : ScaleReducedClassEstimate 11 k₀ C c)
    (hthree : 3 ≤ logRadius 10 M)
    (hxM : x ≤ M)
    (hlarge : Real.sqrt (M : Real) ≤ x) :
    ‖fullLambdaQ3DirichletCharacterPartialSum x.succ‖ ≤
      2 * prefixEnvelope M C (c / 2) := by
  have hclasses := large_classes_from_scale_estimate
    10 M k₀ C c hM hC hc hlog hstart hscale
  apply dirichletCharacterPartialSum_norm_le_two_mul_of_psiResidueBounds
    x (prefixEnvelope M C (c / 2))
  intro r hr
  have h := hclasses 3 (by norm_num) hthree r hr x hxM hlarge
  have ht : Nat.totient 3 = 2 := by decide
  rw [ht] at h
  exact h

end GoldbachCircleMethodActualQ3ScaleEstimateBridgeV18764
