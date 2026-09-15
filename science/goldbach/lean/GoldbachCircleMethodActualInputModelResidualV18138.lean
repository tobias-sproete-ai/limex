import GoldbachCircleMethodAuxiliaryMinorGlobalErrorV18137
import GoldbachCircleMethodActiveExceptionalCenteringV18129

set_option autoImplicit false
open scoped BigOperators Classical
open GoldbachCircleMethodFourierIdentityV171
open GoldbachCircleMethodFiniteCompanionBindingV18118
open GoldbachCircleMethodFiniteWindowConvolutionV18119
open GoldbachCircleMethodLogCutoffPresieveBindingV18120
open GoldbachCircleMethodPrincipalWindowBoundaryV18121
open GoldbachCircleMethodActualCenteredResidualAssemblyV18127
open GoldbachCircleMethodActiveExceptionalCenteringV18129
open GoldbachCircleMethodRealApproximationMinorAdapterV1873
open GoldbachCircleMethodActualBlockAuxiliaryMinorV18136
open GoldbachCircleMethodAuxiliaryMinorGlobalErrorV18137

namespace GoldbachCircleMethodActualInputModelResidualV18138

/-- The actual input minus the actual principal companion and centered error,
not the earlier convolution residual and not an arbitrary small function. -/
noncomputable def inputPrincipalResidual (B N : ℕ) (R : ℝ) (hR : 1<R)
    (G : ℝ → ℝ) : ℂ :=
  blockInput B N -
    finiteCompanion (oneLevel (log_cutoff_contains_one R hR)) N (logWeight R G) -
    centeredWindowError ⌊R^2⌋₊ N ((B : ℝ)/R^4)
      (blockCarrier B) (blockInput B) (logWeight R G)

/-- Active character is an admitted finite slot, not asserted exceptional here. -/
noncomputable def inputActiveResidual (B N : ℕ) (R : ℝ) (hR : 1<R)
    (b : ℝ) (G : ℝ → ℝ) (e : CharacterSlot ⌊R^2⌋₊) : ℂ :=
  blockInput B N -
    adjustedModel ⌊R^2⌋₊ N (log_cutoff_contains_one R hR) b (logWeight R G) e -
    adjustedCenteredError ⌊R^2⌋₊ B N ((B : ℝ)/R^4) b
      (blockInput B) (logWeight R G) e

theorem input_principal_residual_identity (B N : ℕ) (R : ℝ) (hR : 1<R)
    (G : ℝ → ℝ) :
    inputPrincipalResidual B N R hR G =
      blockInput B N -
        normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
          (blockCarrier B) (blockInput B) (logWeight R G) +
      actualCenteredResidual B N R hR G := by
  unfold inputPrincipalResidual actualCenteredResidual
  ring

theorem input_active_residual_identity (B N : ℕ) (R : ℝ) (hR : 1<R)
    (b : ℝ) (G : ℝ → ℝ) (e : CharacterSlot ⌊R^2⌋₊) :
    inputActiveResidual B N R hR b G e =
      blockInput B N -
        normalizedWindowConvolution ⌊R^2⌋₊ N ((B : ℝ)/R^4)
          (blockCarrier B) (blockInput B) (logWeight R G) +
      activeCenteredResidual B N R hR b G e := by
  unfold inputActiveResidual activeCenteredResidual
  ring

theorem input_principal_fourier_identity (B : ℕ) (R : ℝ) (hR : 1<R)
    (G : ℝ → ℝ) (x : UnitAddCircle) :
    (∑ N ∈ blockCarrier B, inputPrincipalResidual B N R hR G*fourier (N : ℤ) x) =
      blockFourier B x-windowFourier B R G x+
        actualCenteredResidualFourier B R hR G x := by
  unfold blockFourier windowFourier actualCenteredResidualFourier
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N _
  rw [input_principal_residual_identity]
  ring

theorem input_active_fourier_identity (B : ℕ) (R : ℝ) (hR : 1<R)
    (b : ℝ) (G : ℝ → ℝ) (e : CharacterSlot ⌊R^2⌋₊) (x : UnitAddCircle) :
    (∑ N ∈ blockCarrier B, inputActiveResidual B N R hR b G e*fourier (N : ℤ) x) =
      blockFourier B x-windowFourier B R G x+
        activeCenteredResidualFourier B R hR b G e x := by
  unfold blockFourier windowFourier activeCenteredResidualFourier
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro N _
  rw [input_active_residual_identity]
  ring

/-- Conditional approximation to model PLUS its actual centered error.
No bound on the centered error itself is supplied or claimed. -/
theorem input_principal_fourier_bound (B : ℕ) (hB : 6≤B)
    (R C : ℝ) (hR : 1<R) (hC : 0≤C) (hV : RealVaughanEstimate C)
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ)))≤R)
    (hupper : R≤(B : ℝ)^((1 : ℝ)/10000))
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (hplateau : ∀ u : ℝ, 0≤u → u≤1 → G u=1)
    (x : UnitAddCircle) :
    ‖∑ N ∈ blockCarrier B, inputPrincipalResidual B N R hR G*fourier (N : ℤ) x‖≤
      (9*((1+M)/2+3*Real.pi)+(8*(48 : ℝ)^8*C)*(1+2*M)+(81/2)*M)*
        (B : ℝ)*R^(-(1 : ℝ)/3) := by
  rw [input_principal_fourier_identity]
  have ha := actual_window_global_error_fits_budget B hB R C hC hV
    hlower hupper G M hM hG hplateau x
  have hb := centered_residual_fourier_fits_target_budget B (by omega)
    R hR G M hM hG hupper x
  exact (norm_add_le _ _).trans (by linarith)

/-- Arbitrary admitted active character; the exact adjusted coefficient stays
in both model and error. No exceptional-zero existence is inferred. -/
theorem input_active_fourier_bound (B : ℕ) (hB : 6≤B)
    (R C : ℝ) (hR : 1<R) (hC : 0≤C) (hV : RealVaughanEstimate C)
    (hlower : Real.exp (Real.sqrt (Real.log (B : ℝ)))≤R)
    (hupper : R≤(B : ℝ)^((1 : ℝ)/10000))
    (b : ℝ) (hb : 0≤b) (hb1 : b≤1)
    (G : ℝ → ℝ) (M : ℝ) (hM : 0≤M) (hG : ∀ u : ℝ, |G u|≤M)
    (hplateau : ∀ u : ℝ, 0≤u → u≤1 → G u=1)
    (e : CharacterSlot ⌊R^2⌋₊) (x : UnitAddCircle) :
    ‖∑ N ∈ blockCarrier B, inputActiveResidual B N R hR b G e*fourier (N : ℤ) x‖≤
      (9*((1+M)/2+3*Real.pi)+(8*(48 : ℝ)^8*C)*(1+2*M)+46*M)*
        (B : ℝ)*R^(-(1 : ℝ)/3) := by
  rw [input_active_fourier_identity]
  have ha := actual_window_global_error_fits_budget B hB R C hC hV
    hlower hupper G M hM hG hplateau x
  have he := active_residual_fourier_fits_target_budget B (by omega)
    R hR b hb hb1 G M hM hG hupper e x
  exact (norm_add_le _ _).trans (by linarith)

end GoldbachCircleMethodActualInputModelResidualV18138
