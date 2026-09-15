import GoldbachCircleMethodActualQ3ExplicitPsiSourceMatchV18761

/-!
# V1.8.762: finite q=3 prefix-square-root source envelope

Bennett--Martin--O'Bryant--Rechnitzer, Theorem 1.9, supplies a maximal
small-range estimate for `psi(y;q,a)`.  At `q = 3` its published conservative
constant is `1.745 = 349/200`, and its stated range reaches `4 * 10^13`.

This append-only module states the exact finite specialization as an open
proposition and proves that it yields the single prefix ceiling required by
V1.8.760, with constant `3.49 = 349/100` after subtracting the two reduced
residue classes.  No source proposition is asserted or inhabited.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3ExplicitPrefixSqrtEnvelopeV18762

open GoldbachCircleMethodTwoScaleEvenBlockDefectReserveV1833
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688
open GoldbachCircleMethodActualMixedChannelRamanujanFactorizationV18727
open GoldbachCircleMethodActualQ3PrefixLocalDensitySignedReserveV18755
open GoldbachCircleMethodActualQ3UnitDifferenceScaleEnvelopeV18756
open GoldbachCircleMethodActualQ3DirichletCharacterBindingV18760
open GoldbachCircleMethodActualQ3ExplicitPsiSourceMatchV18761

noncomputable def q3ExplicitSmallPrefixClassConstant : Real := 349 / 200

def q3ExplicitSmallPrefixUpperRange : Nat := 40000000000000

/-- Exact modulus-three specialization of the published maximal small-range
`psi` estimate.  This proposition is the external analytic boundary. -/
noncomputable def BennettMartinOBryantRechnitzerQ3SmallPrefixBound
    (M : Nat) : Prop :=
  1 ≤ M ∧ M ≤ q3ExplicitSmallPrefixUpperRange ∧
    ∀ x : Nat, 1 ≤ x → x ≤ M →
      ∀ r : ZMod 3, r = 1 ∨ r = 2 →
        ‖fullLambdaQ3ResidueMass x r -
            ((x : Real) / 2 : Complex)‖ ≤
          q3ExplicitSmallPrefixClassConstant * Real.sqrt (M : Real)

/-- Subtracting the two residue classes cancels the identical main term and
doubles the one-class maximal error. -/
theorem dirichletCharacterPartialSum_norm_le_smallPrefixEnvelope
    (M x : Nat)
    (hSource : BennettMartinOBryantRechnitzerQ3SmallPrefixBound M)
    (hx : x ≤ M) :
    ‖fullLambdaQ3DirichletCharacterPartialSum x.succ‖ ≤
      (349 / 100 : Real) * Real.sqrt (M : Real) := by
  by_cases hx0 : x = 0
  · subst x
    simp [fullLambdaQ3DirichletCharacterPartialSum,
      q3QuadraticDirichletCharacter]
  · have hx1 : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx0
    rw [fullLambdaQ3DirichletCharacterPartialSum_succ_eq_residueMass_sub]
    have h1 := hSource.2.2 x hx1 hx (1 : ZMod 3) (Or.inl rfl)
    have h2 := hSource.2.2 x hx1 hx (2 : ZMod 3) (Or.inr rfl)
    have htri :
        ‖fullLambdaQ3ResidueMass x 1 - fullLambdaQ3ResidueMass x 2‖ ≤
          ‖fullLambdaQ3ResidueMass x 1 - ((x : Real) / 2 : Complex)‖ +
            ‖fullLambdaQ3ResidueMass x 2 - ((x : Real) / 2 : Complex)‖ := by
      calc
        ‖fullLambdaQ3ResidueMass x 1 - fullLambdaQ3ResidueMass x 2‖ =
            ‖(fullLambdaQ3ResidueMass x 1 - ((x : Real) / 2 : Complex)) +
              (((x : Real) / 2 : Complex) - fullLambdaQ3ResidueMass x 2)‖ := by
                congr 1
                ring
        _ ≤ ‖fullLambdaQ3ResidueMass x 1 - ((x : Real) / 2 : Complex)‖ +
            ‖((x : Real) / 2 : Complex) - fullLambdaQ3ResidueMass x 2‖ :=
              norm_add_le _ _
        _ = ‖fullLambdaQ3ResidueMass x 1 - ((x : Real) / 2 : Complex)‖ +
            ‖fullLambdaQ3ResidueMass x 2 - ((x : Real) / 2 : Complex)‖ := by
              congr 1
              exact norm_sub_rev _ _
    calc
      ‖fullLambdaQ3ResidueMass x 1 - fullLambdaQ3ResidueMass x 2‖ ≤
          ‖fullLambdaQ3ResidueMass x 1 - ((x : Real) / 2 : Complex)‖ +
            ‖fullLambdaQ3ResidueMass x 2 - ((x : Real) / 2 : Complex)‖ := htri
      _ ≤ 2 * (q3ExplicitSmallPrefixClassConstant *
          Real.sqrt (M : Real)) := by linarith
      _ = (349 / 100 : Real) * Real.sqrt (M : Real) := by
        unfold q3ExplicitSmallPrefixClassConstant
        ring

/-- The source-matched maximal estimate supplies exactly the uniform ceiling
over all prefixes required by the project interface. -/
theorem actualQ3DirichletCharacterPartialSumCeiling_of_smallPrefixSource
    (M : Nat)
    (hSource : BennettMartinOBryantRechnitzerQ3SmallPrefixBound M) :
    ActualQ3DirichletCharacterPartialSumCeiling M
      ((349 / 100 : Real) * Real.sqrt (M : Real)) := by
  constructor
  · positivity
  · intro X hX
    cases X with
    | zero =>
        simp [fullLambdaQ3DirichletCharacterPartialSum]
    | succ x =>
        apply dirichletCharacterPartialSum_norm_le_smallPrefixEnvelope
          M x hSource
        omega

/-- Direct conditional project composition in the published finite source
range.  The signed reserve comparison remains explicit and open. -/
theorem projectReserve_add_negativeAggregate_re_pos_of_smallPrefixSource
    (M : Nat) (hM : 0 < M)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hTarget : 2 * n ∈ evenTargetBlock M)
    (hq : q.val.val = 3)
    (hSource : BennettMartinOBryantRechnitzerQ3SmallPrefixBound M)
    (hAbsorb : actualQ3UnitDifferenceScaleEnvelope M q
        ((349 / 100 : Real) * Real.sqrt (M : Real) +
          Real.log (M : Real)) <
      actualQ3PrefixLocalDensityProjectReserve M q n) :
    0 < (M : Real) / 14 +
      (selectedPairNegativeCenteredUnitAggregate M q n).re := by
  exact projectReserve_add_negativeAggregate_re_pos_of_dirichletCharacterCeiling
    M hM q n hTarget hq
      ((349 / 100 : Real) * Real.sqrt (M : Real))
      (actualQ3DirichletCharacterPartialSumCeiling_of_smallPrefixSource M hSource)
      hAbsorb

end GoldbachCircleMethodActualQ3ExplicitPrefixSqrtEnvelopeV18762
