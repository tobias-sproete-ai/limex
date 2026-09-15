import GoldbachCircleMethodActualQ3DirichletCharacterBindingV18760

/-!
# V1.8.761: exact q=3 explicit-psi source interface

This append-only module translates the genuine quadratic Dirichlet-character
von-Mangoldt sum from V1.8.760 into the literal difference of the two reduced
residue-class Chebyshev functions modulo three.  It then exposes the exact
finite proposition matched by Bennett--Martin--O'Bryant--Rechnitzer,
Theorem 1.1, using the conservative constants `1 / 840` and `8 * 10^9`.

The cited analytic proposition is not asserted, imported as an axiom, or
inhabited here.  The kernel proves only the exact finite translation and the
conditional `1 / 420` character-sum consequence.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3ExplicitPsiSourceMatchV18761

open GoldbachCircleMethodActualQ3DirichletCharacterBindingV18760
open GoldbachCircleMethodActualQ3UnitDifferenceCharacterAdapterV18757

/-- Finite Chebyshev `psi` mass in one residue class modulo three.  The range
`x.succ` is exactly the natural-number convention `n <= x`. -/
noncomputable def fullLambdaQ3ResidueMass
    (x : Nat) (r : ZMod 3) : Complex :=
  ∑ a ∈ Finset.range x.succ,
    if (a : ZMod 3) = r then
      (ArithmeticFunction.vonMangoldt a : Complex)
    else 0

/-- Pointwise expansion of the q=3 character table into the difference of
the two reduced residue-class indicators. -/
theorem lambda_mul_q3Table_eq_residueIndicators
    (a : Nat) :
    (ArithmeticFunction.vonMangoldt a : Complex) *
        q3UnitDifferenceCharacterTable (a : ZMod 3) =
      ((if (a : ZMod 3) = 1 then
          (ArithmeticFunction.vonMangoldt a : Complex)
        else 0 : Complex)) -
      ((if (a : ZMod 3) = 2 then
          (ArithmeticFunction.vonMangoldt a : Complex)
        else 0 : Complex)) := by
  by_cases h1 : (a : ZMod 3) = 1
  · have h12 : (a : ZMod 3) ≠ 2 := by
      intro h
      exact (by decide : (1 : ZMod 3) ≠ 2) (h1.symm.trans h)
    have hRhs :
        ((if (a : ZMod 3) = 1 then
            (ArithmeticFunction.vonMangoldt a : Complex)
          else 0 : Complex)) -
          ((if (a : ZMod 3) = 2 then
            (ArithmeticFunction.vonMangoldt a : Complex)
          else 0 : Complex)) =
        (ArithmeticFunction.vonMangoldt a : Complex) := by
      rw [if_pos h1, if_neg h12]
      ring
    rw [hRhs]
    unfold q3UnitDifferenceCharacterTable
    rw [if_pos h1]
    simp
  · by_cases h2 : (a : ZMod 3) = 2
    · unfold q3UnitDifferenceCharacterTable
      rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
      simp
    · unfold q3UnitDifferenceCharacterTable
      rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
      simp

/-- Exact source identity: the genuine character partial sum through `x`
is the difference `psi(x;3,1) - psi(x;3,2)`. -/
theorem fullLambdaQ3DirichletCharacterPartialSum_succ_eq_residueMass_sub
    (x : Nat) :
    fullLambdaQ3DirichletCharacterPartialSum x.succ =
      fullLambdaQ3ResidueMass x 1 -
        fullLambdaQ3ResidueMass x 2 := by
  unfold fullLambdaQ3DirichletCharacterPartialSum fullLambdaQ3ResidueMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [q3QuadraticDirichletCharacter_eq_table]
  simpa using lambda_mul_q3Table_eq_residueIndicators a

/-- The exact one-point source proposition supplied by an explicit
prime-number theorem in arithmetic progressions.  It is deliberately a
proposition, not an axiom or a structure instance. -/
def ExplicitPsiQ3ResidueBoundAt
    (x : Nat) (C : Real) : Prop :=
  ∀ r : ZMod 3, r = 1 ∨ r = 2 →
    ‖fullLambdaQ3ResidueMass x r - ((x : Real) / 2 : Complex)‖ <
      C * (x : Real) / Real.log (x : Real)

/-- Conservative constants appearing directly in Theorem 1.1 of
Bennett--Martin--O'Bryant--Rechnitzer for every `3 <= q <= 10^4`. -/
noncomputable def q3ExplicitPsiSourceConstant : Real := 1 / 840

def q3ExplicitPsiSourceThreshold : Nat := 8000000000

/-- Exact source-matched proposition for the modulus-three specialization.
No inhabitant is supplied by this module. -/
def BennettMartinOBryantRechnitzerQ3MatchAt (x : Nat) : Prop :=
  q3ExplicitPsiSourceThreshold ≤ x ∧
    ExplicitPsiQ3ResidueBoundAt x q3ExplicitPsiSourceConstant

/-- Algebraic cancellation transfer: equal main terms cancel, so two
residue-class error bounds of size `C*x/log x` give a character bound with
constant `2*C`. -/
theorem dirichletCharacterPartialSum_norm_lt_two_mul_of_residueBounds
    (x : Nat) (C : Real)
    (hC : ExplicitPsiQ3ResidueBoundAt x C) :
    ‖fullLambdaQ3DirichletCharacterPartialSum x.succ‖ <
      2 * (C * (x : Real) / Real.log (x : Real)) := by
  rw [fullLambdaQ3DirichletCharacterPartialSum_succ_eq_residueMass_sub]
  have h1 := hC (1 : ZMod 3) (Or.inl rfl)
  have h2 := hC (2 : ZMod 3) (Or.inr rfl)
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
  exact lt_of_le_of_lt htri (by linarith)

/-- The conservative source constants compose exactly to `1 / 420` for the
q=3 character sum.  This remains conditional on the explicit source-matched
proposition. -/
theorem dirichletCharacterPartialSum_norm_lt_sourceEnvelope
    (x : Nat)
    (hSource : BennettMartinOBryantRechnitzerQ3MatchAt x) :
    ‖fullLambdaQ3DirichletCharacterPartialSum x.succ‖ <
      (x : Real) / (420 * Real.log (x : Real)) := by
  have h := dirichletCharacterPartialSum_norm_lt_two_mul_of_residueBounds
    x q3ExplicitPsiSourceConstant hSource.2
  unfold q3ExplicitPsiSourceConstant at h
  have heq :
      2 * ((1 / 840 : Real) * (x : Real) / Real.log (x : Real)) =
        (x : Real) / (420 * Real.log (x : Real)) := by
    ring
  rw [← heq]
  exact h

end GoldbachCircleMethodActualQ3ExplicitPsiSourceMatchV18761
