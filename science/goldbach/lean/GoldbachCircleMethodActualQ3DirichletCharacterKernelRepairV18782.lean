import GoldbachCircleMethodActualQ3UnitCharacterSourceCompatibilityV18781
import GoldbachCircleMethodActualQ3DirichletCharacterBindingV18760

/-!
# V1.8.782: kernel-only repair of the q=3 Dirichlet-character table

V1.8.760 evaluated the fixed Legendre-symbol entry through a tactic path whose
readback contains a theorem-local `native_decide` axiom.  This append-only
successor repeats the finite table proof with kernel reduction (`decide`) and
rebinds the partial-sum identity without depending on that predecessor theorem.

No analytic estimate and no Goldbach conclusion is introduced.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical ArithmeticFunction.vonMangoldt

namespace GoldbachCircleMethodActualQ3DirichletCharacterKernelRepairV18782

open GoldbachCircleMethodActualQ3UnitDifferenceCharacterAdapterV18757
open GoldbachCircleMethodActualQ3FullCharacterPartialSumNormalizationV18759
open GoldbachCircleMethodActualQ3DirichletCharacterBindingV18760
open GoldbachCircleMethodActualQ3UnitCharacterSourceBindingV18780
open GoldbachCircleMethodActualQ3UnitCharacterSourceCompatibilityV18781

/-- Kernel-reduced replacement for the V1.8.760 pointwise table theorem. -/
theorem q3QuadraticDirichletCharacter_eq_table_kernel
    (r : ZMod 3) :
    q3QuadraticDirichletCharacter r =
      q3UnitDifferenceCharacterTable r := by
  by_cases h1 : r = 1
  · subst r
    change (((quadraticChar (ZMod 3)) (1 : ZMod 3) : Int) : Complex) = _
    rw [map_one]
    unfold q3UnitDifferenceCharacterTable
    rw [if_pos rfl]
    norm_num
  · by_cases h2 : r = 2
    · subst r
      change (((quadraticChar (ZMod 3)) (2 : ZMod 3) : Int) : Complex) = _
      have hquad : quadraticChar (ZMod 3) (2 : ZMod 3) = -1 := by
        change legendreSym 3 2 = -1
        decide
      have h21 : (2 : ZMod 3) ≠ 1 := by decide
      rw [hquad]
      unfold q3UnitDifferenceCharacterTable
      rw [if_neg h21, if_pos rfl]
      norm_num
    · have h0 : r = 0 := by
        have hv1 : r.val ≠ 1 := by
          intro hv
          apply h1
          apply ZMod.val_injective 3
          rw [ZMod.val_one 3]
          exact hv
        have hv2 : r.val ≠ 2 := by
          intro hv
          apply h2
          apply ZMod.val_injective 3
          rw [ZMod.val_two_eq_two_mod 3]
          norm_num
          exact hv
        have hvlt : r.val < 3 := ZMod.val_lt r
        have hv0 : r.val = 0 := by omega
        apply ZMod.val_injective 3
        simpa using hv0
      subst r
      change (((quadraticChar (ZMod 3)) (0 : ZMod 3) : Int) : Complex) = _
      have h01 : (0 : ZMod 3) ≠ 1 := by decide
      have h02 : (0 : ZMod 3) ≠ 2 := by decide
      rw [quadraticChar_zero]
      unfold q3UnitDifferenceCharacterTable
      rw [if_neg h01, if_neg h02]
      norm_num

/-- Clean partial-sum bridge using only the kernel-reduced table theorem. -/
theorem fullLambdaQ3DirichletCharacterPartialSum_eq_actual_kernel
    (X : Nat) :
    fullLambdaQ3DirichletCharacterPartialSum X =
      fullLambdaQ3CharacterPartialSum X := by
  apply Finset.sum_congr rfl
  intro a _ha
  rw [q3QuadraticDirichletCharacter_eq_table_kernel]

/-- Clean direct bridge from the V1.8.780 real sign to the genuine character. -/
theorem q3UnitCharacterSign_cast_eq_dirichletCharacter_kernel (a : Nat) :
    ((q3UnitCharacterSign a : Real) : Complex) =
      q3QuadraticDirichletCharacter (a : ZMod 3) := by
  rw [q3QuadraticDirichletCharacter_eq_table_kernel]
  exact q3UnitCharacterSign_cast_eq_characterTable a

end GoldbachCircleMethodActualQ3DirichletCharacterKernelRepairV18782
