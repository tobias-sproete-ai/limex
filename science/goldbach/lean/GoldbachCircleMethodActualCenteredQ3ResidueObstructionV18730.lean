import GoldbachCircleMethodActualCenteredRamanujanPrefixAbelV18728
import GoldbachCircleMethodEvenStepDenominatorAliasNegativeWitnessV18677

/-!
# V1.8.730: exact denominator-three residue obstruction after global centering

This append-only module isolates the first nontrivial odd Ramanujan mode.  It
proves, for arbitrary complex coefficients, that the denominator-three
even-step transform is exactly three times one residue-class mass minus the
total mass.  Specializing to the definitionally fixed centered actual
Lambda-pair source removes only the total-mass term.  The full transform is
therefore three times a centered residue-class mass; global mean zero does not
make this nonconstant rational mode vanish.

The result is an exact finite identity.  It proves no nonzero lower bound, no
asymptotic size, no minor-arc estimate, and no Goldbach conclusion.
`proof_status = NO_PROOF`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators Classical

namespace GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730

open GoldbachCircleMethodFiniteResiduePrefixV1866
open GoldbachCircleMethodEvenStepDenominatorAliasNegativeWitnessV18677
open GoldbachCircleMethodGeneralCoprimeCharacterV1868
open GoldbachCircleMethodRamanujanCoprimeBindingV1840
open GoldbachCircleMethodExactLambdaPairSourceMeanSplitV18716
open GoldbachCircleMethodActualCenteredRamanujanPrefixAbelV18728
open GoldbachCircleMethodOddChannelEventualAbsorptionV18658
open GoldbachCircleMethodFullDenominatorFourClassPartitionV18688

/-- Exact equality of natural residue classes modulo three. -/
def sameResidueThree (s n : Nat) : Prop :=
  (s : ZMod 3) = (n : ZMod 3)

/-- The denominator-three Ramanujan coefficient takes the value two at zero
and minus one at both nonzero residue classes. -/
theorem unitCharacterSum_three_eq_if_zero (x : ZMod 3) :
    @unitCharacterSum 3 ⟨by norm_num⟩ x =
      if x = 0 then 2 else -1 := by
  have hx : ((x.val : Nat) : ZMod 3) = x := ZMod.natCast_zmod_val x
  rw [← hx]
  by_cases hdiv : 3 ∣ x.val
  · have hval : x.val = 0 := by
      have hlt : x.val < 3 := ZMod.val_lt x
      omega
    simp [hval, unitCharacterSum_three_zero]
  · have hcop : Nat.Coprime x.val 3 :=
      (Nat.coprime_comm.trans
        (show Nat.Coprime 3 x.val ↔ ¬ 3 ∣ x.val from
          (by norm_num : Nat.Prime 3).coprime_iff_not_dvd)).2 hdiv
    have hne : ((x.val : Nat) : ZMod 3) ≠ 0 := by
      intro hz
      exact hdiv ((ZMod.natCast_eq_zero_iff x.val 3).mp hz)
    have hne_x : x ≠ 0 := by
      rw [← hx]
      exact hne
    rw [← finiteFourierRamanujan_eq_unitCharacterSum 3 x.val (by norm_num),
      finiteFourierRamanujan_eq_neg_one_of_prime (by norm_num) hcop]
    simp [hne_x]

/-- Multiplication by two is invertible modulo three, so the literal
V1.8.728 frequency is zero exactly on the target residue class. -/
theorem two_int_sub_cast_eq_zero_iff_sameResidueThree (s n : Nat) :
    (((2 * ((s : Int) - (n : Int)) : Int) : ZMod 3)) = 0 ↔
      sameResidueThree s n := by
  have hcast :
      (((2 * ((s : Int) - (n : Int)) : Int) : ZMod 3)) =
        (2 : ZMod 3) * ((s : ZMod 3) - (n : ZMod 3)) := by
    push_cast
    ring
  rw [hcast]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with htwo | hsub
    · exact ((by decide : (2 : ZMod 3) ≠ 0) htwo).elim
    · exact sub_eq_zero.mp hsub
  · intro h
    rw [show (s : ZMod 3) = (n : ZMod 3) from h]
    simp

/-- Pointwise denominator-three evaluation in the exact sign convention of
the canonical centered Ramanujan atom. -/
theorem unitCharacterSum_three_two_int_sub
    (s n : Nat) :
    @unitCharacterSum 3 ⟨by norm_num⟩
        (((2 * ((s : Int) - (n : Int)) : Int) : ZMod 3)) =
      if sameResidueThree s n then 2 else -1 := by
  rw [unitCharacterSum_three_eq_if_zero]
  by_cases hz :
      (((2 * ((s : Int) - (n : Int)) : Int) : ZMod 3)) = 0
  · have hres := (two_int_sub_cast_eq_zero_iff_sameResidueThree s n).1 hz
    rw [if_pos hz, if_pos hres]
  · have hres : ¬ sameResidueThree s n := by
      intro hres
      exact hz ((two_int_sub_cast_eq_zero_iff_sameResidueThree s n).2 hres)
    rw [if_neg hz, if_neg hres]

/-- Finite denominator-three transform for arbitrary complex coefficients. -/
noncomputable def q3EvenStepTransform
    (z : Nat → Complex) (n k : Nat) : Complex :=
  ∑ s ∈ Finset.range k,
    z s * @unitCharacterSum 3 ⟨by norm_num⟩
      (((2 * ((s : Int) - (n : Int)) : Int) : ZMod 3))

/-- The coefficient mass in the unique residue class of the target modulo
three.  The `if` representation keeps the identity on the same range. -/
noncomputable def q3ResidueMass
    (z : Nat → Complex) (n k : Nat) : Complex :=
  ∑ s ∈ Finset.range k, if sameResidueThree s n then z s else 0

/-- Generic exact obstruction identity: denominator three retains a residue
imbalance even when the total coefficient mass is zero. -/
theorem q3EvenStepTransform_eq_three_mul_residueMass_sub_total
    (z : Nat → Complex) (n k : Nat) :
    q3EvenStepTransform z n k =
      3 * q3ResidueMass z n k - ∑ s ∈ Finset.range k, z s := by
  unfold q3EvenStepTransform q3ResidueMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [unitCharacterSum_three_two_int_sub]
  by_cases hres : sameResidueThree s n
  · simp [hres]
    ring
  · simp [hres]

/-- The actual centered Lambda-pair mass in the target residue class modulo
three.  This is a deterministic finite arithmetic quantity, not a hypothesis. -/
noncomputable def actualCenteredQ3ResidueMass (M n : Nat) : Complex :=
  q3ResidueMass
    (fun s => (centeredActualLambdaPairSource M s : Complex)) n M.succ

/-- Exact full-range specialization to the actual mean-centered source.  The
global zero-total theorem removes exactly the total term and nothing else. -/
theorem actualCenteredQ3EvenStepTransform_eq_three_mul_residueMass
    (M n : Nat) :
    q3EvenStepTransform
        (fun s => (centeredActualLambdaPairSource M s : Complex)) n M.succ =
      3 * actualCenteredQ3ResidueMass M n := by
  rw [q3EvenStepTransform_eq_three_mul_residueMass_sub_total]
  have hzero :
      (∑ s ∈ Finset.range M.succ,
        (centeredActualLambdaPairSource M s : Complex)) = 0 := by
    exact_mod_cast sum_centeredActualLambdaPairSource_eq_zero M
  rw [hzero, sub_zero]
  rfl

/-- If a selected odd denominator is definitionally the modulus three, the
canonical V1.8.728 full prefix is the direct denominator-three transform. -/
theorem actualCenteredRamanujanPrefix_eq_q3EvenStepTransform
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3) :
    actualCenteredRamanujanPrefix M q n M.succ =
      q3EvenStepTransform
        (fun s => (centeredActualLambdaPairSource M s : Complex)) n M.succ := by
  unfold actualCenteredRamanujanPrefix actualCenteredRamanujanAtom
    q3EvenStepTransform
  rcases q with ⟨⟨qv, hqv⟩, hclass⟩
  dsimp at hq ⊢
  subst qv
  apply Finset.sum_congr rfl
  intro s _hs
  rfl

/-- Exact q=3 obstruction on the canonical actual prefix: global centering
leaves precisely three times the target residue-class imbalance. -/
theorem actualCenteredRamanujanPrefix_q3_eq_three_mul_residueMass
    (M : Nat)
    (q : PairedOddBase (oddProjectRadius M))
    (n : Nat)
    (hq : q.val.val = 3) :
    actualCenteredRamanujanPrefix M q n M.succ =
      3 * actualCenteredQ3ResidueMass M n := by
  rw [actualCenteredRamanujanPrefix_eq_q3EvenStepTransform M q n hq]
  exact actualCenteredQ3EvenStepTransform_eq_three_mul_residueMass M n

end GoldbachCircleMethodActualCenteredQ3ResidueObstructionV18730
