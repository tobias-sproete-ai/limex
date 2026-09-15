import GoldbachCircleMethodLocalizedAdjustedExplicitCorrectionReserveV18297

/-!
# Goldbach V1.8.298: even-conductor coprime-branch obstruction

The V1.8.295--297 localized reserve branch assumes that the Goldbach target
is coprime to the active conductor.  This module records the exact domain
obstruction: an even target and an even active conductor cannot satisfy that
hypothesis.
-/

set_option autoImplicit false

namespace GoldbachCircleMethodEvenConductorCoprimeBranchObstructionV18298

/-- Two even naturals are not coprime, since `2` divides both. -/
theorem even_even_not_coprime {N r : ℕ}
    (hN : Even N) (hr : Even r) :
    ¬ Nat.Coprime N r := by
  rw [Nat.Prime.not_coprime_iff_dvd]
  exact ⟨2, Nat.prime_two, even_iff_two_dvd.mp hN,
    even_iff_two_dvd.mp hr⟩

/-- The coprime hypothesis consumed by the localized reserve is impossible
on the even-target/even-conductor subdomain. -/
theorem no_coprime_localized_reserve_input {N r : ℕ}
    (hN : Even N) (hr : Even r) :
    Nat.Coprime N r → False := by
  exact even_even_not_coprime hN hr

end GoldbachCircleMethodEvenConductorCoprimeBranchObstructionV18298

